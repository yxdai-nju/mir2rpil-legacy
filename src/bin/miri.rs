#![feature(rustc_private, stmt_expr_attributes)]
#![allow(
    clippy::manual_range_contains,
    clippy::useless_format,
    clippy::field_reassign_with_default,
    rustc::diagnostic_outside_of_impl,
    rustc::untranslatable_diagnostic
)]

// Some "regular" crates we want to share with rustc
extern crate tracing;

// The rustc crates we need
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_log;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_target;

use core::fmt;
use std::env::{self, VarError};
use std::mem::discriminant;
use std::num::NonZero;
use std::path::PathBuf;
use std::str::FromStr;

use rustc_target::abi::{FieldIdx, VariantIdx};
use tracing::debug;

use rustc_data_structures::sync::Lrc;
use rustc_driver::Compilation;
use rustc_hir::{self as hir, Node};
use rustc_interface::interface::Config;
use rustc_middle::{
    middle::{
        codegen_fn_attrs::CodegenFnAttrFlags,
        exported_symbols::{ExportedSymbol, SymbolExportInfo, SymbolExportKind, SymbolExportLevel},
    },
    mir,
    query::LocalCrate,
    ty,
    ty::TyCtxt,
    util::Providers,
};
use rustc_session::config::{CrateType, ErrorOutputType, OptLevel};
use rustc_session::search_paths::PathKind;
use rustc_session::{CtfeBacktrace, EarlyDiagCtxt};

use miri::{BacktraceStyle, BorrowTrackerMethod, ProvenanceMode, RetagFields};

struct MiriCompilerCalls {
    miri_config: miri::MiriConfig,
}

enum RpilOp {
    Var(usize),
    Place(Box<RpilOp>, String),
    ExternPlace(Box<RpilOp>),
    Deref(Box<RpilOp>),
}

impl fmt::Debug for RpilOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RpilOp::*;
        match self {
            Var(var) => write!(f, "${:?}", var),
            Place(op, place) => write!(f, "{:?}.{}", op, place),
            ExternPlace(op) => write!(f, "{:?}.extern", op),
            Deref(op) => write!(f, "({:?})*", op),
        }
    }
}

enum RpilInst {
    Bind(RpilOp, RpilOp),
    Borrow(RpilOp, RpilOp),
    BorrowMut(RpilOp, RpilOp),
    Move(RpilOp),
    DerefMove(RpilOp),
    DerefPin(RpilOp),
}

impl fmt::Debug for RpilInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RpilInst::*;
        match self {
            Bind(op1, op2) => write!(f, "BIND {:?}, {:?}", op1, op2),
            Borrow(op1, op2) => write!(f, "BORROW {:?}, {:?}", op1, op2),
            BorrowMut(op1, op2) => write!(f, "BORROW-MUT {:?}, {:?}", op1, op2),
            Move(op) => write!(f, "MOVE {:?}", op),
            DerefMove(op) => write!(f, "DEREF-MOVE {:?}", op),
            DerefPin(op) => write!(f, "DEREF-PIN {:?}", op),
        }
    }
}

fn def_id_of_func_operand<'tcx>(func: &'tcx mir::Operand<'tcx>) -> hir::def_id::DefId {
    match func {
        mir::Operand::Constant(operand) =>
            match operand.const_ {
                mir::Const::Val(_, fn_def) =>
                    match fn_def.kind() {
                        ty::FnDef(def_id, _) => *def_id,
                        _ => unimplemented!(),
                    },
                mir::Const::Unevaluated(_, _) | mir::Const::Ty(_, _) => unimplemented!(),
            },
        mir::Operand::Copy(_) | mir::Operand::Move(_) => unimplemented!(),
    }
}

fn place_project<'tcx>(place: &'tcx mir::Place<'tcx>, idx: usize) -> RpilOp {
    if idx == place.projection.len() {
        return RpilOp::Var(place.local.as_usize());
    }
    let rplace = &place.projection[idx];
    match rplace {
        mir::ProjectionElem::Field(ridx, _) =>
            RpilOp::Place(Box::new(place_project(place, idx + 1)), format!("p{}", ridx.as_usize())),
        mir::ProjectionElem::Deref => RpilOp::Deref(Box::new(place_project(place, idx + 1))),
        mir::ProjectionElem::Downcast(_, variant_idx) => {
            let next_projection = place_project(place, idx + 1);
            match next_projection {
                RpilOp::Place(op, place_string) =>
                    RpilOp::Place(op, format!("v{}{}", variant_idx.as_usize(), place_string)),
                _ => unreachable!(),
            }
        }
        _ => {
            let x = discriminant(rplace);
            println!("[ProjectionElem-{:?}] Unknown `{:?}`", x, rplace);
            unimplemented!()
        }
    }
}

fn rpil_place<'tcx>(place: &'tcx mir::Place<'tcx>) -> RpilOp {
    let projection = place_project(place, 0);
    if place.projection.len() > 0 {
        println!("[ProjectionElems] {:#?}", place.projection);
        println!("[Projection] {:?}", projection);
    }
    projection
}

#[allow(clippy::needless_lifetimes)]
fn rpil_of_func<'tcx>(tcx: TyCtxt<'tcx>, func_id: hir::def_id::DefId) -> Vec<RpilInst> {
    let mut rpil_insts = vec![];
    let mut emit_rpil = |inst: RpilInst| {
        rpil_insts.push(inst);
    };
    let fn_name = tcx.def_path_str(func_id);
    println!("[MIR] Body for function: {}", fn_name);
    if !tcx.is_mir_available(func_id) {
        println!("MIR not available for `{:?}`", func_id);
        return vec![];
    }
    let body = tcx.optimized_mir(func_id);
    for (bb, block_data) in body.basic_blocks.iter_enumerated() {
        println!("Basic Block {:?}:", bb);
        // BB statements
        for statement in &block_data.statements {
            let statement = &statement.kind;
            match statement {
                mir::StatementKind::Assign(p) => {
                    println!("Statement: {:?}", statement);
                    let (ref place, ref rvalue) = **p;
                    match rvalue {
                        mir::Rvalue::Use(operand) | mir::Rvalue::Cast(_, operand, _) => {
                            if let mir::Rvalue::Use(_) = rvalue {
                                println!("[Rvalue] Use({:?})", operand);
                            } else {
                                println!("[Rvalue] Cast({:?})", operand);
                            }
                            match operand {
                                mir::Operand::Copy(rplace) => {
                                    emit_rpil(RpilInst::Bind(
                                        RpilOp::Var(place.local.as_usize()),
                                        rpil_place(rplace),
                                    ));
                                }
                                mir::Operand::Move(rplace) => {
                                    emit_rpil(RpilInst::Move(rpil_place(rplace)));
                                    emit_rpil(RpilInst::Bind(
                                        RpilOp::Var(place.local.as_usize()),
                                        rpil_place(rplace),
                                    ));
                                }
                                mir::Operand::Constant(_) => {}
                            }
                        }
                        mir::Rvalue::Aggregate(agg_kind, values) => {
                            println!("[Rvalue] Aggregate({:?}, {:?})", agg_kind, values);
                            let agg_kind = &**agg_kind;
                            match agg_kind {
                                mir::AggregateKind::Array(..) => {
                                    println!("[AggregateKind] Array({:?})", values);
                                    for (lidx, value) in values.iter().enumerate() {
                                        match value {
                                            mir::Operand::Copy(rplace) => {
                                                emit_rpil(RpilInst::Bind(
                                                    RpilOp::Place(
                                                        Box::new(RpilOp::Var(
                                                            place.local.as_usize(),
                                                        )),
                                                        format!("p{}", lidx),
                                                    ),
                                                    rpil_place(rplace),
                                                ));
                                            }
                                            mir::Operand::Move(rplace) => {
                                                emit_rpil(RpilInst::Move(rpil_place(rplace)));
                                                emit_rpil(RpilInst::Bind(
                                                    RpilOp::Place(
                                                        Box::new(RpilOp::Var(
                                                            place.local.as_usize(),
                                                        )),
                                                        format!("p{}", lidx),
                                                    ),
                                                    rpil_place(rplace),
                                                ));
                                            }
                                            mir::Operand::Constant(_) => {}
                                        }
                                    }
                                }
                                mir::AggregateKind::Adt(_, variant_idx, _, _, _) =>
                                    if *variant_idx == VariantIdx::from_usize(0) {
                                        for (lidx, value) in values.iter().enumerate() {
                                            match value {
                                                mir::Operand::Copy(rplace) => {
                                                    emit_rpil(RpilInst::Bind(
                                                        RpilOp::Place(
                                                            Box::new(RpilOp::Var(
                                                                place.local.as_usize(),
                                                            )),
                                                            format!("p{}", lidx),
                                                        ),
                                                        rpil_place(rplace),
                                                    ));
                                                }
                                                mir::Operand::Move(rplace) => {
                                                    emit_rpil(RpilInst::Move(rpil_place(rplace)));
                                                    emit_rpil(RpilInst::Bind(
                                                        RpilOp::Place(
                                                            Box::new(RpilOp::Var(
                                                                place.local.as_usize(),
                                                            )),
                                                            format!("p{}", lidx),
                                                        ),
                                                        rpil_place(rplace),
                                                    ));
                                                }
                                                mir::Operand::Constant(_) => {}
                                            }
                                        }
                                    } else {
                                        let value = values.get(FieldIdx::from_usize(0)).unwrap();
                                        match value {
                                            mir::Operand::Copy(rplace) => {
                                                emit_rpil(RpilInst::Bind(
                                                    RpilOp::Place(
                                                        Box::new(RpilOp::Var(
                                                            place.local.as_usize(),
                                                        )),
                                                        format!("p{}", variant_idx.as_usize()),
                                                    ),
                                                    rpil_place(rplace),
                                                ));
                                            }
                                            mir::Operand::Move(rplace) => {
                                                emit_rpil(RpilInst::Move(rpil_place(rplace)));
                                                emit_rpil(RpilInst::Bind(
                                                    RpilOp::Place(
                                                        Box::new(RpilOp::Var(
                                                            place.local.as_usize(),
                                                        )),
                                                        format!("p{}", variant_idx.as_usize()),
                                                    ),
                                                    rpil_place(rplace),
                                                ));
                                            }
                                            mir::Operand::Constant(_) => {}
                                        }
                                    },
                                _ => {
                                    let x = discriminant(agg_kind);
                                    println!("[AggregateKind-{:?}] Unknown `{:?}`", x, agg_kind);
                                    unimplemented!();
                                }
                            };
                        }
                        mir::Rvalue::Ref(_, _, rplace) => {
                            println!("[Rvalue] Ref({:?})", rplace);
                            emit_rpil(RpilInst::Borrow(
                                RpilOp::Var(place.local.as_usize()),
                                rpil_place(rplace),
                            ));
                        }
                        mir::Rvalue::Discriminant(..) => {}
                        _ => {
                            let x = discriminant(rvalue);
                            println!("[Rvalue-{:?}] Unknown `{:?}`", x, rvalue);
                            unimplemented!();
                        }
                    }
                }
                mir::StatementKind::StorageDead(..)
                | mir::StatementKind::StorageLive(..)
                | mir::StatementKind::Retag(..)
                | mir::StatementKind::PlaceMention(..) => {}
                _ => {
                    let x = discriminant(statement);
                    println!("Statement-{:?}: Unknown `{:?}`", x, statement);
                    unimplemented!();
                }
            }
        }
        // BB terminator
        if let Some(terminator) = &block_data.terminator {
            let terminator = &terminator.kind;
            match terminator {
                mir::TerminatorKind::Call { ref func, ref args, destination, target, .. } => {
                    println!("Terminator: Assign(({:?}, {:?}{:?}))", destination, func, args);
                    let called_func_id = def_id_of_func_operand(func);
                    let rpil_insts = rpil_of_func(tcx, called_func_id);
                    println!(
                        "[RPIL] FunCall RPIL:{}",
                        if rpil_insts.is_empty() { " (empty)" } else { "" }
                    );
                    for inst in rpil_insts {
                        println!("    {:?}", inst);
                    }
                    // let args: Vec<_> = args.iter().map(|s| s.node.clone()).collect();
                    println!("Next: {:?}", target);
                }
                mir::TerminatorKind::Drop { place, target, .. } => {
                    println!("Terminator: Drop({:?})", place);
                    println!("Next: {:?}", target);
                }
                mir::TerminatorKind::Assert { cond, msg, target, .. } => {
                    println!("Terminator: Assert({:?}, {:?})", cond, msg);
                    println!("Next: {:?}", target);
                }
                mir::TerminatorKind::Return => {
                    println!("Next: return");
                }
                mir::TerminatorKind::UnwindResume | mir::TerminatorKind::Unreachable => {
                    println!("Next: !");
                }
                mir::TerminatorKind::SwitchInt { discr, ref targets, .. } => {
                    println!("Terminator: SwitchInt({:?})", discr);
                    println!("Next: {:?}", targets.all_targets());
                }
                _ => {
                    let x = discriminant(terminator);
                    println!("Terminator-{:?}: Unknown `{:?}`", x, terminator);
                    unimplemented!();
                }
            };
        }
        println!();
    }
    rpil_insts
}

impl rustc_driver::Callbacks for MiriCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, providers| {
            providers.extern_queries.used_crate_source = |tcx, cnum| {
                let mut providers = Providers::default();
                rustc_metadata::provide(&mut providers);
                let mut crate_source = (providers.extern_queries.used_crate_source)(tcx, cnum);
                // HACK: rustc will emit "crate ... required to be available in rlib format, but
                // was not found in this form" errors once we use `tcx.dependency_formats()` if
                // there's no rlib provided, so setting a dummy path here to workaround those errors.
                Lrc::make_mut(&mut crate_source).rlib = Some((PathBuf::new(), PathKind::All));
                crate_source
            };
        });
    }

    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            let mut pub_fns = vec![];
            let items = tcx.hir_crate_items(());
            let free_items_owner_id = items.free_items().map(|id| id.owner_id);
            let impl_items_owner_id = items.impl_items().map(|id| id.owner_id);
            let func_ids = free_items_owner_id.chain(impl_items_owner_id).map(|id| id.to_def_id());
            for func_id in func_ids {
                if let hir::def::DefKind::Fn | hir::def::DefKind::AssocFn = tcx.def_kind(func_id) {
                    if tcx.visibility(func_id).is_public() {
                        pub_fns.push(func_id);
                    }
                }
            }
            println!("Public functions: {:?}\n", pub_fns);
            for pub_fn in pub_fns {
                let rpil = rpil_of_func(tcx, pub_fn);
                println!("[RPIL] Result: {:#?}", rpil);
            }
        });

        // queries.global_ctxt().unwrap().enter(|tcx| {
        //     if tcx.sess.dcx().has_errors_or_delayed_bugs().is_some() {
        //         tcx.dcx().fatal("miri cannot be run on programs that fail compilation");
        //     }

        //     let early_dcx = EarlyDiagCtxt::new(tcx.sess.opts.error_format);
        //     init_late_loggers(&early_dcx, tcx);
        //     // if !tcx.crate_types().contains(&CrateType::Executable) {
        //     //     tcx.dcx().fatal("miri only makes sense on bin crates");
        //     // }

        //     // let (entry_def_id, entry_type) = if let Some(entry_def) = tcx.entry_fn(()) {
        //     //     entry_def
        //     // } else {
        //     //     tcx.dcx().fatal("miri can only run programs that have a main function");
        //     // };
        //     let mut funcs_owner_id = tcx.hir_crate_items(()).free_items().map(|x| x.owner_id);
        //     let mut pubfns = vec![];
        //     for owner_id in funcs_owner_id {
        //                 if let hir::def::DefKind::Fn | hir::def::DefKind::AssocFn = tcx.def_kind(owner_id) {
        //                     if tcx.visibility(owner_id).is_public() {
        //                         pubfns.push(owner_id);
        //                     }
        //                 }
        //             }
        //     let pubfn_def_id = pubfns.first().unwrap().to_def_id();
        //     let body = tcx.optimized_mir(pubfn_def_id);
        //     println!("[MIR] {:#?}", body);
        //     let mut config = self.miri_config.clone();

        //     // Add filename to `miri` arguments.
        //     config.args.insert(0, tcx.sess.io.input.filestem().to_string());

        //     // Adjust working directory for interpretation.
        //     if let Some(cwd) = env::var_os("MIRI_CWD") {
        //         env::set_current_dir(cwd).unwrap();
        //     }

        //     if tcx.sess.opts.optimize != OptLevel::No {
        //         tcx.dcx().warn("Miri does not support optimizations: the opt-level is ignored. The only effect \
        //             of selecting a Cargo profile that enables optimizations (such as --release) is to apply \
        //             its remaining settings, such as whether debug assertions and overflow checks are enabled.");
        //     }
        //     if tcx.sess.mir_opt_level() > 0 {
        //         tcx.dcx().warn("You have explicitly enabled MIR optimizations, overriding Miri's default \
        //             which is to completely disable them. Any optimizations may hide UB that Miri would \
        //             otherwise detect, and it is not necessarily possible to predict what kind of UB will \
        //             be missed. If you are enabling optimizations to make Miri run faster, we advise using \
        //             cfg(miri) to shrink your workload instead. The performance benefit of enabling MIR \
        //             optimizations is usually marginal at best.");
        //     }

        //     // if let Some(return_code) = miri::eval_entry(tcx, entry_def_id, entry_type, config) {
        //     //     std::process::exit(
        //     //         i32::try_from(return_code).expect("Return value was too large!"),
        //     //     );
        //     // }
        //     println!("[RPIL] Evaluating `{:?}`", pubfn_def_id);
        //     let rpil = miri::eval_pubfn(tcx, pubfn_def_id, config);
        //     println!("[RPIL] Result: {:?}", rpil);

        //     tcx.dcx().abort_if_errors();
        // });

        Compilation::Stop
    }
}

struct MiriBeRustCompilerCalls {
    target_crate: bool,
}

impl rustc_driver::Callbacks for MiriBeRustCompilerCalls {
    #[allow(rustc::potential_query_instability)] // rustc_codegen_ssa (where this code is copied from) also allows this lint
    fn config(&mut self, config: &mut Config) {
        if config.opts.prints.is_empty() && self.target_crate {
            // Queries overridden here affect the data stored in `rmeta` files of dependencies,
            // which will be used later in non-`MIRI_BE_RUSTC` mode.
            config.override_queries = Some(|_, local_providers| {
                // `exported_symbols` and `reachable_non_generics` provided by rustc always returns
                // an empty result if `tcx.sess.opts.output_types.should_codegen()` is false.
                // In addition we need to add #[used] symbols to exported_symbols for `lookup_link_section`.
                local_providers.exported_symbols = |tcx, LocalCrate| {
                    let reachable_set = tcx.with_stable_hashing_context(|hcx| {
                        tcx.reachable_set(()).to_sorted(&hcx, true)
                    });
                    tcx.arena.alloc_from_iter(
                        // This is based on:
                        // https://github.com/rust-lang/rust/blob/2962e7c0089d5c136f4e9600b7abccfbbde4973d/compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L62-L63
                        // https://github.com/rust-lang/rust/blob/2962e7c0089d5c136f4e9600b7abccfbbde4973d/compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L174
                        reachable_set.into_iter().filter_map(|&local_def_id| {
                            // Do the same filtering that rustc does:
                            // https://github.com/rust-lang/rust/blob/2962e7c0089d5c136f4e9600b7abccfbbde4973d/compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L84-L102
                            // Otherwise it may cause unexpected behaviours and ICEs
                            // (https://github.com/rust-lang/rust/issues/86261).
                            let is_reachable_non_generic = matches!(
                                tcx.hir_node_by_def_id(local_def_id),
                                Node::Item(&hir::Item {
                                    kind: hir::ItemKind::Static(..) | hir::ItemKind::Fn(..),
                                    ..
                                }) | Node::ImplItem(&hir::ImplItem {
                                    kind: hir::ImplItemKind::Fn(..),
                                    ..
                                })
                                if !tcx.generics_of(local_def_id).requires_monomorphization(tcx)
                            );
                            if !is_reachable_non_generic {
                                return None;
                            }
                            let codegen_fn_attrs = tcx.codegen_fn_attrs(local_def_id);
                            if codegen_fn_attrs.contains_extern_indicator()
                                || codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::USED)
                                || codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::USED_LINKER)
                            {
                                Some((
                                    ExportedSymbol::NonGeneric(local_def_id.to_def_id()),
                                    // Some dummy `SymbolExportInfo` here. We only use
                                    // `exported_symbols` in shims/foreign_items.rs and the export info
                                    // is ignored.
                                    SymbolExportInfo {
                                        level: SymbolExportLevel::C,
                                        kind: SymbolExportKind::Text,
                                        used: false,
                                    },
                                ))
                            } else {
                                None
                            }
                        }),
                    )
                }
            });
        }
    }

    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            if self.target_crate {
                // cargo-miri has patched the compiler flags to make these into check-only builds,
                // but we are still emulating regular rustc builds, which would perform post-mono
                // const-eval during collection. So let's also do that here, even if we might be
                // running with `--emit=metadata`. In particular this is needed to make
                // `compile_fail` doc tests trigger post-mono errors.
                // In general `collect_and_partition_mono_items` is not safe to call in check-only
                // builds, but we are setting `-Zalways-encode-mir` which avoids those issues.
                let _ = tcx.collect_and_partition_mono_items(());
            }
        });
        Compilation::Continue
    }
}

fn show_error(msg: &impl std::fmt::Display) -> ! {
    eprintln!("fatal error: {msg}");
    std::process::exit(1)
}

macro_rules! show_error {
    ($($tt:tt)*) => { show_error(&format_args!($($tt)*)) };
}

fn rustc_logger_config() -> rustc_log::LoggerConfig {
    // Start with the usual env vars.
    let mut cfg = rustc_log::LoggerConfig::from_env("RUSTC_LOG");

    // Overwrite if MIRI_LOG is set.
    if let Ok(var) = env::var("MIRI_LOG") {
        // MIRI_LOG serves as default for RUSTC_LOG, if that is not set.
        if matches!(cfg.filter, Err(VarError::NotPresent)) {
            // We try to be a bit clever here: if `MIRI_LOG` is just a single level
            // used for everything, we only apply it to the parts of rustc that are
            // CTFE-related. Otherwise, we use it verbatim for `RUSTC_LOG`.
            // This way, if you set `MIRI_LOG=trace`, you get only the right parts of
            // rustc traced, but you can also do `MIRI_LOG=miri=trace,rustc_const_eval::interpret=debug`.
            if tracing::Level::from_str(&var).is_ok() {
                cfg.filter = Ok(format!(
                    "rustc_middle::mir::interpret={var},rustc_const_eval::interpret={var},miri={var}"
                ));
            } else {
                cfg.filter = Ok(var);
            }
        }
    }

    cfg
}

fn init_early_loggers(early_dcx: &EarlyDiagCtxt) {
    // Now for rustc. We only initialize `rustc` if the env var is set (so the user asked for it).
    // If it is not set, we avoid initializing now so that we can initialize later with our custom
    // settings, and *not* log anything for what happens before `miri` gets started.
    if env::var_os("RUSTC_LOG").is_some() {
        rustc_driver::init_logger(early_dcx, rustc_logger_config());
    }
}

fn init_late_loggers(early_dcx: &EarlyDiagCtxt, tcx: TyCtxt<'_>) {
    // If `RUSTC_LOG` is not set, then `init_early_loggers` did not call
    // `rustc_driver::init_logger`, so we have to do this now.
    if env::var_os("RUSTC_LOG").is_none() {
        rustc_driver::init_logger(early_dcx, rustc_logger_config());
    }

    // If `MIRI_BACKTRACE` is set and `RUSTC_CTFE_BACKTRACE` is not, set `RUSTC_CTFE_BACKTRACE`.
    // Do this late, so we ideally only apply this to Miri's errors.
    if let Some(val) = env::var_os("MIRI_BACKTRACE") {
        let ctfe_backtrace = match &*val.to_string_lossy() {
            "immediate" => CtfeBacktrace::Immediate,
            "0" => CtfeBacktrace::Disabled,
            _ => CtfeBacktrace::Capture,
        };
        *tcx.sess.ctfe_backtrace.borrow_mut() = ctfe_backtrace;
    }
}

/// Execute a compiler with the given CLI arguments and callbacks.
fn run_compiler(
    mut args: Vec<String>,
    target_crate: bool,
    callbacks: &mut (dyn rustc_driver::Callbacks + Send),
    using_internal_features: std::sync::Arc<std::sync::atomic::AtomicBool>,
) -> ! {
    // Don't insert `MIRI_DEFAULT_ARGS`, in particular, `--cfg=miri`, if we are building
    // a "host" crate. That may cause procedural macros (and probably build scripts) to
    // depend on Miri-only symbols, such as `miri_resolve_frame`:
    // https://github.com/rust-lang/miri/issues/1760
    if target_crate {
        // Some options have different defaults in Miri than in plain rustc; apply those by making
        // them the first arguments after the binary name (but later arguments can overwrite them).
        args.splice(1..1, miri::MIRI_DEFAULT_ARGS.iter().map(ToString::to_string));
    }

    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&args, callbacks)
            .set_using_internal_features(using_internal_features)
            .run()
    });
    std::process::exit(exit_code)
}

/// Parses a comma separated list of `T` from the given string:
/// `<value1>,<value2>,<value3>,...`
fn parse_comma_list<T: FromStr>(input: &str) -> Result<Vec<T>, T::Err> {
    input.split(',').map(str::parse::<T>).collect()
}

/// Parses the input as a float in the range from 0.0 to 1.0 (inclusive).
fn parse_rate(input: &str) -> Result<f64, &'static str> {
    match input.parse::<f64>() {
        Ok(rate) if rate >= 0.0 && rate <= 1.0 => Ok(rate),
        Ok(_) => Err("must be between `0.0` and `1.0`"),
        Err(_) => Err("requires a `f64` between `0.0` and `1.0`"),
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn jemalloc_magic() {
    // These magic runes are copied from
    // <https://github.com/rust-lang/rust/blob/e89bd9428f621545c979c0ec686addc6563a394e/compiler/rustc/src/main.rs#L39>.
    // See there for further comments.
    use std::os::raw::{c_int, c_void};

    #[used]
    static _F1: unsafe extern "C" fn(usize, usize) -> *mut c_void = jemalloc_sys::calloc;
    #[used]
    static _F2: unsafe extern "C" fn(*mut *mut c_void, usize, usize) -> c_int =
        jemalloc_sys::posix_memalign;
    #[used]
    static _F3: unsafe extern "C" fn(usize, usize) -> *mut c_void = jemalloc_sys::aligned_alloc;
    #[used]
    static _F4: unsafe extern "C" fn(usize) -> *mut c_void = jemalloc_sys::malloc;
    #[used]
    static _F5: unsafe extern "C" fn(*mut c_void, usize) -> *mut c_void = jemalloc_sys::realloc;
    #[used]
    static _F6: unsafe extern "C" fn(*mut c_void) = jemalloc_sys::free;

    // On OSX, jemalloc doesn't directly override malloc/free, but instead
    // registers itself with the allocator's zone APIs in a ctor. However,
    // the linker doesn't seem to consider ctors as "used" when statically
    // linking, so we need to explicitly depend on the function.
    #[cfg(target_os = "macos")]
    {
        extern "C" {
            fn _rjem_je_zone_register();
        }

        #[used]
        static _F7: unsafe extern "C" fn() = _rjem_je_zone_register;
    }
}

fn main() {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    jemalloc_magic();

    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());

    // Snapshot a copy of the environment before `rustc` starts messing with it.
    // (`install_ice_hook` might change `RUST_BACKTRACE`.)
    let env_snapshot = env::vars_os().collect::<Vec<_>>();

    let args = rustc_driver::args::raw_args(&early_dcx)
        .unwrap_or_else(|_| std::process::exit(rustc_driver::EXIT_FAILURE));

    // Install the ctrlc handler that sets `rustc_const_eval::CTRL_C_RECEIVED`, even if
    // MIRI_BE_RUSTC is set.
    rustc_driver::install_ctrlc_handler();

    // If the environment asks us to actually be rustc, then do that.
    if let Some(crate_kind) = env::var_os("MIRI_BE_RUSTC") {
        // Earliest rustc setup.
        let using_internal_features =
            rustc_driver::install_ice_hook(rustc_driver::DEFAULT_BUG_REPORT_URL, |_| ());
        rustc_driver::init_rustc_env_logger(&early_dcx);

        let target_crate = if crate_kind == "target" {
            true
        } else if crate_kind == "host" {
            false
        } else {
            panic!("invalid `MIRI_BE_RUSTC` value: {crate_kind:?}")
        };

        // We cannot use `rustc_driver::main` as we need to adjust the CLI arguments.
        run_compiler(
            args,
            target_crate,
            &mut MiriBeRustCompilerCalls { target_crate },
            using_internal_features,
        )
    }

    // Add an ICE bug report hook.
    let using_internal_features =
        rustc_driver::install_ice_hook("https://github.com/rust-lang/miri/issues/new", |_| ());

    // Init loggers the Miri way.
    init_early_loggers(&early_dcx);

    // Parse our arguments and split them across `rustc` and `miri`.
    let mut miri_config = miri::MiriConfig::default();
    miri_config.env = env_snapshot;

    let mut rustc_args = vec![];
    let mut after_dashdash = false;
    // If user has explicitly enabled/disabled isolation
    let mut isolation_enabled: Option<bool> = None;

    // Note that we require values to be given with `=`, not with a space.
    // This matches how rustc parses `-Z`.
    // However, unlike rustc we do not accept a space after `-Z`.
    for arg in args {
        if rustc_args.is_empty() {
            // Very first arg: binary name.
            rustc_args.push(arg);
        } else if after_dashdash {
            // Everything that comes after `--` is forwarded to the interpreted crate.
            miri_config.args.push(arg);
        } else if arg == "--" {
            after_dashdash = true;
        } else if arg == "-Zmiri-disable-validation" {
            miri_config.validate = false;
        } else if arg == "-Zmiri-disable-stacked-borrows" {
            miri_config.borrow_tracker = None;
        } else if arg == "-Zmiri-tree-borrows" {
            miri_config.borrow_tracker = Some(BorrowTrackerMethod::TreeBorrows);
        } else if arg == "-Zmiri-unique-is-unique" {
            miri_config.unique_is_unique = true;
        } else if arg == "-Zmiri-disable-data-race-detector" {
            miri_config.data_race_detector = false;
            miri_config.weak_memory_emulation = false;
        } else if arg == "-Zmiri-disable-alignment-check" {
            miri_config.check_alignment = miri::AlignmentCheck::None;
        } else if arg == "-Zmiri-symbolic-alignment-check" {
            miri_config.check_alignment = miri::AlignmentCheck::Symbolic;
        } else if arg == "-Zmiri-disable-abi-check" {
            eprintln!(
                "WARNING: the flag `-Zmiri-disable-abi-check` no longer has any effect; \
                    ABI checks cannot be disabled any more"
            );
        } else if arg == "-Zmiri-disable-isolation" {
            if matches!(isolation_enabled, Some(true)) {
                show_error!(
                    "-Zmiri-disable-isolation cannot be used along with -Zmiri-isolation-error"
                );
            } else {
                isolation_enabled = Some(false);
            }
            miri_config.isolated_op = miri::IsolatedOp::Allow;
        } else if arg == "-Zmiri-disable-leak-backtraces" {
            miri_config.collect_leak_backtraces = false;
        } else if arg == "-Zmiri-disable-weak-memory-emulation" {
            miri_config.weak_memory_emulation = false;
        } else if arg == "-Zmiri-track-weak-memory-loads" {
            miri_config.track_outdated_loads = true;
        } else if let Some(param) = arg.strip_prefix("-Zmiri-isolation-error=") {
            if matches!(isolation_enabled, Some(false)) {
                show_error!(
                    "-Zmiri-isolation-error cannot be used along with -Zmiri-disable-isolation"
                );
            } else {
                isolation_enabled = Some(true);
            }

            miri_config.isolated_op = match param {
                "abort" => miri::IsolatedOp::Reject(miri::RejectOpWith::Abort),
                "hide" => miri::IsolatedOp::Reject(miri::RejectOpWith::NoWarning),
                "warn" => miri::IsolatedOp::Reject(miri::RejectOpWith::Warning),
                "warn-nobacktrace" =>
                    miri::IsolatedOp::Reject(miri::RejectOpWith::WarningWithoutBacktrace),
                _ =>
                    show_error!(
                        "-Zmiri-isolation-error must be `abort`, `hide`, `warn`, or `warn-nobacktrace`"
                    ),
            };
        } else if arg == "-Zmiri-ignore-leaks" {
            miri_config.ignore_leaks = true;
            miri_config.collect_leak_backtraces = false;
        } else if arg == "-Zmiri-panic-on-unsupported" {
            miri_config.panic_on_unsupported = true;
        } else if arg == "-Zmiri-strict-provenance" {
            miri_config.provenance_mode = ProvenanceMode::Strict;
        } else if arg == "-Zmiri-permissive-provenance" {
            miri_config.provenance_mode = ProvenanceMode::Permissive;
        } else if arg == "-Zmiri-mute-stdout-stderr" {
            miri_config.mute_stdout_stderr = true;
        } else if arg == "-Zmiri-retag-fields" {
            miri_config.retag_fields = RetagFields::Yes;
        } else if let Some(retag_fields) = arg.strip_prefix("-Zmiri-retag-fields=") {
            miri_config.retag_fields = match retag_fields {
                "all" => RetagFields::Yes,
                "none" => RetagFields::No,
                "scalar" => RetagFields::OnlyScalar,
                _ => show_error!("`-Zmiri-retag-fields` can only be `all`, `none`, or `scalar`"),
            };
        } else if let Some(param) = arg.strip_prefix("-Zmiri-seed=") {
            if miri_config.seed.is_some() {
                show_error!("Cannot specify -Zmiri-seed multiple times!");
            }
            let seed = param.parse::<u64>().unwrap_or_else(|_| {
                show_error!("-Zmiri-seed must be an integer that fits into u64")
            });
            miri_config.seed = Some(seed);
        } else if let Some(_param) = arg.strip_prefix("-Zmiri-env-exclude=") {
            show_error!(
                "`-Zmiri-env-exclude` has been removed; unset env vars before starting Miri instead"
            );
        } else if let Some(param) = arg.strip_prefix("-Zmiri-env-forward=") {
            miri_config.forwarded_env_vars.push(param.to_owned());
        } else if let Some(param) = arg.strip_prefix("-Zmiri-env-set=") {
            let Some((name, value)) = param.split_once('=') else {
                show_error!("-Zmiri-env-set requires an argument of the form <name>=<value>");
            };
            miri_config.set_env_vars.insert(name.to_owned(), value.to_owned());
        } else if let Some(param) = arg.strip_prefix("-Zmiri-track-pointer-tag=") {
            let ids: Vec<u64> = parse_comma_list(param).unwrap_or_else(|err| {
                show_error!("-Zmiri-track-pointer-tag requires a comma separated list of valid `u64` arguments: {err}")
            });
            for id in ids.into_iter().map(miri::BorTag::new) {
                if let Some(id) = id {
                    miri_config.tracked_pointer_tags.insert(id);
                } else {
                    show_error!("-Zmiri-track-pointer-tag requires nonzero arguments");
                }
            }
        } else if let Some(param) = arg.strip_prefix("-Zmiri-track-call-id=") {
            let ids: Vec<u64> = parse_comma_list(param).unwrap_or_else(|err| {
                show_error!("-Zmiri-track-call-id requires a comma separated list of valid `u64` arguments: {err}")
            });
            for id in ids.into_iter().map(miri::CallId::new) {
                if let Some(id) = id {
                    miri_config.tracked_call_ids.insert(id);
                } else {
                    show_error!("-Zmiri-track-call-id requires a nonzero argument");
                }
            }
        } else if let Some(param) = arg.strip_prefix("-Zmiri-track-alloc-id=") {
            let ids = parse_comma_list::<NonZero<u64>>(param).unwrap_or_else(|err| {
                show_error!("-Zmiri-track-alloc-id requires a comma separated list of valid non-zero `u64` arguments: {err}")
            });
            miri_config.tracked_alloc_ids.extend(ids.into_iter().map(miri::AllocId));
        } else if arg == "-Zmiri-track-alloc-accesses" {
            miri_config.track_alloc_accesses = true;
        } else if let Some(param) = arg.strip_prefix("-Zmiri-address-reuse-rate=") {
            miri_config.address_reuse_rate = parse_rate(param)
                .unwrap_or_else(|err| show_error!("-Zmiri-address-reuse-rate {err}"));
        } else if let Some(param) = arg.strip_prefix("-Zmiri-address-reuse-cross-thread-rate=") {
            miri_config.address_reuse_cross_thread_rate = parse_rate(param)
                .unwrap_or_else(|err| show_error!("-Zmiri-address-reuse-cross-thread-rate {err}"));
        } else if let Some(param) = arg.strip_prefix("-Zmiri-compare-exchange-weak-failure-rate=") {
            miri_config.cmpxchg_weak_failure_rate = parse_rate(param).unwrap_or_else(|err| {
                show_error!("-Zmiri-compare-exchange-weak-failure-rate {err}")
            });
        } else if let Some(param) = arg.strip_prefix("-Zmiri-preemption-rate=") {
            miri_config.preemption_rate =
                parse_rate(param).unwrap_or_else(|err| show_error!("-Zmiri-preemption-rate {err}"));
        } else if arg == "-Zmiri-report-progress" {
            // This makes it take a few seconds between progress reports on my laptop.
            miri_config.report_progress = Some(1_000_000);
        } else if let Some(param) = arg.strip_prefix("-Zmiri-report-progress=") {
            let interval = param.parse::<u32>().unwrap_or_else(|err| {
                show_error!("-Zmiri-report-progress requires a `u32`: {}", err)
            });
            miri_config.report_progress = Some(interval);
        } else if let Some(param) = arg.strip_prefix("-Zmiri-provenance-gc=") {
            let interval = param.parse::<u32>().unwrap_or_else(|err| {
                show_error!("-Zmiri-provenance-gc requires a `u32`: {}", err)
            });
            miri_config.gc_interval = interval;
        } else if let Some(param) = arg.strip_prefix("-Zmiri-measureme=") {
            miri_config.measureme_out = Some(param.to_string());
        } else if let Some(param) = arg.strip_prefix("-Zmiri-backtrace=") {
            miri_config.backtrace_style = match param {
                "0" => BacktraceStyle::Off,
                "1" => BacktraceStyle::Short,
                "full" => BacktraceStyle::Full,
                _ => show_error!("-Zmiri-backtrace may only be 0, 1, or full"),
            };
        } else if let Some(param) = arg.strip_prefix("-Zmiri-native-lib=") {
            let filename = param.to_string();
            if std::path::Path::new(&filename).exists() {
                if let Some(other_filename) = miri_config.native_lib {
                    show_error!("-Zmiri-native-lib is already set to {}", other_filename.display());
                }
                miri_config.native_lib = Some(filename.into());
            } else {
                show_error!("-Zmiri-native-lib `{}` does not exist", filename);
            }
        } else if let Some(param) = arg.strip_prefix("-Zmiri-num-cpus=") {
            let num_cpus = param
                .parse::<u32>()
                .unwrap_or_else(|err| show_error!("-Zmiri-num-cpus requires a `u32`: {}", err));
            if !(1..=miri::MAX_CPUS).contains(&usize::try_from(num_cpus).unwrap()) {
                show_error!("-Zmiri-num-cpus must be in the range 1..={}", miri::MAX_CPUS);
            }
            miri_config.num_cpus = num_cpus;
        } else if let Some(param) = arg.strip_prefix("-Zmiri-force-page-size=") {
            let page_size = param.parse::<u64>().unwrap_or_else(|err| {
                show_error!("-Zmiri-force-page-size requires a `u64`: {}", err)
            });
            // Convert from kilobytes to bytes.
            let page_size = if page_size.is_power_of_two() {
                page_size * 1024
            } else {
                show_error!("-Zmiri-force-page-size requires a power of 2: {page_size}");
            };
            miri_config.page_size = Some(page_size);
        } else {
            // Forward to rustc.
            rustc_args.push(arg);
        }
    }
    // `-Zmiri-unique-is-unique` should only be used with `-Zmiri-tree-borrows`
    if miri_config.unique_is_unique
        && !matches!(miri_config.borrow_tracker, Some(BorrowTrackerMethod::TreeBorrows))
    {
        show_error!(
            "-Zmiri-unique-is-unique only has an effect when -Zmiri-tree-borrows is also used"
        );
    }

    debug!("rustc arguments: {:?}", rustc_args);
    debug!("crate arguments: {:?}", miri_config.args);
    run_compiler(
        rustc_args,
        /* target_crate: */ true,
        &mut MiriCompilerCalls { miri_config },
        using_internal_features,
    )
}
