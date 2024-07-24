use rustc_hir::{self as hir};
use rustc_middle::{mir, ty, ty::TyCtxt};

use std::fmt;
use std::mem::discriminant;

#[derive(Clone)]
pub enum RpilOp {
    Var(usize),
    Closure(hir::def_id::DefId),
    Place(Box<RpilOp>, String),
    Deref(Box<RpilOp>),
}

impl fmt::Debug for RpilOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RpilOp::*;
        match self {
            Var(var) => write!(f, "${}", var),
            Closure(closure_id) => write!(f, "{{closure:{}}}", closure_id.index.as_u32()),
            Place(op, place) => write!(f, "{:?}.{}", op, place),
            Deref(op) => write!(f, "({:?})*", op),
        }
    }
}

pub enum RpilInst {
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

#[allow(clippy::needless_lifetimes)]
fn project_rpil_place<'tcx>(place: &mir::Place<'tcx>, idx: usize) -> RpilOp {
    if idx == place.projection.len() {
        return RpilOp::Var(place.local.as_usize());
    }
    let rplace = &place.projection[idx];
    match rplace {
        mir::ProjectionElem::Field(ridx, _) =>
            RpilOp::Place(
                Box::new(project_rpil_place(place, idx + 1)),
                format!("p{}", ridx.as_usize()),
            ),
        mir::ProjectionElem::Deref => RpilOp::Deref(Box::new(project_rpil_place(place, idx + 1))),
        mir::ProjectionElem::Downcast(_, variant_idx) => {
            let next_projection = project_rpil_place(place, idx + 1);
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

fn rpil_place<'tcx>(place: &mir::Place<'tcx>) -> RpilOp {
    let projection = project_rpil_place(place, 0);
    if place.projection.len() > 0 {
        println!("[Projection] {:?}, {:?}", place.local, place.projection);
        println!("[Projection Result] {:?}", projection);
    }
    projection
}

struct TranslationCtxt {
    rpil_insts: Vec<RpilInst>,
}

impl TranslationCtxt {
    fn new() -> Self {
        Self { rpil_insts: vec![] }
    }

    fn push_rpil_inst(&mut self, inst: RpilInst) {
        println!("[RPIL] {:?}", inst);
        self.rpil_insts.push(inst);
    }
}

pub fn prepare_debug_log_func_mir() {
    use std::fs;
    use std::path::PathBuf;

    let crate_root = std::env::var("CARGO_MANIFEST_DIR").expect("Failed to get CARGO_MANIFEST_DIR");
    let log_dir = PathBuf::from(crate_root).join("playground").join("mir");
    fs::create_dir_all(&log_dir).unwrap();

    // If the directory already existed, clean it
    if log_dir.is_dir() {
        for entry in fs::read_dir(&log_dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_file() {
                fs::remove_file(path).unwrap();
            }
        }
    }
}

#[allow(clippy::needless_lifetimes)]
fn debug_log_func_mir<'tcx>(tcx: TyCtxt<'tcx>, func_id: hir::def_id::DefId) {
    use std::fs::File;
    use std::io::Write;
    use std::path::PathBuf;

    let crate_root = std::env::var("CARGO_MANIFEST_DIR").expect("Failed to get CARGO_MANIFEST_DIR");
    let log_dir = PathBuf::from(crate_root).join("playground").join("mir");

    let debug_output = if !tcx.is_mir_available(func_id) {
        "(empty)\n".into()
    } else {
        let mir_body = tcx.optimized_mir(func_id);
        format!("{:?}\n{:#?}\n\n", func_id, mir_body)
    };
    let func_def_path = tcx.def_path_str(func_id);
    let func_id = func_id.index.as_u32();

    let log_path = log_dir.join(format!("{}.{}.log", func_def_path, func_id));
    let mut file = File::create(&log_path)
        .unwrap_or_else(|_| panic!("Failed to open `{}`", log_path.display()));
    writeln!(file, "{}", debug_output)
        .unwrap_or_else(|_| panic!("Failed to write to `{}`", log_path.display()));
}

#[allow(clippy::needless_lifetimes)]
pub fn debug_func_rpil_insts<'tcx>(
    tcx: TyCtxt<'tcx>,
    func_id: hir::def_id::DefId,
    rpil_insts: &Vec<RpilInst>,
) {
    let fn_name = tcx.def_path_str(func_id);
    let fn_id = func_id.index.as_u32();
    println!("[RPIL] `{}` {}:", fn_name, fn_id);
    if !rpil_insts.is_empty() {
        for inst in rpil_insts {
            println!("    {:?}", inst);
        }
    } else {
        println!("    (empty)");
    }
}

#[allow(clippy::needless_lifetimes)]
pub fn translate_func_def<'tcx>(tcx: TyCtxt<'tcx>, func_id: hir::def_id::DefId) -> Vec<RpilInst> {
    debug_log_func_mir(tcx, func_id);

    let fn_name = tcx.def_path_str(func_id);
    let fn_id = func_id.index.as_u32();
    println!("[MIR] `{}` {}:", fn_name, fn_id);
    if !tcx.is_mir_available(func_id) {
        println!("    (empty)");
        return vec![];
    }

    // Initialize MIR->RPIL translation context
    let mut trcx = TranslationCtxt::new();

    let mir_body = tcx.optimized_mir(func_id);

    // TODO: Support jumping between BBs according to terminator targets
    for (bb, block_data) in mir_body.basic_blocks.iter_enumerated() {
        println!("{:?} of `{}` {}:", bb, fn_name, fn_id);
        translate_basic_block(tcx, block_data, &mut trcx);
    }

    trcx.rpil_insts
}

#[allow(clippy::needless_lifetimes)]
fn _translate_func_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    func_id: hir::def_id::DefId,
    _args: Vec<mir::Operand<'tcx>>,
) -> Vec<RpilInst> {
    debug_log_func_mir(tcx, func_id);
    // match args.first().unwrap() {
    //     mir::Operand::Copy(rplace) => {
    //         trcx.push_rpil_inst(RpilInst::Bind(
    //             RpilOp::Var(place.local.as_usize()),
    //             rpil_place(rplace),
    //         ));
    //     }
    //     mir::Operand::Move(rplace) => {
    //         trcx.push_rpil_inst(RpilInst::Move(rpil_place(rplace)));
    //         trcx.push_rpil_inst(RpilInst::Bind(
    //             RpilOp::Var(place.local.as_usize()),
    //             rpil_place(rplace),
    //         ));
    //     }
    //     mir::Operand::Constant(_) => {}
    // }

    vec![]
}

fn translate_basic_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    block_data: &'tcx mir::BasicBlockData<'tcx>,
    trcx: &mut TranslationCtxt,
) {
    for statement in &block_data.statements {
        translate_statement(tcx, statement, trcx);
    }
    if let Some(terminator) = &block_data.terminator {
        translate_terminator(tcx, terminator, trcx);
    }
    println!("---");
}

fn translate_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    statement: &'tcx mir::Statement<'tcx>,
    trcx: &mut TranslationCtxt,
) {
    let statement = &statement.kind;
    match statement {
        mir::StatementKind::Assign(p) => {
            println!("Statement: {:?}", statement);
            let (place, rvalue) = &**p;
            translate_statement_of_assign(tcx, place, rvalue, trcx);
        }
        mir::StatementKind::Intrinsic(intrinsic_func) => {
            println!("Statement: {:?}", statement);
            match &**intrinsic_func {
                mir::NonDivergingIntrinsic::Assume(..) => {}
                mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                    println!("[Intrinsic] CopyNonOverlapping({:?})", cno);
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

fn translate_statement_of_assign<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: &'tcx mir::Place<'tcx>,
    rvalue: &'tcx mir::Rvalue<'tcx>,
    trcx: &mut TranslationCtxt,
) {
    let place = rpil_place(place);
    println!("[LHS] {:?}", place);
    match rvalue {
        mir::Rvalue::Use(operand) | mir::Rvalue::Cast(_, operand, _) => {
            if let mir::Rvalue::Use(_) = rvalue {
                println!("[Rvalue] Use({:?})", operand);
            } else {
                println!("[Rvalue] Cast({:?})", operand);
            }
            match operand {
                mir::Operand::Copy(rplace) => {
                    trcx.push_rpil_inst(RpilInst::Bind(place, rpil_place(rplace)));
                }
                mir::Operand::Move(rplace) => {
                    trcx.push_rpil_inst(RpilInst::Move(rpil_place(rplace)));
                    trcx.push_rpil_inst(RpilInst::Bind(place, rpil_place(rplace)));
                }
                mir::Operand::Constant(_) => {}
            }
        }
        mir::Rvalue::Aggregate(aggregate, values) => {
            println!("[Rvalue] Aggregate({:?}, {:?})", aggregate, values);
            translate_statement_of_assign_aggregate(tcx, place, rvalue, trcx);
        }
        mir::Rvalue::Ref(_, kind, rplace) => {
            let (lhs, rhs) = (place, rpil_place(rplace));
            match kind {
                mir::BorrowKind::Shared => {
                    println!("[Rvalue] Ref(Shared, {:?})", rplace);
                    trcx.push_rpil_inst(RpilInst::Borrow(lhs, rhs));
                }
                mir::BorrowKind::Mut { kind } => {
                    println!("[Rvalue] Ref(Mut({:?}), {:?})", kind, rplace);
                    trcx.push_rpil_inst(RpilInst::BorrowMut(lhs, rhs));
                }
                mir::BorrowKind::Fake(kind) => {
                    println!("[Rvalue] Ref(Fake({:?}), {:?})", kind, rplace);
                    unimplemented!();
                }
            };
        }
        mir::Rvalue::CopyForDeref(rplace) => {
            println!("[Rvalue] CopyForDeref({:?})", rplace);
            trcx.push_rpil_inst(RpilInst::Bind(place, rpil_place(rplace)));
        }
        mir::Rvalue::ShallowInitBox(op, ty) => {
            println!("[Rvalue] ShallowInitBox({:?}, {:?})", op, ty);
            match op {
                mir::Operand::Copy(..) => {
                    unimplemented!();
                }
                mir::Operand::Move(_ptr) => {
                    // The `lhs = ShallowInitBox(ptr, T)` operation is similar to
                    // `lhs = Box::<T>::from_raw(ptr, ..)`. It's sufficient to know
                    // that the reference stored within lhs (lhs.p0.p0.p0)
                    // points to some external (heap) location, which we represent
                    // as lhs.ext.
                    //
                    // Therefore, we omit the ptr argument and interpret this
                    // operation as:
                    //
                    // BORROW-MUT lhs.p0.p0.p0, lhs.ext.
                    let ptr = RpilOp::Place(
                        Box::new(RpilOp::Place(
                            Box::new(RpilOp::Place(Box::new(place.clone()), "p0".to_owned())),
                            "p0".to_owned(),
                        )),
                        "p0".to_owned(),
                    );
                    let ext_place = RpilOp::Place(Box::new(place), "ext".to_owned());
                    trcx.push_rpil_inst(RpilInst::BorrowMut(ptr, ext_place));
                }
                mir::Operand::Constant(_) => {}
            }
        }
        mir::Rvalue::Discriminant(..)
        | mir::Rvalue::NullaryOp(..)
        | mir::Rvalue::UnaryOp(..)
        | mir::Rvalue::BinaryOp(..) => {}
        _ => {
            let x = discriminant(rvalue);
            println!("[Rvalue-{:?}] Unknown `{:?}`", x, rvalue);
            unimplemented!();
        }
    }
}

fn translate_statement_of_assign_aggregate<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: RpilOp,
    rvalue: &'tcx mir::Rvalue<'tcx>,
    trcx: &mut TranslationCtxt,
) {
    let (aggregate, values) = match rvalue {
        mir::Rvalue::Aggregate(aggregate, values) => (&**aggregate, values),
        _ => unreachable!(),
    };
    match aggregate {
        mir::AggregateKind::Array(..) | mir::AggregateKind::Tuple => {
            if let mir::AggregateKind::Array(..) = aggregate {
                println!("[Aggregate] Array({:?})", values);
            } else {
                println!("[Aggregate] Tuple({:?})", values);
            }
            for (lidx, value) in values.iter().enumerate() {
                match value {
                    mir::Operand::Copy(rplace) => {
                        trcx.push_rpil_inst(RpilInst::Bind(
                            RpilOp::Place(Box::new(place.clone()), format!("p{}", lidx)),
                            rpil_place(rplace),
                        ));
                    }
                    mir::Operand::Move(rplace) => {
                        trcx.push_rpil_inst(RpilInst::Move(rpil_place(rplace)));
                        trcx.push_rpil_inst(RpilInst::Bind(
                            RpilOp::Place(Box::new(place.clone()), format!("p{}", lidx)),
                            rpil_place(rplace),
                        ));
                    }
                    mir::Operand::Constant(_) => {}
                }
            }
        }
        mir::AggregateKind::Adt(_, variant_idx, _, _, _) => {
            println!("[Aggregate] Adt(variant_idx={:?})", variant_idx);
            for (lidx, value) in values.iter().enumerate() {
                match value {
                    mir::Operand::Copy(rplace) => {
                        trcx.push_rpil_inst(RpilInst::Bind(
                            RpilOp::Place(
                                Box::new(place.clone()),
                                format!("v{}p{}", variant_idx.as_usize(), lidx),
                            ),
                            rpil_place(rplace),
                        ));
                    }
                    mir::Operand::Move(rplace) => {
                        trcx.push_rpil_inst(RpilInst::Move(rpil_place(rplace)));
                        trcx.push_rpil_inst(RpilInst::Bind(
                            RpilOp::Place(
                                Box::new(place.clone()),
                                format!("v{}p{}", variant_idx.as_usize(), lidx),
                            ),
                            rpil_place(rplace),
                        ));
                    }
                    mir::Operand::Constant(_) => {}
                }
            }
        }
        mir::AggregateKind::Closure(closure_id, _) => {
            println!("[Aggregate] Closure(def_id={})", closure_id.index.as_u32());
            // debug_log_func_mir(tcx, *closure_id);
            translate_func_def(tcx, *closure_id); // DEBUG
            trcx.push_rpil_inst(RpilInst::Bind(place, RpilOp::Closure(*closure_id)));
        }
        _ => {
            let x = discriminant(aggregate);
            println!("[Aggregate-{:?}] Unknown `{:?}`", x, aggregate);
            unimplemented!();
        }
    };
}

#[allow(clippy::needless_lifetimes)]
fn is_function_excluded<'tcx>(tcx: TyCtxt<'tcx>, def_id: hir::def_id::DefId) -> bool {
    let excluded_from_translation: rustc_data_structures::fx::FxHashSet<&str> =
        ["alloc::alloc::exchange_malloc"].iter().cloned().collect();
    let def_path = tcx.def_path_str(def_id);
    excluded_from_translation.contains(def_path.as_str())
}

#[allow(clippy::needless_lifetimes)]
fn is_fn_trait_shim<'tcx>(tcx: TyCtxt<'tcx>, def_id: hir::def_id::DefId) -> bool {
    let def_path = tcx.def_path_str(def_id);
    def_path.contains("::call")
        && (def_path.contains("std::ops::Fn")
            || def_path.contains("std::ops::FnMut")
            || def_path.contains("std::ops::FnOnce"))
}

fn translate_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &'tcx mir::Terminator<'tcx>,
    _trcx: &mut TranslationCtxt,
) {
    let terminator = &terminator.kind;
    match terminator {
        mir::TerminatorKind::Call { ref func, ref args, destination, target, .. } => {
            let args: Vec<_> = args.iter().map(|s| s.node.clone()).collect();
            println!("Terminator: Assign(({:?}, {:?}{:?}))", destination, func, args);
            let called_func_id = def_id_of_func_operand(func);
            println!("Function Name: {}", tcx.def_path_str(called_func_id));

            if !is_function_excluded(tcx, called_func_id) {
                if is_fn_trait_shim(tcx, called_func_id) {
                    let place = match args.first().unwrap() {
                        mir::Operand::Move(place) => place,
                        _ => unreachable!(),
                    };
                    println!("Function Place: {:?}", rpil_place(place));
                    todo!("support storing and referring to closures");
                } else {
                    // let rpil_insts = translate_func_call(tcx, called_func_id, args);
                    let rpil_insts = translate_func_def(tcx, called_func_id); // DEBUG
                    debug_func_rpil_insts(tcx, called_func_id, &rpil_insts);
                }
            }

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
