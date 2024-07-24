use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty, ty::TyCtxt};

use std::mem::discriminant;

use super::debug;
use super::rpil::{LowRpilInst, LowRpilOp, RpilInst};

struct TranslationCtxt {
    mapping: FxHashMap<LowRpilOp, LowRpilOp>,
    depth: usize,
    rpil_insts: Vec<RpilInst>,
}

impl TranslationCtxt {
    fn new() -> Self {
        Self { mapping: FxHashMap::with_hasher(Default::default()), depth: 0, rpil_insts: vec![] }
    }

    fn push_rpil_inst(&mut self, inst: LowRpilInst) {
        println!("[Low-RPIL] {:?}", inst);
    }

    fn enter_function(&mut self) {
        self.depth += 1;
    }

    fn leave_function(&mut self) {
        self.depth -= 1;
        // todo!("remove mappings for current function scope");
    }
}

pub fn translate_func_def<'tcx>(tcx: TyCtxt<'tcx>, func_id: DefId) -> Vec<RpilInst> {
    debug::log_func_mir(tcx, func_id);

    let fn_name = tcx.def_path_str(func_id);
    let fn_id = func_id.index.as_u32();
    println!("===== Entered function `{}` {} =====", fn_name, fn_id);
    if !tcx.is_mir_available(func_id) {
        println!("    (empty)");
        return vec![];
    }

    // Initialize MIR->RPIL translation context
    let mut trcx = TranslationCtxt::new();

    let mir_body = tcx.optimized_mir(func_id);

    // todo!("support jumping between BBs according to terminator targets");
    for (bb, block_data) in mir_body.basic_blocks.iter_enumerated() {
        println!("{:?} of `{}` {}:", bb, fn_name, fn_id);
        translate_basic_block(tcx, block_data, &mut trcx);
    }

    println!("===== Leaving function `{}` {} =====", fn_name, fn_id);
    trcx.rpil_insts
}

fn translate_func_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    func_id: DefId,
    args: Vec<mir::Operand<'tcx>>,
    trcx: &mut TranslationCtxt,
) {
    debug::log_func_mir(tcx, func_id);
    println!("Function Args: {:?}", args);

    trcx.enter_function();
    let fn_name = tcx.def_path_str(func_id);
    let fn_id = func_id.index.as_u32();
    println!("===== Entered function `{}` {} =====", fn_name, fn_id);
    if !tcx.is_mir_available(func_id) {
        println!("    (empty)");
        return;
    }

    let mir_body = tcx.optimized_mir(func_id);

    // TODO: Support jumping between BBs according to terminator targets
    for (bb, block_data) in mir_body.basic_blocks.iter_enumerated() {
        println!("{:?} of `{}` {}:", bb, fn_name, fn_id);
        translate_basic_block(tcx, block_data, trcx);
    }

    println!("===== Leaving function `{}` {} =====", fn_name, fn_id);
    trcx.leave_function();
}

fn translate_basic_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    block_data: &mir::BasicBlockData<'tcx>,
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
    statement: &mir::Statement<'tcx>,
    trcx: &mut TranslationCtxt,
) {
    let statement = &statement.kind;
    match statement {
        mir::StatementKind::Assign(p) => {
            println!("[MIR Stmt] {:?}", statement);
            let (lplace, rvalue) = &**p;
            translate_statement_of_assign(tcx, lplace, rvalue, trcx);
        }
        mir::StatementKind::Intrinsic(intrinsic_func) => {
            println!("[MIR Stmt] {:?}", statement);
            match &**intrinsic_func {
                mir::NonDivergingIntrinsic::Assume(..) => {}
                mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                    println!("[MIR-Intrinsic] CopyNonOverlapping({:?})", cno);
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
            println!("[MIR Stmt-{:?}] Unknown `{:?}`", x, statement);
            unimplemented!();
        }
    }
}

fn translate_statement_of_assign<'tcx>(
    tcx: TyCtxt<'tcx>,
    lplace: &mir::Place<'tcx>,
    rvalue: &mir::Rvalue<'tcx>,
    trcx: &mut TranslationCtxt,
) {
    let lhs = LowRpilOp::from_mir_place(lplace, trcx.depth);
    match rvalue {
        mir::Rvalue::Use(operand) | mir::Rvalue::Cast(_, operand, _) => {
            if let mir::Rvalue::Use(_) = rvalue {
                println!("[Rvalue] Use({:?})", operand);
            } else {
                println!("[Rvalue] Cast({:?})", operand);
            }
            match operand {
                mir::Operand::Copy(rplace) => {
                    let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
                    trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs })
                }
                mir::Operand::Move(rplace) => {
                    let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
                    let moved_rhs = LowRpilOp::Move(Box::new(rhs));
                    trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs: moved_rhs });
                }
                mir::Operand::Constant(_) => {}
            }
        }
        mir::Rvalue::Aggregate(aggregate, values) => {
            println!("[Rvalue] Aggregate({:?}, {:?})", aggregate, values);
            translate_statement_of_assign_aggregate(tcx, lhs, rvalue, trcx);
        }
        mir::Rvalue::Ref(_, kind, rplace) => {
            let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
            match kind {
                mir::BorrowKind::Shared => {
                    println!("[Rvalue] Ref(Shared, {:?})", rplace);
                    let borrowed_rhs = LowRpilOp::Ref(Box::new(rhs));
                    trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs: borrowed_rhs });
                }
                mir::BorrowKind::Mut { kind } => {
                    println!("[Rvalue] Ref(Mut({:?}), {:?})", kind, rplace);
                    let borrowed_rhs = LowRpilOp::MutRef(Box::new(rhs));
                    trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs: borrowed_rhs });
                }
                mir::BorrowKind::Fake(kind) => {
                    println!("[Rvalue] Ref(Fake({:?}), {:?})", kind, rplace);
                    unimplemented!();
                }
            };
        }
        mir::Rvalue::CopyForDeref(rplace) => {
            println!("[Rvalue] CopyForDeref({:?})", rplace);
            let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
            trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs });
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
                    // lhs.p0.p0.p0 = &mut lhs.ext.
                    let ptr = LowRpilOp::Place {
                        base: Box::new(LowRpilOp::Place {
                            base: Box::new(LowRpilOp::Place {
                                base: Box::new(lhs.clone()),
                                place_string: "p0".to_owned(),
                            }),
                            place_string: "p0".to_owned(),
                        }),
                        place_string: "p0".to_owned(),
                    };
                    let ext_place =
                        LowRpilOp::Place { base: Box::new(lhs), place_string: "ext".to_owned() };
                    trcx.push_rpil_inst(LowRpilInst::Assign { lhs: ptr, rhs: ext_place });
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
    lhs: LowRpilOp,
    rvalue: &mir::Rvalue<'tcx>,
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
                let lhs_place = LowRpilOp::Place {
                    base: Box::new(lhs.clone()),
                    place_string: format!("p{}", lidx),
                };
                match value {
                    mir::Operand::Copy(rplace) => {
                        let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
                        trcx.push_rpil_inst(LowRpilInst::Assign { lhs: lhs_place, rhs });
                    }
                    mir::Operand::Move(rplace) => {
                        let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
                        let moved_rhs = LowRpilOp::Move(Box::new(rhs));
                        trcx.push_rpil_inst(LowRpilInst::Assign { lhs: lhs_place, rhs: moved_rhs });
                    }
                    mir::Operand::Constant(_) => {}
                }
            }
        }
        mir::AggregateKind::Adt(_, variant_idx, _, _, _) => {
            println!("[Aggregate] Adt(variant_idx={:?})", variant_idx);
            for (lidx, value) in values.iter().enumerate() {
                let lhs_place = LowRpilOp::Place {
                    base: Box::new(lhs.clone()),
                    place_string: format!("v{}p{}", variant_idx.as_usize(), lidx),
                };
                match value {
                    mir::Operand::Copy(rplace) => {
                        let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
                        trcx.push_rpil_inst(LowRpilInst::Assign { lhs: lhs_place, rhs });
                    }
                    mir::Operand::Move(rplace) => {
                        let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
                        let moved_rhs = LowRpilOp::Move(Box::new(rhs));
                        trcx.push_rpil_inst(LowRpilInst::Assign { lhs: lhs_place, rhs: moved_rhs });
                    }
                    mir::Operand::Constant(_) => {}
                }
            }
        }
        mir::AggregateKind::Closure(def_id, _) => {
            println!("[Aggregate] Closure(def_id={})", def_id.index.as_u32());
            let def_id = *def_id;
            debug::log_func_mir(tcx, def_id);
            trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs: LowRpilOp::Closure { def_id } });
        }
        _ => {
            let x = discriminant(aggregate);
            println!("[Aggregate-{:?}] Unknown `{:?}`", x, aggregate);
            unimplemented!();
        }
    };
}

fn def_id_of_func_operand<'tcx>(func: &mir::Operand<'tcx>) -> DefId {
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

fn is_function_excluded<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let excluded_from_translation: rustc_data_structures::fx::FxHashSet<&str> =
        ["alloc::alloc::exchange_malloc"].iter().cloned().collect();
    let def_path = tcx.def_path_str(def_id);
    excluded_from_translation.contains(def_path.as_str())
}

fn is_fn_trait_shim<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let def_path = tcx.def_path_str(def_id);
    def_path.contains("::call")
        && (def_path.contains("std::ops::Fn")
            || def_path.contains("std::ops::FnMut")
            || def_path.contains("std::ops::FnOnce"))
}

fn translate_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &mir::Terminator<'tcx>,
    trcx: &mut TranslationCtxt,
) {
    let terminator = &terminator.kind;
    match terminator {
        mir::TerminatorKind::Call { ref func, ref args, destination, target, .. } => {
            let args: Vec<_> = args.iter().map(|s| s.node.clone()).collect();
            println!("[MIR Term] Assign(({:?}, {:?}{:?}))", destination, func, args);
            let called_func_id = def_id_of_func_operand(func);
            println!("Function Name: {}", tcx.def_path_str(called_func_id));

            if !is_function_excluded(tcx, called_func_id) {
                if is_fn_trait_shim(tcx, called_func_id) {
                    let place = match args.first().unwrap() {
                        mir::Operand::Move(place) => place,
                        _ => unreachable!(),
                    };
                    let func_place = LowRpilOp::from_mir_place(place, trcx.depth);
                    println!("Function Place: {:?}", func_place);
                    todo!("support storing and referring to closures");
                } else {
                    translate_func_call(tcx, called_func_id, args, trcx);
                }
            }

            println!("Next: {:?}", target);
        }
        mir::TerminatorKind::Drop { place, target, .. } => {
            println!("[MIR Term] Drop({:?})", place);
            println!("Next: {:?}", target);
        }
        mir::TerminatorKind::Assert { cond, msg, target, .. } => {
            println!("[MIR Term] Assert({:?}, {:?})", cond, msg);
            println!("Next: {:?}", target);
        }
        mir::TerminatorKind::Return => {
            println!("Next: return");
            trcx.push_rpil_inst(LowRpilInst::Return);
        }
        mir::TerminatorKind::UnwindResume | mir::TerminatorKind::Unreachable => {
            println!("Next: !");
        }
        mir::TerminatorKind::SwitchInt { discr, ref targets, .. } => {
            println!("[MIR Term] SwitchInt({:?})", discr);
            println!("Next: {:?}", targets.all_targets());
        }
        _ => {
            let x = discriminant(terminator);
            println!("[MIR Term-{:?}] Unknown `{:?}`", x, terminator);
            unimplemented!();
        }
    };
}
