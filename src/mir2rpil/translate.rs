use rustc_data_structures::graph::StartNode;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty, ty::TyCtxt};

use std::mem::discriminant;

use super::context::TranslationCtxt;
use super::debug;
use super::rpil::{LowRpilInst, LowRpilOp, PlaceDesc, RpilInst};

type NextBB = Option<Vec<mir::BasicBlock>>;

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
    let bb0 = mir_body.basic_blocks.start_node();
    let bb0_data = mir_body.basic_blocks.get(bb0).unwrap();
    let _ = translate_basic_block(tcx, &mut trcx, bb0, bb0_data);

    println!("===== Leaving function `{}` {} =====", fn_name, fn_id);
    trcx.rpil_insts
}

fn translate_func_call<'tcx>(tcx: TyCtxt<'tcx>, trcx: &mut TranslationCtxt, func_id: DefId) {
    debug::log_func_mir(tcx, func_id);

    trcx.enter_function(func_id);
    let fn_name = tcx.def_path_str(func_id);
    let fn_id = func_id.index.as_u32();
    println!("===== Entered function `{}` {} =====", fn_name, fn_id);
    if !tcx.is_mir_available(func_id) {
        println!("    (empty)");
        return;
    }

    let mir_body = tcx.optimized_mir(func_id);

    // todo!("support jumping between BBs according to terminator targets")
    let bb0 = mir_body.basic_blocks.start_node();
    let bb0_data = mir_body.basic_blocks.get(bb0).unwrap();
    let _ = translate_basic_block(tcx, trcx, bb0, bb0_data);

    println!("===== Leaving function `{}` {} =====", fn_name, fn_id);
    trcx.leave_function();
}

fn translate_basic_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    trcx: &mut TranslationCtxt,
    _bb: mir::BasicBlock,
    bb_data: &mir::BasicBlockData<'tcx>,
) -> NextBB {
    // println!("{:?} of `{}` {}:", bb, fn_name, fn_id);
    for statement in &bb_data.statements {
        translate_statement(tcx, trcx, statement);
    }
    let terminator = bb_data.terminator();
    let next_bb = translate_terminator(tcx, trcx, terminator);
    println!("---");
    next_bb
}

fn translate_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    trcx: &mut TranslationCtxt,
    statement: &mir::Statement<'tcx>,
) {
    let statement = &statement.kind;
    match statement {
        mir::StatementKind::Assign(p) => {
            println!("[MIR Stmt] {:?}", statement);
            let (lplace, rvalue) = &**p;
            translate_statement_of_assign(tcx, trcx, lplace, rvalue);
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
    trcx: &mut TranslationCtxt,
    lplace: &mir::Place<'tcx>,
    rvalue: &mir::Rvalue<'tcx>,
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
                    trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs, moves: false });
                }
                mir::Operand::Move(rplace) => {
                    let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
                    trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs, moves: true });
                }
                mir::Operand::Constant(_) => {}
            }
        }
        mir::Rvalue::Aggregate(aggregate, values) => {
            println!("[Rvalue] Aggregate({:?}, {:?})", aggregate, values);
            translate_statement_of_assign_aggregate(tcx, trcx, &lhs, rvalue);
        }
        mir::Rvalue::Ref(_, kind, rplace) => {
            let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
            match kind {
                mir::BorrowKind::Shared => {
                    println!("[Rvalue] Ref(Shared, {:?})", rplace);
                    let borrowed_rhs = LowRpilOp::Ref(Box::new(rhs));
                    trcx.push_rpil_inst(LowRpilInst::Assign {
                        lhs,
                        rhs: borrowed_rhs,
                        moves: false,
                    });
                }
                mir::BorrowKind::Mut { kind } => {
                    println!("[Rvalue] Ref(Mut({:?}), {:?})", kind, rplace);
                    let borrowed_rhs = LowRpilOp::MutRef(Box::new(rhs));
                    trcx.push_rpil_inst(LowRpilInst::Assign {
                        lhs,
                        rhs: borrowed_rhs,
                        moves: false,
                    });
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
            trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs, moves: false });
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
                    // operation as: `lhs.p0.p0.p0 = &mut lhs.ext;`.
                    let ptr = LowRpilOp::Place {
                        base: Box::new(LowRpilOp::Place {
                            base: Box::new(LowRpilOp::Place {
                                base: Box::new(lhs.clone()),
                                place_desc: PlaceDesc::P(0),
                            }),
                            place_desc: PlaceDesc::P(0),
                        }),
                        place_desc: PlaceDesc::P(0),
                    };
                    let ext_place =
                        LowRpilOp::Place { base: Box::new(lhs), place_desc: PlaceDesc::PExt };
                    trcx.push_rpil_inst(LowRpilInst::Assign {
                        lhs: ptr,
                        rhs: LowRpilOp::MutRef(Box::new(ext_place)),
                        moves: false,
                    });
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
    trcx: &mut TranslationCtxt,
    lhs: &LowRpilOp,
    rvalue: &mir::Rvalue<'tcx>,
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
                handle_aggregate(trcx, lhs, value, PlaceDesc::P(lidx));
            }
        }
        mir::AggregateKind::Adt(_, variant_idx, _, _, _) => {
            println!("[Aggregate] Adt(variant_idx={:?})", variant_idx);
            for (lidx, value) in values.iter().enumerate() {
                handle_aggregate(trcx, lhs, value, PlaceDesc::VP(variant_idx.as_usize(), lidx));
            }
        }
        mir::AggregateKind::Closure(def_id, _) => {
            println!("[Aggregate] Closure(def_id={})", def_id.index.as_u32());
            let def_id = *def_id;
            debug::log_func_mir(tcx, def_id);
            trcx.push_rpil_inst(LowRpilInst::Assign {
                lhs: lhs.clone(),
                rhs: LowRpilOp::Closure { def_id },
                moves: false,
            });
            for (lidx, value) in values.iter().enumerate() {
                handle_aggregate(trcx, lhs, value, PlaceDesc::P(lidx));
            }
        }
        _ => {
            let x = discriminant(aggregate);
            println!("[Aggregate-{:?}] Unknown `{:?}`", x, aggregate);
            unimplemented!();
        }
    };
}

fn handle_aggregate<'tcx>(
    trcx: &mut TranslationCtxt,
    lhs: &LowRpilOp,
    value: &mir::Operand<'tcx>,
    place_desc: PlaceDesc,
) {
    let lhs_place = LowRpilOp::Place { base: Box::new(lhs.clone()), place_desc };
    match value {
        mir::Operand::Copy(rplace) => {
            let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
            trcx.push_rpil_inst(LowRpilInst::Assign { lhs: lhs_place, rhs, moves: false });
        }
        mir::Operand::Move(rplace) => {
            let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
            trcx.push_rpil_inst(LowRpilInst::Assign { lhs: lhs_place, rhs, moves: true });
        }
        mir::Operand::Constant(_) => {}
    }
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
    trcx: &mut TranslationCtxt,
    terminator: &mir::Terminator<'tcx>,
) -> NextBB {
    let terminator = &terminator.kind;
    match terminator {
        mir::TerminatorKind::Call { ref func, ref args, destination, target, .. } => {
            let args: Vec<_> = args.iter().map(|s| s.node.clone()).collect();
            println!("[MIR Term] Assign(({:?}, {:?}{:?}))", destination, func, args);
            let ret_op = LowRpilOp::from_mir_place(destination, trcx.depth);
            let called_func_id = def_id_of_func_operand(func);
            println!("Function Name: {}", tcx.def_path_str(called_func_id));
            println!("Function Args: {:?}", args);

            if !is_function_excluded(tcx, called_func_id) {
                if is_fn_trait_shim(tcx, called_func_id) {
                    assert_eq!(args.len(), 2);
                    let closure_place = match args.first().unwrap() {
                        mir::Operand::Move(place) => place,
                        _ => unreachable!(),
                    };
                    let closure_op = LowRpilOp::from_mir_place(closure_place, trcx.depth);
                    let closure_args_op = args.last().unwrap();
                    match trcx.reduced_rpil_op(&closure_op).get_inner_closure() {
                        Some(closure_id) => {
                            println!("Closure Name: {}", tcx.def_path_str(closure_id));
                            println!("Closure Args: {:?}", closure_args_op);
                            trcx.prepare_args_mapping_for_closure_call(
                                &ret_op,
                                &closure_op,
                                closure_args_op,
                            );
                            translate_func_call(tcx, trcx, closure_id);
                        }
                        None => unreachable!(),
                    }
                } else {
                    trcx.prepare_args_mapping_for_function_call(&ret_op, &args);
                    translate_func_call(tcx, trcx, called_func_id);
                }
            }

            println!("Next: {:?}", target);
            Some(target.map_or(vec![], |bb| vec![bb]))
        }
        mir::TerminatorKind::Goto { target }
        | mir::TerminatorKind::Assert { target, .. }
        | mir::TerminatorKind::Drop { target, .. } => {
            println!("Next: {:?}", target);
            Some(vec![*target])
        }
        mir::TerminatorKind::SwitchInt { discr, ref targets, .. } => {
            println!("[MIR Term] SwitchInt({:?})", discr);
            println!("Next: {:?}", targets.all_targets());
            Some(targets.all_targets().into())
        }
        mir::TerminatorKind::Return => {
            println!("Next: return");
            trcx.push_rpil_inst(LowRpilInst::Return);
            None
        }
        mir::TerminatorKind::UnwindResume | mir::TerminatorKind::Unreachable => {
            println!("Next: !");
            Some(vec![])
        }
        _ => {
            let x = discriminant(terminator);
            println!("[MIR Term-{:?}] Unknown `{:?}`", x, terminator);
            unimplemented!()
        }
    }
}
