use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty, ty::TyCtxt};

use std::mem::discriminant;

use super::debug;
use super::rpil::{LowRpilInst, LowRpilOp, PlaceDesc, RpilInst};

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
        match inst {
            LowRpilInst::Assign { lhs, rhs } => {
                let (lhs, rhs) = (self.reduced_rpil_op(&lhs), self.reduced_rpil_op(&rhs));
                println!(
                    "[Reduced Low-RPIL] {:?}",
                    LowRpilInst::Assign { lhs: lhs.clone(), rhs: rhs.clone() }
                );
                self.mapping.insert(lhs, rhs);
                // todo!("also insert bound mappings");
                println!("[Context] {:?}", self.mapping);
            }
            LowRpilInst::Return => {}
        };
    }

    fn reduced_rpil_op(&mut self, op: &LowRpilOp) -> LowRpilOp {
        let op = match op {
            LowRpilOp::Var { .. }
            | LowRpilOp::Closure { .. }
            | LowRpilOp::Ref(_)
            | LowRpilOp::MutRef(_) => op.clone(),
            LowRpilOp::Place { base: inner_op, place_desc } => {
                let reduced_inner_op = self.reduced_rpil_op(inner_op);
                LowRpilOp::Place {
                    base: Box::new(reduced_inner_op),
                    place_desc: place_desc.clone(),
                }
            }
            LowRpilOp::Deref(inner_op) => {
                let reduced_inner_op = self.reduced_rpil_op(inner_op);
                match reduced_inner_op {
                    LowRpilOp::Ref(derefed_op) | LowRpilOp::MutRef(derefed_op) =>
                        self.reduced_rpil_op(&derefed_op),
                    _ => LowRpilOp::Deref(Box::new(reduced_inner_op)),
                }
            }
            LowRpilOp::Move(inner_op) => {
                let reduced_inner_op = self.reduced_rpil_op(inner_op);
                self.mapping.remove(inner_op);
                reduced_inner_op
            }
        };
        if let Some(mapped_op) = self.mapping.get(&op).cloned() {
            self.reduced_rpil_op(&mapped_op)
        } else {
            op
        }
    }

    fn prepare_args_mapping_for_function_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        args: &[mir::Operand<'tcx>],
    ) {
        let mut to_be_removed = vec![];
        let mut to_be_inserted = vec![];

        // Map return place
        let mapped_ret = LowRpilOp::Var { depth: self.depth + 1, index: 0 };
        to_be_inserted.push((mapped_ret, ret_op.clone()));

        // Map argument places
        for (idx, value) in args.iter().enumerate() {
            match value {
                mir::Operand::Copy(_) => unreachable!(),
                mir::Operand::Move(arg_place) => {
                    let arg_op = LowRpilOp::from_mir_place(arg_place, self.depth);
                    let mapped_arg = LowRpilOp::Var { depth: self.depth + 1, index: idx + 1 };
                    let val = self.mapping.get(&arg_op).unwrap();
                    to_be_removed.push(arg_op);
                    to_be_inserted.push((mapped_arg, val.clone()));
                }
                mir::Operand::Constant(_) => {}
            }
        }

        println!("Remove: {:?}", to_be_removed);
        println!("Insert: {:?}", to_be_inserted);
        for k in to_be_removed {
            self.mapping.remove(&k);
        }
        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }
        println!("[Context] {:?}", self.mapping);
    }

    fn prepare_args_mapping_for_closure_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        closure_op: &LowRpilOp,
        args_op: &mir::Operand<'tcx>,
    ) {
        let mut to_be_removed = vec![];
        let mut to_be_inserted = vec![];

        // Map return place
        let mapped_ret = LowRpilOp::Var { depth: self.depth + 1, index: 0 };
        to_be_inserted.push((mapped_ret, ret_op.clone()));

        // Map closure place
        let mapped_closure = LowRpilOp::Var { depth: self.depth + 1, index: 1 };
        to_be_inserted.push((mapped_closure, closure_op.clone()));

        // Map argument places
        match args_op {
            mir::Operand::Move(args_place) => {
                let args_place = LowRpilOp::from_mir_place(args_place, self.depth);
                for (key, val) in self.mapping.iter() {
                    let place_index = match key {
                        LowRpilOp::Place { base, place_desc: PlaceDesc::P(place_index) }
                            if **base == args_place =>
                            place_index,
                        _ => continue,
                    };
                    let mapped_arg =
                        LowRpilOp::Var { depth: self.depth + 1, index: place_index + 2 };
                    to_be_removed.push(key.clone());
                    to_be_inserted.push((mapped_arg, val.clone()));
                }
            }
            _ => unreachable!(),
        };

        println!("Remove: {:?}", to_be_removed);
        println!("Insert: {:?}", to_be_inserted);
        for k in to_be_removed {
            self.mapping.remove(&k);
        }
        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }
        println!("[Context] {:?}", self.mapping);
    }

    fn enter_function(&mut self) {
        self.depth += 1;
    }

    fn leave_function(&mut self) {
        // Remove mappings for current function scope
        let mut to_be_removed = vec![];
        for (key, val) in self.mapping.iter() {
            if key.depth() == self.depth || val.depth() == self.depth {
                to_be_removed.push(key.clone());
            }
        }
        println!("Remove: {:?}", to_be_removed);
        for k in to_be_removed {
            self.mapping.remove(&k);
        }
        println!("[Context] {:?}", self.mapping);
        self.depth -= 1;
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
        translate_basic_block(tcx, &mut trcx, block_data);
    }

    println!("===== Leaving function `{}` {} =====", fn_name, fn_id);
    trcx.rpil_insts
}

fn translate_func_call<'tcx>(tcx: TyCtxt<'tcx>, trcx: &mut TranslationCtxt, func_id: DefId) {
    debug::log_func_mir(tcx, func_id);

    trcx.enter_function();
    let fn_name = tcx.def_path_str(func_id);
    let fn_id = func_id.index.as_u32();
    println!("===== Entered function `{}` {} =====", fn_name, fn_id);
    if !tcx.is_mir_available(func_id) {
        println!("    (empty)");
        return;
    }

    let mir_body = tcx.optimized_mir(func_id);

    // todo!("support jumping between BBs according to terminator targets")
    for (bb, block_data) in mir_body.basic_blocks.iter_enumerated() {
        println!("{:?} of `{}` {}:", bb, fn_name, fn_id);
        translate_basic_block(tcx, trcx, block_data);
    }

    println!("===== Leaving function `{}` {} =====", fn_name, fn_id);
    trcx.leave_function();
}

fn translate_basic_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    trcx: &mut TranslationCtxt,
    block_data: &mir::BasicBlockData<'tcx>,
) {
    for statement in &block_data.statements {
        translate_statement(tcx, trcx, statement);
    }
    if let Some(terminator) = &block_data.terminator {
        translate_terminator(tcx, trcx, terminator);
    }
    println!("---");
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
            translate_statement_of_assign_aggregate(tcx, trcx, &lhs, rvalue);
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
) {
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
                    // todo!("add args mapping before translating a function call");
                    trcx.prepare_args_mapping_for_function_call(&ret_op, &args);
                    translate_func_call(tcx, trcx, called_func_id);
                }
            }

            println!("Next: {:?}", target);
        }
        mir::TerminatorKind::Goto { target }
        | mir::TerminatorKind::Assert { target, .. }
        | mir::TerminatorKind::Drop { target, .. } => {
            println!("Next: {:?}", target);
        }
        mir::TerminatorKind::SwitchInt { discr, ref targets, .. } => {
            println!("[MIR Term] SwitchInt({:?})", discr);
            println!("Next: {:?}", targets.all_targets());
        }
        mir::TerminatorKind::Return => {
            println!("Next: return");
            trcx.push_rpil_inst(LowRpilInst::Return);
        }
        mir::TerminatorKind::UnwindResume | mir::TerminatorKind::Unreachable => {
            println!("Next: !");
        }
        _ => {
            let x = discriminant(terminator);
            println!("[MIR Term-{:?}] Unknown `{:?}`", x, terminator);
            unimplemented!();
        }
    };
}
