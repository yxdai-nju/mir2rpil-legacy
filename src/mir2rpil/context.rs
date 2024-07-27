use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir;

use super::path::ExecutionPath;
use super::rpil::{LowRpilInst, LowRpilOp, PlaceDesc, RpilInst};

pub struct TranslationCtxt {
    pub mapping: FxHashMap<LowRpilOp, LowRpilOp>,
    pub depth: usize,
    pub rpil_insts: Vec<RpilInst>,
    pub path: ExecutionPath,
}

impl TranslationCtxt {
    pub fn new() -> Self {
        Self {
            mapping: FxHashMap::with_hasher(Default::default()),
            depth: 0,
            rpil_insts: vec![],
            path: ExecutionPath::new(),
        }
    }

    pub fn push_rpil_inst(&mut self, inst: LowRpilInst) {
        println!("[Low-RPIL] {:?}", inst);
        match inst {
            LowRpilInst::Assign { lhs, rhs, moves } => {
                let (lhs, rhs) = (self.reduced_rpil_op(&lhs), self.reduced_rpil_op(&rhs));
                println!(
                    "[Reduced Low-RPIL] {:?}",
                    LowRpilInst::Assign { lhs: lhs.clone(), rhs: rhs.clone(), moves }
                );

                // Insert mapping for the directly assigned place
                let mut to_be_inserted = vec![];
                to_be_inserted.push((lhs.clone(), rhs.clone()));

                // Insert mappings for contagious places
                //
                // Example: If A.p0->x and A.p1->y, the assignment `B = A;` will
                //          insert B.p0->x and B.p1->y to the context
                for (key, val) in self.mapping.iter() {
                    let replaced_key = key.replace_origin(&rhs, &lhs);
                    let replaced_val = val.replace_origin(&rhs, &lhs);
                    if replaced_key.is_some() || replaced_val.is_some() {
                        to_be_inserted.push((
                            replaced_key.unwrap_or(key.clone()),
                            replaced_val.unwrap_or(val.clone()),
                        ));
                    }
                }

                println!("Insert: {:?}", to_be_inserted);
                for (k, v) in to_be_inserted {
                    self.mapping.insert(k, v);
                }
                println!("[Context] {:?}", self.mapping);
            }
            LowRpilInst::Return => {}
        };
    }

    fn reduced_rpil_op_nonstructural(&self, op: &LowRpilOp) -> LowRpilOp {
        if let Some(mapped_op) = self.mapping.get(op) {
            self.reduced_rpil_op_nonstructural(mapped_op)
        } else {
            op.clone()
        }
    }

    pub fn reduced_rpil_op(&self, op: &LowRpilOp) -> LowRpilOp {
        let op = match op {
            LowRpilOp::Var { .. } | LowRpilOp::Closure { .. } => op.clone(),
            LowRpilOp::Place { base: inner_op, place_desc } => {
                let reduced_inner_op = self.reduced_rpil_op(inner_op);
                LowRpilOp::Place {
                    base: Box::new(reduced_inner_op),
                    place_desc: place_desc.clone(),
                }
            }
            LowRpilOp::Ref(refed_op) | LowRpilOp::MutRef(refed_op) =>
                match *refed_op.clone() {
                    LowRpilOp::Deref(derefed_op) => *derefed_op,
                    _ => op.clone(),
                },
            LowRpilOp::Deref(inner_op) => {
                let reduced_inner_op = self.reduced_rpil_op(inner_op);
                match reduced_inner_op {
                    LowRpilOp::Ref(derefed_op) | LowRpilOp::MutRef(derefed_op) =>
                        self.reduced_rpil_op(&derefed_op),
                    _ => LowRpilOp::Deref(Box::new(reduced_inner_op)),
                }
            }
        };
        if let Some(mapped_op) = self.mapping.get(&op).cloned() {
            self.reduced_rpil_op(&mapped_op)
        } else {
            op
        }
    }

    pub fn prepare_args_mapping_for_function_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        args: &[mir::Operand<'tcx>],
    ) {
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
                    to_be_inserted.push((mapped_arg, val.clone()));
                }
                mir::Operand::Constant(_) => {}
            }
        }

        println!("Insert: {:?}", to_be_inserted);
        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }
        println!("[Context] {:?}", self.mapping);
    }

    pub fn prepare_args_mapping_for_closure_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        closure_op: &LowRpilOp,
        args_op: &mir::Operand<'tcx>,
    ) {
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
                    to_be_inserted.push((mapped_arg, val.clone()));
                }
            }
            _ => unreachable!(),
        };

        println!("Insert: {:?}", to_be_inserted);
        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }
        println!("[Context] {:?}", self.mapping);
    }

    pub fn initialize_with_function(&mut self, func_name: String) {
        self.depth = 0;
        self.path.push_function(func_name);
    }

    pub fn enter_function(&mut self, func_name: String) {
        self.depth += 1;
        self.path.push_function(func_name);
    }

    pub fn leave_function(&mut self) {
        // Insert mappings that are valid out of the current function scope, by
        // following through indirections
        //
        // Example: If 0_1->1_2 and 1_2->0_3, insert 0_1->0_3 to the context
        let mut to_be_inserted = vec![];
        for (key, val) in self.mapping.iter() {
            let reduced_val = self.reduced_rpil_op_nonstructural(val);
            if key.depth() < self.depth && reduced_val.depth() < self.depth {
                to_be_inserted.push((key.clone(), reduced_val));
            }
        }
        println!("Insert: {:?}", to_be_inserted);
        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }

        // Remove mappings that are valid only for the current function scope
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
        self.path.pop_function();
        self.depth -= 1;
    }
}
