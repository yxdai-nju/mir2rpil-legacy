use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;

use std::fmt;

use super::rpil::{LowRpilOp, PlaceDesc};

#[derive(Clone)]
pub struct LowRpilMapping {
    mapping: FxHashMap<LowRpilOp, LowRpilOp>,
}

impl LowRpilMapping {
    pub fn new() -> Self {
        Self { mapping: FxHashMap::default() }
    }

    pub fn insert(&mut self, lhs: &LowRpilOp, rhs: &LowRpilOp) {
        // Structurally reduce each operand
        let (lhs, rhs) = (self.reduced_rpil_op(&lhs), self.reduced_rpil_op(&rhs));

        // Insert a mapping for the directly assigned place
        let mut to_be_inserted = vec![];
        to_be_inserted.push((lhs.clone(), rhs.clone()));

        // Insert mappings for places that are bound with operands
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
        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }
    }

    pub fn insert_mappings_for_closure_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        closure_op: &LowRpilOp,
        closure_args_op: &mir::Operand<'tcx>,
        depth: usize,
    ) -> DefId {
        let mut to_be_inserted = vec![];

        // Insert a mapping for the return place
        let mapped_ret = LowRpilOp::Var { depth: depth + 1, index: 0 };
        to_be_inserted.push((mapped_ret, ret_op.clone()));

        // Insert a mapping for the closure place
        let mapped_closure = LowRpilOp::Var { depth: depth + 1, index: 1 };
        to_be_inserted.push((mapped_closure, closure_op.clone()));

        // Insert mappings for argument places
        match closure_args_op {
            mir::Operand::Move(closure_args_place) => {
                let args_place_op = LowRpilOp::from_mir_place(closure_args_place, depth);
                for (key, val) in self.mapping.iter() {
                    let place_index = match key {
                        LowRpilOp::Place { base, place_desc: PlaceDesc::P(place_index) }
                            if **base == args_place_op =>
                            place_index,
                        _ => continue,
                    };
                    let mapped_arg = LowRpilOp::Var { depth: depth + 1, index: place_index + 2 };
                    to_be_inserted.push((mapped_arg, val.clone()));
                }
            }
            _ => unreachable!(),
        };

        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }

        self.reduced_rpil_op(closure_op).assume_closure().unwrap()
    }

    pub fn insert_mappings_for_function_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        args: &[mir::Operand<'tcx>],
        depth: usize,
    ) {
        let mut to_be_inserted = vec![];

        // Insert a mapping for the return place
        let mapped_ret = LowRpilOp::Var { depth: depth + 1, index: 0 };
        to_be_inserted.push((mapped_ret, ret_op.clone()));

        // Insert mappings for argument places
        for (idx, value) in args.iter().enumerate() {
            match value {
                mir::Operand::Copy(_) => unreachable!(),
                mir::Operand::Move(arg_place) => {
                    let arg_op = LowRpilOp::from_mir_place(arg_place, depth);
                    let mapped_arg = LowRpilOp::Var { depth: depth + 1, index: idx + 1 };
                    let val = self.mapping.get(&arg_op).unwrap();
                    to_be_inserted.push((mapped_arg, val.clone()));
                }
                mir::Operand::Constant(_) => {}
            }
        }

        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }
    }

    fn reduced_rpil_op(&self, op: &LowRpilOp) -> LowRpilOp {
        let structurally_reduced_op = match op {
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
        if let Some(mapped_op) = self.mapping.get(&structurally_reduced_op) {
            self.reduced_rpil_op(mapped_op)
        } else {
            structurally_reduced_op
        }
    }

    fn reduced_rpil_op_nonstructural(&self, op: &LowRpilOp) -> LowRpilOp {
        if let Some(mapped_op) = self.mapping.get(op) {
            self.reduced_rpil_op_nonstructural(mapped_op)
        } else {
            op.clone()
        }
    }

    pub fn resolve_indirections_then_clean_up(&mut self, depth: usize) {
        // Insert mappings that are valid beyond the current function scope,
        // i.e. mappings that have a depth lower than the current call stack,
        // by eliminating indirections, then remove over-depth ones
        //
        // Example: Assume the current depth is 1. If 0_1->1_2 and 1_2->0_3
        //          are in the mapping, this method inserts 0_1->0_3 to and
        //          removes 0_1->1_2 and 1_2->0_3 from the mapping
        let mut to_be_inserted = vec![];
        for (key, val) in self.mapping.iter() {
            let reduced_val = self.reduced_rpil_op_nonstructural(val);
            if key.depth() < depth && reduced_val.depth() < depth {
                to_be_inserted.push((key.clone(), reduced_val));
            }
        }
        for (k, v) in to_be_inserted {
            self.mapping.insert(k, v);
        }

        // Remove over-depth mappings
        let mut to_be_removed = vec![];
        for (key, val) in self.mapping.iter() {
            if key.depth() == depth || val.depth() == depth {
                to_be_removed.push(key.clone());
            }
        }
        for k in to_be_removed {
            self.mapping.remove(&k);
        }
    }

    pub fn cleaned_up(&self, argc: usize) -> FxHashMap<LowRpilOp, LowRpilOp> {
        let mut mapping = self.mapping.clone();

        // Insert
        let mut to_be_inserted = vec![];
        for (key, val) in mapping.iter() {
            let reduced_val = self.reduced_rpil_op_nonstructural(val);
            match (key.origin_var_index(), reduced_val.origin_var_index()) {
                (Some(key_index), Some(val_index)) if key_index <= argc && val_index <= argc => {
                    to_be_inserted.push((key.clone(), reduced_val));
                }
                _ => {}
            };
        }
        for (k, v) in to_be_inserted {
            mapping.insert(k, v);
        }

        // Remove
        let mut to_be_removed = vec![];
        for (key, val) in mapping.iter() {
            match (key.origin_var_index(), val.origin_var_index()) {
                (Some(key_index), Some(val_index)) if key_index <= argc && val_index <= argc => {}
                _ => {
                    to_be_removed.push(key.clone());
                }
            };
        }
        for k in to_be_removed {
            mapping.remove(&k);
        }

        mapping
    }
}

impl fmt::Debug for LowRpilMapping {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.mapping)
    }
}
