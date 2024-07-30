use rustc_hir::def_id::DefId;
use rustc_middle::mir;

use std::fmt;
use std::mem::discriminant;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum LowRpilOp {
    Var { depth: usize, index: usize },
    Place { base: Box<LowRpilOp>, place_desc: PlaceDesc },
    Closure { def_id: DefId },
    Ref(Box<LowRpilOp>),
    MutRef(Box<LowRpilOp>),
    Deref(Box<LowRpilOp>),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum PlaceDesc {
    P(usize),
    PExt,
    VP(usize, usize),
}

impl fmt::Debug for PlaceDesc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use PlaceDesc::*;
        match self {
            P(p) => write!(f, "p{}", p),
            PExt => write!(f, "ext"),
            VP(v, p) => write!(f, "v{}p{}", v, p),
        }
    }
}

impl LowRpilOp {
    pub fn assume_closure(&self) -> Option<DefId> {
        use LowRpilOp::*;
        match self {
            Closure { def_id } => Some(*def_id),
            Ref(inner_op) | MutRef(inner_op) => inner_op.assume_closure(),
            _ => None,
        }
    }

    pub fn depth(&self) -> usize {
        use LowRpilOp::*;
        match self {
            Var { depth, .. } => *depth,
            Place { base: op, .. } | Ref(op) | MutRef(op) | Deref(op) => op.depth(),
            Closure { .. } => 0,
        }
    }

    pub fn origin_var_index(&self) -> Option<usize> {
        use LowRpilOp::*;
        match self.origin() {
            Var { index, .. } => Some(index),
            _ => None,
        }
    }

    fn origin(&self) -> LowRpilOp {
        use LowRpilOp::*;
        match self {
            Var { .. } | Closure { .. } => self.clone(),
            Place { base, .. } => base.origin(),
            Ref(op) | MutRef(op) | Deref(op) => op.origin(),
        }
    }

    pub fn replace_origin(&self, from: &LowRpilOp, to: &LowRpilOp) -> Option<LowRpilOp> {
        use LowRpilOp::*;
        if self == from {
            return Some(to.clone());
        }
        match self {
            Var { .. } | Closure { .. } => None,
            Place { base, place_desc } =>
                base.replace_origin(from, to).map(|replaced_base| {
                    Place { base: Box::new(replaced_base), place_desc: place_desc.clone() }
                }),
            Ref(op) => op.replace_origin(from, to).map(|replaced_op| Ref(Box::new(replaced_op))),
            MutRef(op) =>
                op.replace_origin(from, to).map(|replaced_op| MutRef(Box::new(replaced_op))),
            Deref(op) =>
                op.replace_origin(from, to).map(|replaced_op| Deref(Box::new(replaced_op))),
        }
    }
}

impl fmt::Debug for LowRpilOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LowRpilOp::*;
        match self {
            Var { depth, index } => write!(f, "{}_{}", depth, index),
            Place { base, place_desc } => write!(f, "{:?}.{:?}", base, place_desc),
            Closure { def_id } => write!(f, "{{closure:{}}}", def_id.index.as_u32()),
            Ref(op) => write!(f, "& {:?}", op),
            MutRef(op) => write!(f, "&mut {:?}", op),
            Deref(op) => write!(f, "({:?})*", op),
        }
    }
}

pub enum LowRpilInst {
    Assign { lhs: LowRpilOp, rhs: LowRpilOp, moves: bool },
    Return,
}

impl fmt::Debug for LowRpilInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LowRpilInst::*;
        match self {
            Assign { lhs, rhs, moves } =>
                if *moves {
                    write!(f, "{:?} = move {:?};", lhs, rhs)
                } else {
                    write!(f, "{:?} = {:?};", lhs, rhs)
                },
            Return => write!(f, "return;"),
        }
    }
}

impl LowRpilOp {
    pub fn from_mir_place<'tcx>(place: &mir::Place<'tcx>, depth: usize) -> Self {
        let projection = project_rpil_place(place, depth);
        if place.projection.len() > 0 {
            println!("[Projection] {:?}, {:?}", place.local, place.projection);
            println!("[Projection Result] {:?}", projection);
        }
        projection
    }
}

#[inline(always)]
fn project_rpil_place<'tcx>(place: &mir::Place<'tcx>, depth: usize) -> LowRpilOp {
    project_rpil_place_(place, place.projection.len(), depth)
}

fn project_rpil_place_<'tcx>(place: &mir::Place<'tcx>, idx: usize, depth: usize) -> LowRpilOp {
    if idx == 0 {
        return LowRpilOp::Var { depth, index: place.local.as_usize() };
    }
    let rplace = &place.projection[idx - 1];
    match rplace {
        mir::ProjectionElem::Field(ridx, _) =>
            LowRpilOp::Place {
                base: Box::new(project_rpil_place_(place, idx - 1, depth)),
                place_desc: PlaceDesc::P(ridx.as_usize()),
            },
        mir::ProjectionElem::Deref =>
            LowRpilOp::Deref(Box::new(project_rpil_place_(place, idx - 1, depth))),
        mir::ProjectionElem::Downcast(_, variant_idx) => {
            let next_projection = project_rpil_place_(place, idx - 1, depth);
            match next_projection {
                LowRpilOp::Place { base, place_desc } => {
                    let place_index = match place_desc {
                        PlaceDesc::P(place_index) => place_index,
                        _ => unreachable!(),
                    };
                    LowRpilOp::Place {
                        base,
                        place_desc: PlaceDesc::VP(variant_idx.as_usize(), place_index),
                    }
                }
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

pub enum RpilInst {
    Bind(LowRpilOp, LowRpilOp),
    Borrow(LowRpilOp, LowRpilOp),
    BorrowMut(LowRpilOp, LowRpilOp),
    Move(LowRpilOp),
    DerefMove(LowRpilOp),
    DerefPin(LowRpilOp),
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
