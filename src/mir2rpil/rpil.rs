use rustc_hir::def_id::DefId;
use rustc_middle::mir;

use std::fmt;
use std::mem::discriminant;

#[derive(Clone)]
pub enum LowRpilOp {
    Var { depth: usize, index: usize },
    Place { base: Box<LowRpilOp>, place_string: String },
    Closure { def_id: DefId },
    Ref(Box<LowRpilOp>),
    MutRef(Box<LowRpilOp>),
    Deref(Box<LowRpilOp>),
    Move(Box<LowRpilOp>),
}

impl fmt::Debug for LowRpilOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LowRpilOp::*;
        match self {
            Var { depth, index } => write!(f, "{}_{}", depth, index),
            Place { base, place_string } => write!(f, "{:?}.{}", base, place_string),
            Closure { def_id } => write!(f, "{{closure:{}}}", def_id.index.as_u32()),
            Ref(op) => write!(f, "& {:?}", op),
            MutRef(op) => write!(f, "&mut {:?}", op),
            Deref(op) => write!(f, "({:?})*", op),
            Move(op) => write!(f, "move {:?}", op),
        }
    }
}

pub enum LowRpilInst {
    Assign { lhs: LowRpilOp, rhs: LowRpilOp },
    Return,
}

impl fmt::Debug for LowRpilInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LowRpilInst::*;
        match self {
            Assign { lhs, rhs } => write!(f, "{:?} = {:?};", lhs, rhs),
            Return => write!(f, "return;"),
        }
    }
}

impl LowRpilOp {
    pub fn from_mir_place<'tcx>(place: &mir::Place<'tcx>, depth: usize) -> Self {
        let projection = project_rpil_place(place, 0, depth);
        if place.projection.len() > 0 {
            println!("[Projection] {:?}, {:?}", place.local, place.projection);
            println!("[Projection Result] {:?}", projection);
        }
        projection
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

fn project_rpil_place<'tcx>(place: &mir::Place<'tcx>, idx: usize, depth: usize) -> LowRpilOp {
    if idx == place.projection.len() {
        return LowRpilOp::Var { depth, index: place.local.as_usize() };
    }
    let rplace = &place.projection[idx];
    match rplace {
        mir::ProjectionElem::Field(ridx, _) =>
            LowRpilOp::Place {
                base: Box::new(project_rpil_place(place, idx + 1, depth)),
                place_string: format!("p{}", ridx.as_usize()),
            },
        mir::ProjectionElem::Deref =>
            LowRpilOp::Deref(Box::new(project_rpil_place(place, idx + 1, depth))),
        mir::ProjectionElem::Downcast(_, variant_idx) => {
            let next_projection = project_rpil_place(place, idx + 1, depth);
            match next_projection {
                LowRpilOp::Place { base, place_string } =>
                    LowRpilOp::Place {
                        base,
                        place_string: format!("v{}{}", variant_idx.as_usize(), place_string),
                    },
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
