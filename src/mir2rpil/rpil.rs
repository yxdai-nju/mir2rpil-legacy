use rustc_hir::def_id::DefId;
use rustc_middle::mir;

use std::fmt;
use std::mem::discriminant;

#[derive(Clone)]
pub enum RpilOp {
    Var(usize),
    Closure(DefId),
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

impl RpilOp {
    pub fn from_mir_place<'tcx>(place: &mir::Place<'tcx>) -> Self {
        let projection = project_rpil_place(place, 0);
        if place.projection.len() > 0 {
            println!("[Projection] {:?}, {:?}", place.local, place.projection);
            println!("[Projection Result] {:?}", projection);
        }
        projection
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
