use rustc_hir::def_id::DefId;

pub struct Roadmap {
    function_stack: Vec<DefId>,
    waypoints: Vec<Waypoint>,
}

struct Waypoint {}

impl Roadmap {
    pub fn new() -> Self {
        Self { function_stack: vec![], waypoints: vec![] }
    }
}
