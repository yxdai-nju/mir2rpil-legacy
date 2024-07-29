use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir;

use std::fmt;

#[derive(Clone)]
pub struct ExecutionPath {
    call_stack: Vec<String>,
    bb_trace: Vec<(usize, usize)>,
    visited_bbs: FxHashSet<(usize, usize)>,
}

impl ExecutionPath {
    pub fn new() -> Self {
        Self { call_stack: vec![], bb_trace: vec![], visited_bbs: FxHashSet::default() }
    }

    pub fn push_function(&mut self, func_name: &str) {
        self.call_stack.push(func_name.to_owned());
    }

    pub fn pop_function(&mut self) {
        self.call_stack.pop();
    }

    pub fn is_bb_visited(&self, bb: mir::BasicBlock) -> bool {
        let waypoint = (self.call_stack.len() - 1, bb.as_usize());
        self.visited_bbs.contains(&waypoint)
    }

    pub fn push_bb(&mut self, bb: mir::BasicBlock) {
        let waypoint = (self.call_stack.len() - 1, bb.as_usize());
        self.bb_trace.push(waypoint);
        self.visited_bbs.insert(waypoint);
    }

    pub fn pop_bb(&mut self) {
        let waypoint = self.bb_trace.pop().unwrap();
        self.visited_bbs.remove(&waypoint);
    }
}

impl fmt::Debug for ExecutionPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Call Stack: [")?;
        for (idx, func_name) in self.call_stack.iter().enumerate() {
            write!(f, "{}: {}", idx, func_name)?;
            if idx != self.call_stack.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]\nPath: ")?;
        for (idx, (func_idx, bb)) in self.bb_trace.iter().copied().enumerate() {
            write!(f, "{}.bb{}", func_idx, bb)?;
            if idx != self.bb_trace.len() - 1 {
                write!(f, " -> ")?;
            }
        }
        Ok(())
    }
}
