use rustc_hir::def_id::DefId;
use rustc_middle::mir;

use super::mapping::LowRpilMapping;
use super::path::ExecutionPath;
use super::rpil::{LowRpilInst, LowRpilOp};

pub struct TranslationCtxt {
    mappings: Vec<LowRpilMapping>,
    functions_to_be_called: Option<FunctionsToBeCalled>,
    pub depth: usize,
    path: ExecutionPath,
}

enum FunctionsToBeCalled {
    Function(DefId),
    Closure(Vec<DefId>),
}

impl TranslationCtxt {
    pub fn new(func_name: &str) -> Self {
        let mut execution_path = ExecutionPath::new();
        execution_path.push_function(func_name);
        Self {
            mappings: vec![LowRpilMapping::new()],
            functions_to_be_called: None,
            depth: 0,
            path: execution_path,
        }
    }

    pub fn push_rpil_inst(&mut self, inst: LowRpilInst) {
        println!("[Low-RPIL] {:?}", inst);
        match inst {
            LowRpilInst::Assign { lhs, rhs, moves: _moves } => {
                for mapping in self.mappings.iter_mut() {
                    mapping.insert(&lhs, &rhs);
                }
            }
            LowRpilInst::Return => {}
        }
        self.debug_variants();
    }

    pub fn prepare_for_closure_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        closure_op: &LowRpilOp,
        closure_args_op: &mir::Operand<'tcx>,
    ) {
        assert!(self.functions_to_be_called.is_none());
        let mut closure_def_ids = Vec::with_capacity(self.mappings.len());
        for mapping in self.mappings.iter_mut() {
            let closure_def_id = mapping.insert_mappings_for_closure_call(
                ret_op,
                closure_op,
                closure_args_op,
                self.depth,
            );
            closure_def_ids.push(closure_def_id);
        }
        self.functions_to_be_called = Some(FunctionsToBeCalled::Closure(closure_def_ids));
    }

    pub fn prepare_for_function_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        func_def_id: DefId,
        arg_list: &[mir::Operand<'tcx>],
    ) {
        assert!(self.functions_to_be_called.is_none());
        for mapping in self.mappings.iter_mut() {
            mapping.insert_mappings_for_function_call(ret_op, arg_list, self.depth);
        }
        self.functions_to_be_called = Some(FunctionsToBeCalled::Function(func_def_id));
    }

    pub fn translate_function_call_with_each_variant(
        &mut self,
        f: impl Fn(&mut TranslationCtxt, DefId),
    ) {
        let mut snapshots = vec![];
        for (idx, mapping) in self.mappings.iter().cloned().enumerate() {
            let function_to_be_called = match self.functions_to_be_called.take().unwrap() {
                FunctionsToBeCalled::Function(def_id) => def_id,
                FunctionsToBeCalled::Closure(def_ids) => def_ids[idx],
            };
            let mut trcx_variant = Self {
                mappings: vec![mapping],
                functions_to_be_called: None,
                depth: self.depth,
                path: self.path.clone(),
            };
            f(&mut trcx_variant, function_to_be_called);
            snapshots.push(trcx_variant.mappings);
        }
        self.gather_variants(snapshots);
    }

    pub fn enter_function(&mut self, func_name: &str) {
        self.path.push_function(func_name);
        self.depth += 1;
    }

    pub fn leave_function(&mut self) {
        for mapping in self.mappings.iter_mut() {
            mapping.resolve_indirections_then_clean_up(self.depth);
        }
        self.path.pop_function();
        self.depth -= 1;
    }

    pub fn enter_basic_block(&mut self, bb: mir::BasicBlock) {
        self.path.push_bb(bb);
    }

    pub fn leave_basic_block(&mut self) {
        self.path.pop_bb();
    }

    pub fn take_snapshot(&self) -> Vec<LowRpilMapping> {
        self.mappings.clone()
    }

    pub fn recover_from_snapshot(&mut self, mappings: Vec<LowRpilMapping>) {
        self.mappings = mappings;
    }

    pub fn gather_variants(&mut self, mut snapshots: Vec<Vec<LowRpilMapping>>) {
        self.mappings.clear();
        println!("Number of variants: {}", snapshots.len());
        for variant in snapshots.iter_mut() {
            self.mappings.append(variant);
        }
    }

    pub fn is_bb_visited(&self, bb: mir::BasicBlock) -> bool {
        self.path.is_bb_visited(bb)
    }

    pub fn debug_path(&self) {
        println!("{:?}", self.path);
    }

    pub fn debug_variants(&self) {
        for (idx, mapping) in self.mappings.iter().enumerate() {
            println!("Context#{}: {:?}", idx + 1, mapping);
        }
    }
}
