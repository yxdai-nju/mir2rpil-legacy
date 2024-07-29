use rustc_hir::def_id::DefId;
use rustc_middle::mir;

use super::mapping::LowRpilMapping;
use super::path::ExecutionPath;
use super::rpil::{LowRpilInst, LowRpilOp};

pub struct TranslationCtxt {
    pub mappings: Vec<LowRpilMapping>,
    new_variants: Vec<Vec<LowRpilMapping>>,
    functions_to_be_called: Option<FunctionToBeCalled>,
    pub function_to_be_called: Option<DefId>,
    pub depth: usize,
    pub path: ExecutionPath,
}

enum FunctionToBeCalled {
    Function(DefId),
    Closure(Vec<DefId>),
}

impl TranslationCtxt {
    pub fn new(func_name: &str) -> Self {
        let mut execution_path = ExecutionPath::new();
        execution_path.push_function(func_name);
        Self {
            mappings: vec![LowRpilMapping::new()],
            new_variants: vec![],
            functions_to_be_called: None,
            function_to_be_called: None,
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
    }

    pub fn prepare_for_closure_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        closure_op: &LowRpilOp,
        closure_args_op: &mir::Operand<'tcx>,
    ) {
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
        self.functions_to_be_called = Some(FunctionToBeCalled::Closure(closure_def_ids));
    }

    pub fn prepare_for_function_call<'tcx>(
        &mut self,
        ret_op: &LowRpilOp,
        func_def_id: DefId,
        arg_list: &[mir::Operand<'tcx>],
    ) {
        for mapping in self.mappings.iter_mut() {
            mapping.insert_mappings_for_function_call(ret_op, arg_list, self.depth);
        }
        self.functions_to_be_called = Some(FunctionToBeCalled::Function(func_def_id));
    }

    pub fn apply_to_each_variant(&mut self, f: impl Fn(&mut TranslationCtxt)) {
        self.new_variants.clear();
        for (idx, mapping) in self.mappings.iter().cloned().enumerate() {
            let function_to_be_called = match self.functions_to_be_called.take().unwrap() {
                FunctionToBeCalled::Function(def_id) => Some(def_id),
                FunctionToBeCalled::Closure(def_ids) => Some(def_ids[idx]),
            };
            let mut trcx_variant = Self {
                mappings: vec![mapping],
                new_variants: vec![],
                functions_to_be_called: None,
                function_to_be_called,
                depth: self.depth,
                path: self.path.clone(),
            };
            f(&mut trcx_variant);
            self.new_variants.push(trcx_variant.mappings);
        }
        self.merge_variants();
    }

    pub fn add_variant(&mut self) {
        self.new_variants.push(self.mappings.clone());
    }

    pub fn merge_variants(&mut self) {
        self.mappings.clear();
        for variant in self.new_variants.iter_mut() {
            self.mappings.append(variant);
        }
        self.new_variants.clear();
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
}
