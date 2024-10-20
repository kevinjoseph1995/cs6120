mod local_dead_code_elimination;

use bril_rs::Program;
use clap::ValueEnum;
#[derive(ValueEnum, Clone, Debug, PartialEq)]
pub enum OptimizationPass {
    LocalDeadCodeElimination,
}

impl OptimizationPass {
    pub fn apply(&self, program: &mut Program) {
        match &self {
            OptimizationPass::LocalDeadCodeElimination => {
                local_dead_code_elimination::apply(program)
            }
        }
    }
}