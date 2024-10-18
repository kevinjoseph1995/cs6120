use bril_rs::Program;
use clap::ValueEnum;
#[derive(ValueEnum, Clone, Debug, PartialEq)]
pub enum OptimizationPass {
    LocalDeadCodeElimination,
}

fn local_dead_code_elimination(program: &mut Program) {
    todo!()
}

pub fn apply_optimization(program: &mut Program, optimization: OptimizationPass) {
    match optimization {
        OptimizationPass::LocalDeadCodeElimination => local_dead_code_elimination(program),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
