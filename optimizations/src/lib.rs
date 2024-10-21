mod local_dead_code_elimination;
mod local_value_numbering;

use bril_rs::{Code, Program};
use clap::ValueEnum;
use common::BasicBlock;
#[derive(ValueEnum, Clone, Debug, PartialEq)]
pub enum OptimizationPass {
    LocalDeadCodeElimination,
    LocalValueNumbering,
}

impl OptimizationPass {
    pub fn apply(&self, program: &mut Program) {
        match &self {
            OptimizationPass::LocalDeadCodeElimination => {
                local_dead_code_elimination::apply(program)
            }
            OptimizationPass::LocalValueNumbering => local_value_numbering::apply(program),
        }
    }
}

fn apply_for_each_block<F>(program: &mut bril_rs::Program, block_optimization : F)
where F: Fn(&BasicBlock) -> BasicBlock,
{
    program.functions.iter_mut().for_each(|function| {
        // For every function optimze the basic blocks within it.
        function.instrs = common::construct_basic_block_stream(&function.instrs)
            .iter_mut() // For every block
            .map(|block| block_optimization(block)) // Optimize this block
            .map(|optimized_block| -> Vec<Code> {
                // Re-form instruction stream from blocks
                match optimized_block.name {
                    Some(label_name) => {
                        let mut instructions: Vec<Code> = vec![Code::Label {
                            label: label_name,
                            pos: None,
                        }];
                        instructions.extend_from_slice(&optimized_block.instruction_stream);
                        instructions
                    }
                    None => optimized_block.instruction_stream,
                }
            })
            .flatten()
            .collect::<Vec<Code>>();
    });
}
