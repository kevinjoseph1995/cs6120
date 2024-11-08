mod local_dead_code_elimination;
mod local_value_numbering;

use std::vec;

use bril_rs::{Code, Program};
use clap::ValueEnum;
use common::BasicBlock;
#[derive(ValueEnum, Clone, Debug, PartialEq, Copy)]
pub enum OptimizationPass {
    LocalDeadCodeElimination,
    LocalValueNumbering,
}

pub struct PassManager {
    registered_passes: Vec<Box<dyn Pass>>,
}

impl PassManager {
    fn construct_pass(pass_type: OptimizationPass) -> Box<dyn Pass> {
        match pass_type {
            OptimizationPass::LocalDeadCodeElimination => {
                Box::new(local_dead_code_elimination::LocalDeadCodeEliminationPass::new())
            }
            OptimizationPass::LocalValueNumbering => {
                Box::new(local_value_numbering::LocalValueNumberingPass::new())
            }
        }
    }
    pub fn new() -> Self {
        Self {
            registered_passes: vec![],
        }
    }
    pub fn register_pass(&mut self, pass_type: OptimizationPass) {
        self.registered_passes.push(Self::construct_pass(pass_type));
    }
    pub fn run(&mut self, mut program: Program) -> Program {
        for pass in self.registered_passes.iter_mut() {
            program = pass.apply(program);
        }
        program
    }
}

pub trait Pass {
    fn apply(&mut self, program: Program) -> Program;
}

pub trait LocalScopePass {
    fn apply(&mut self, input_block: BasicBlock) -> BasicBlock;
}

pub fn apply_for_each_block<P>(mut program: bril_rs::Program, pass_manager: &mut P) -> Program
where
    P: LocalScopePass,
{
    program.functions.iter_mut().for_each(|function| {
        // For every function optimze the basic blocks within it.
        function.instrs = common::construct_basic_block_stream(&function.instrs)
            .into_iter() // For every block
            .map(|block| pass_manager.apply(block)) // Optimize this block
            .map(|optimized_block| -> Vec<Code> {
                // Re-form instruction stream from blocks
                let mut instructions: Vec<Code> = vec![];
                if let Some(label_name) = optimized_block.name {
                    instructions.push(Code::Label {
                        label: label_name,
                        pos: None,
                    });
                }
                for instr in optimized_block.instruction_stream.iter() {
                    instructions.push(Code::Instruction(instr.clone()));
                }
                instructions
            })
            .flatten()
            .collect::<Vec<Code>>();
    });
    return program;
}
