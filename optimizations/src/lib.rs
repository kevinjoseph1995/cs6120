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

mod local_dead_code_elimination {

    use super::*;
    use bril_rs::{Code, Instruction};
    use common::BasicBlock;
    use std::collections::HashMap;

    fn get_load_sources(instruction: &Instruction) -> &[String] {
        match instruction {
            bril_rs::Instruction::Value {
                args,
                dest: _,
                funcs: _,
                labels: _,
                op: _,
                pos: _,
                op_type: _,
            } => args.as_slice(),
            bril_rs::Instruction::Effect {
                args,
                funcs: _,
                labels: _,
                op: _,
                pos: _,
            } => args.as_slice(),
            _ => &[],
        }
    }

    fn get_store_destination(instruction: &Instruction) -> Option<&str> {
        match &instruction {
            bril_rs::Instruction::Constant {
                dest,
                op: _,
                pos: _,
                const_type: _,
                value: _,
            } => Some(dest.as_str()),
            bril_rs::Instruction::Value {
                args: _,
                dest,
                funcs: _,
                labels: _,
                op: _,
                pos: _,
                op_type: _,
            } => Some(dest.as_str()),
            bril_rs::Instruction::Effect {
                args: _,
                funcs: _,
                labels: _,
                op: _,
                pos: _,
            } => None,
        }
    }

    fn process_instructions_in_block(block: &BasicBlock) -> BasicBlock {
        let mut instuction_stream = block.instruction_stream.clone();
        loop {
            // Iterate in a loop till convergence
            // We need to find all the dead stores
            let mut last_defined = HashMap::<&str, usize>::new();
            let mut deletion_mask = Vec::<bool>::new();
            deletion_mask.resize(instuction_stream.len(), false);
            let mut atleast_one_marked_for_deleteion = false;

            for index in 0..instuction_stream.len() {
                let instruction = match &instuction_stream[index] {
                    Code::Label { label: _, pos: _ } => panic!("Invalid pre-condition"),
                    Code::Instruction(instruction) => instruction,
                };
                // Check for loads
                for variable_loaded in get_load_sources(&instruction) {
                    let _ = last_defined.remove(variable_loaded.as_str());
                }
                // Check for stores
                let variable_stored = get_store_destination(&instruction);
                if variable_stored.is_some() {
                    match last_defined.get(variable_stored.unwrap()) {
                        Some(dead_store_index) => {
                            deletion_mask[*dead_store_index] = true;
                            atleast_one_marked_for_deleteion = true;
                        } // Mark for deletion,
                        None => {}
                    }
                    last_defined.insert(variable_stored.unwrap(), index);
                }
            }
            // Iterate through all the stores that were not read from
            for (_label, index) in last_defined {
                deletion_mask[index] = true;
                atleast_one_marked_for_deleteion = true;
            }
            if !atleast_one_marked_for_deleteion {
                // We have converged. No more dead stores in this local block
                break;
            }
            instuction_stream = {
                let mut new_instruction_stream = Vec::<Code>::new();
                new_instruction_stream.reserve(instuction_stream.len());
                for (index, instr) in instuction_stream.iter().enumerate() {
                    if !deletion_mask[index] {
                        new_instruction_stream.push(instr.clone());
                    }
                }
                new_instruction_stream
            };
        }
        return BasicBlock {
            name: block.name.clone(),
            instruction_stream: instuction_stream,
        };
    }

    pub fn apply(program: &mut Program) {
        program.functions.iter_mut().for_each(|function| {
            // For every function optimze the basic blocks within it.
            function.instrs = common::construct_basic_block_stream(&function.instrs)
                .iter_mut() // For every block
                .map(|block| process_instructions_in_block(block)) // Optimize this block
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
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_local_dead_code_elimination_1() {
        const BRIL_PROGRAM_TEXT: &'static str = indoc::indoc! {r#"
            @main() {
                v0: int = const 1;
                v1: int = const 2;
                v3: int = const 3;
                v2: int = add v0 v1;
            }
        "#};
        let program = common::parse_bril_text(&BRIL_PROGRAM_TEXT);
        assert!(program.is_ok());
        let mut program = program.unwrap();
        OptimizationPass::LocalDeadCodeElimination.apply(&mut program);
        assert!(program.functions[0].instrs.is_empty());
    }
    #[test]
    fn test_local_dead_code_elimination_2() {
        const BRIL_PROGRAM_TEXT: &'static str = indoc::indoc! {r#"
            @main() {
                v0: int = const 1;
                v1: int = const 2;
                v3: int = const 3;
                v2: int = add v0 v1;
                ret v2;
            }
        "#};
        let program = common::parse_bril_text(&BRIL_PROGRAM_TEXT);
        assert!(program.is_ok());
        let mut program = program.unwrap();
        OptimizationPass::LocalDeadCodeElimination.apply(&mut program);
        assert!(program.functions[0].instrs.len() == 4); // "v3: int = const 3;" is a dead store and will get deleted
    }

    #[test]
    fn test_local_dead_code_elimination_3() {
        const BRIL_PROGRAM_TEXT: &'static str = indoc::indoc! {r#"
            @main {
            a: int = const 100;
            a: int = const 42;
            print a;
            }
        "#};
        let program = common::parse_bril_text(&BRIL_PROGRAM_TEXT);
        assert!(program.is_ok());
        let mut program = program.unwrap();
        OptimizationPass::LocalDeadCodeElimination.apply(&mut program);
        assert!(program.functions[0].instrs.len() == 2); // "a: int = const 100"; is a dead store and will get deleted
    }

    #[test]
    fn test_local_dead_code_elimination_4() {
        const BRIL_PROGRAM_TEXT: &'static str = indoc::indoc! {r#"
            @main {
                a: int = const 4;
                b: int = const 2;
                jmp .end;
                print b;
                .end:
                print a;
            }
        "#};
        let program = common::parse_bril_text(&BRIL_PROGRAM_TEXT);
        assert!(program.is_ok());
        let mut program = program.unwrap();
        OptimizationPass::LocalDeadCodeElimination.apply(&mut program);
        /*
        Output program:
        @main {
            jmp .end;
            print b;
            .end:
            print a;
        }
        */
        assert!(program.functions[0].instrs.len() == 4);
    }
}
