use bril_rs::{Code, Instruction, Program};
use common::BasicBlock;
use std::collections::HashMap;

use crate::{LocalScopePass, Pass};

pub struct LocalDeadCodeEliminationPass {
    instruction_stream_workspace: Vec<Code>,
}

impl LocalDeadCodeEliminationPass {
    pub fn new() -> Self {
        Self {
            instruction_stream_workspace: Vec::new(),
        }
    }
}

impl LocalScopePass for LocalDeadCodeEliminationPass {
    fn apply(&mut self, block: BasicBlock) -> BasicBlock {
        let mut instuction_stream = block.instruction_stream;
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
            {
                // Perform the actual deletion of instructions
                self.instruction_stream_workspace.clear();
                self.instruction_stream_workspace
                    .reserve(instuction_stream.len());
                for (index, instr) in instuction_stream.iter().enumerate() {
                    if !deletion_mask[index] {
                        self.instruction_stream_workspace.push(instr.clone());
                    }
                }
                std::mem::swap(
                    &mut instuction_stream,
                    &mut self.instruction_stream_workspace,
                );
            }
        }
        return BasicBlock {
            name: block.name.clone(),
            instruction_stream: instuction_stream,
        };
    }
}

impl Pass for LocalDeadCodeEliminationPass {
    fn apply(&mut self, program: bril_rs::Program) -> Program {
        crate::apply_for_each_block(program, self)
    }
}

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
        let program = program.unwrap();
        let mut manager = LocalDeadCodeEliminationPass::new();
        let program = Pass::apply(&mut manager, program);
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
        let program = program.unwrap();
        let mut manager = LocalDeadCodeEliminationPass::new();
        let program = Pass::apply(&mut manager, program);
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
        let program = program.unwrap();
        let mut manager = LocalDeadCodeEliminationPass::new();
        let program = Pass::apply(&mut manager, program);
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
        let program = program.unwrap();
        let mut manager = LocalDeadCodeEliminationPass::new();
        let program = Pass::apply(&mut manager, program);
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
