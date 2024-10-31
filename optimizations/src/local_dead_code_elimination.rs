use bril_rs::{Code, Instruction, Program};
use common::BasicBlock;
use smallvec::SmallVec;
use std::collections::HashMap;

use crate::{LocalScopePass, Pass};

pub struct LocalDeadCodeEliminationPass {
    deletion_mask: SmallVec<[bool; 4]>,
}

impl LocalDeadCodeEliminationPass {
    pub fn new() -> Self {
        Self {
            deletion_mask: SmallVec::new(),
        }
    }
}

impl LocalScopePass for LocalDeadCodeEliminationPass {
    fn apply(&mut self, block: BasicBlock) -> BasicBlock {
        let mut instuction_stream = block.instruction_stream;

        loop {
            let mut last_active_store: HashMap<&str, usize> = HashMap::new();
            self.deletion_mask.clear();
            self.deletion_mask.resize(instuction_stream.len(), false);
            let mut atleast_one_deletion = false;

            for (index, instruction) in instuction_stream
                .iter()
                .map(|code| match code {
                    Code::Label { label: _, pos: _ } => panic!("Invalid pre-condition"),
                    Code::Instruction(instruction) => instruction,
                })
                .enumerate()
            {
                let destination = get_store_destination(instruction);
                if destination.is_none() {
                    // Cannot eliminate a dead-store if the current instruction isn't a store :P
                    continue;
                }
                let destination = destination.unwrap();
                let arg_variables = get_load_sources(instruction);
                for arg in arg_variables {
                    // This variable is loaded, remove from the the active store set
                    let _ = last_active_store.remove(arg.as_str());
                }
                if let Some(index) = last_active_store.get(destination) {
                    self.deletion_mask[*index] = true;
                    atleast_one_deletion = true
                }
                last_active_store.insert(destination, index);
            }
            if !atleast_one_deletion {
                break;
            }

            let mut iter = self.deletion_mask.iter();
            instuction_stream.retain(|_| {
                !*(iter.next().expect(
                    "Size of deletion_mask is expected to be the same as instuction_stream",
                ))
            });
        }
        return BasicBlock {
            name: block.name,
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

    use brilirs::{basic_block::BBProgram, interp};

    #[test]
    fn test_local_dead_code_elimination_1() {
        const BRIL_PROGRAM_TEXT: &'static str = indoc::indoc! {r#"
            @main() {
                v0: int = const 1;
                v0: int = const 2;
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
        assert!(program.functions[0].instrs.len() == 4, "{}", program);
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
        assert!(program.functions[0].instrs.len() == 5);
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
        let bbprog: BBProgram = program.try_into().expect("Invalid program");
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        assert!(interp::execute_main(&bbprog, &mut stdout, &[], true, &mut stderr).is_ok());
        assert!(
            String::from_utf8(stdout).unwrap() == "42\n",
            "Error={}",
            String::from_utf8(stderr).unwrap()
        );
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
        assert!(program.functions[0].instrs.len() == 6);
        let bbprog: BBProgram = program.try_into().expect("Invalid program");
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        assert!(interp::execute_main(&bbprog, &mut stdout, &[], true, &mut stderr).is_ok());
        assert!(
            String::from_utf8(stdout).unwrap() == "4\n",
            "Error={}",
            String::from_utf8(stderr).unwrap()
        );
    }
}
