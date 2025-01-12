pub mod cfg;

use bril_rs::{Code, Instruction, Program};
use brilirs::{basic_block::BBProgram, interp};
use std::{error::Error, fmt::Display};

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub name: Option<String>,
    pub instruction_stream: Vec<Instruction>,
}

pub fn get_program_output(program: Program, input_args: &[String]) -> String {
    let bbprog: BBProgram = program.clone().try_into().expect("Invalid program");
    let mut stdout = Vec::<u8>::new();
    let mut stderr = Vec::<u8>::new();
    let result = interp::execute_main(&bbprog, &mut stdout, input_args, true, &mut stderr);
    if let Some(error) = result.err() {
        eprintln!("{}", error);
        panic!("Program execution failed");
    }

    String::from_utf8(stdout).unwrap()
}

pub fn construct_basic_block_stream<'a>(instructions: &'a [Code]) -> Vec<BasicBlock> {
    let mut current_basic_block_start: usize = 0;
    let mut blocks: Vec<BasicBlock> = Vec::new();
    let mut current_label: Option<&str> = None;

    let extract_instruction = |code: &Code| -> Instruction {
        match code {
            Code::Instruction(instruction) => instruction.clone(),
            _ => panic!("Unexpected label found in code stream"),
        }
    };

    for (index, instruction) in instructions.iter().enumerate() {
        match instruction {
            Code::Label { label, pos: _ } => {
                if index != current_basic_block_start {
                    blocks.push(BasicBlock {
                        name: current_label.map(|s| s.to_string()),
                        instruction_stream: instructions[current_basic_block_start..index]
                            .iter()
                            .map(extract_instruction)
                            .collect(),
                    });
                }

                current_label = Some(label.as_str());
                current_basic_block_start = index + 1;

                continue;
            }
            Code::Instruction(instrctuion) => match instrctuion {
                Instruction::Effect {
                    args: _,
                    funcs: _,
                    labels: _,
                    op,
                    pos: _,
                } => match op {
                    bril_rs::EffectOps::Jump
                    | bril_rs::EffectOps::Branch
                    | bril_rs::EffectOps::Return => {
                        blocks.push(BasicBlock {
                            name: current_label.map(|s| s.to_string()),
                            instruction_stream: instructions[current_basic_block_start..index + 1]
                                .iter()
                                .map(extract_instruction)
                                .collect(),
                        });

                        current_label = None;
                        current_basic_block_start = index + 1;
                    }
                    _ => {
                        continue;
                    }
                },
                _ => {
                    continue;
                }
            },
        };
    }
    if current_basic_block_start < instructions.len() {
        blocks.push(BasicBlock {
            name: current_label.map(|s| s.to_string()),
            instruction_stream: instructions[current_basic_block_start..]
                .iter()
                .map(extract_instruction)
                .collect(),
        });
    }
    return blocks;
}

#[derive(Debug)]
struct ParseError {
    message: String,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ParseError {}", self.message)
    }
}

impl Error for ParseError {}

pub fn parse_bril_text<'a>(bril_text: &'a str) -> Result<Program, Box<dyn Error>> {
    let parser = bril2json::bril_grammar::AbstractProgramParser::new();
    let abstract_program = match parser.parse(
        &bril2json::Lines::new(bril_text, true, true, None),
        bril_text,
    ) {
        Ok(program) => program,
        Err(error) => {
            return Err(Box::new(ParseError {
                message: error.to_string(),
            }));
        }
    };
    let json_string = serde_json::to_string(&abstract_program)?;
    Ok(serde_json::from_str(&json_string)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    const BRIL_PROGRAM_TEXT: &'static str = indoc::indoc! {r#"
        @main(b0: bool, b1: bool) {
            jmp .start;
        .end:
            print x_0_2;
            print x_1_2;
            ret;
        .l_1_3:
            jmp .end;
        .l_1_2:
            x_1_2 : int = const 0;
            jmp .l_1_3;
        .l_1_1:
            x_1_1 : int = const 1;
            jmp .l_1_3;
        .l_0_3:
            br b1 .l_1_1 .l_1_2;
        .l_0_2:
            x_0_2 : int = const 2;
            jmp .l_0_3;
        .l_0_1:
            x_0_1 : int = const 3;
            jmp .l_0_3;
        .start:
            br b0 .l_0_1 .l_0_2;
        }
    "#};

    #[test]
    fn test_basic_block_formation() {
        let program = parse_bril_text(BRIL_PROGRAM_TEXT).unwrap();
        for function in &program.functions {
            let blocks = construct_basic_block_stream(&function.instrs);
            assert!(blocks.len() == 9)
        }
    }
}
