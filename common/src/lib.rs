use std::{collections::HashMap, fmt::Debug};

use bril_rs::{Code, Instruction};
use smallvec::SmallVec;

#[derive(Debug)]
pub struct BasicBlock<'a> {
    name: String,
    instruction_stream: &'a [Code],
}

#[derive(Default)]
pub struct Cfg<'a> {
    adjacency_list_per_vertex: Vec<SmallVec<[usize; 4]>>,
    underlying_basic_blocks: &'a [BasicBlock<'a>],
}

fn construct_cfg<'a>(basic_blocks: &'a [BasicBlock<'a>]) -> Option<Cfg<'a>> {
    if basic_blocks.is_empty() {
        return None;
    }
    let label_map = {
        // Construct map of label name to index
        let mut label_map: HashMap<&str, usize> = HashMap::new();
        label_map.reserve(basic_blocks.len());
        for (index, block) in (&basic_blocks).iter().enumerate() {
            label_map.insert(&block.name, index);
        }
        label_map
    };

    let mut adjacency_list_per_vertex: Vec<SmallVec<[usize; 4]>> = Vec::new();
    adjacency_list_per_vertex.reserve(basic_blocks.len());

    for block in (&basic_blocks).iter() {
        let last_instruction_in_block = {
            match block
                .instruction_stream
                .last()
                .expect("Expected non-empty stream of basic blocks")
            {
                Code::Label { label: _, pos: _ } => {
                    panic!("Unexpected label in basic block");
                }
                Code::Instruction(instruction) => instruction,
            }
        };
        let (effect_instruction_op, destination_labels) = match last_instruction_in_block {
            Instruction::Effect {
                args: _,
                funcs: _,
                labels,
                op,
                pos: _,
            } => (op, labels),
            _ => {
                adjacency_list_per_vertex.push(SmallVec::new());
                continue;
            }
        };
        match effect_instruction_op {
            bril_rs::EffectOps::Jump => {
                assert!(
                    destination_labels.len() == 1,
                    "Invalid number of destination labels for EffectOps::Jump"
                );
                adjacency_list_per_vertex.push(smallvec::smallvec![label_map
                    .get(destination_labels[0].as_str())
                    .unwrap()
                    .clone()])
            }
            bril_rs::EffectOps::Branch => {
                assert!(
                    destination_labels.len() == 2,
                    "Invalid number of destination labels for EffectOps::Branch"
                );
                adjacency_list_per_vertex.push(smallvec::smallvec![
                    label_map
                        .get(destination_labels[0].as_str())
                        .unwrap()
                        .clone(),
                    label_map
                        .get(destination_labels[1].as_str())
                        .unwrap()
                        .clone()
                ])
            }
            _ => {
                adjacency_list_per_vertex.push(SmallVec::new());
            }
        }
    }
    assert_eq!(basic_blocks.len(), adjacency_list_per_vertex.len());
    Some(Cfg {
        adjacency_list_per_vertex,
        underlying_basic_blocks: basic_blocks,
    })
}

impl<'a> std::fmt::Display for Cfg<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (index, children) in self.adjacency_list_per_vertex.iter().enumerate() {
            write!(f, "{}: ", self.underlying_basic_blocks[index].name)?;
            for child_index in children {
                write!(f, "{} ", child_index)?;
            }
            write!(f, "\n")?;
        }
        Ok(())
    }
}

fn construct_basic_block_stream<'a>(instructions: &'a [Code]) -> Vec<BasicBlock<'a>> {
    let mut current_basic_block_start: usize = 0;
    let mut blocks: Vec<BasicBlock<'a>> = Vec::new();
    let get_current_label = |index: usize, current_label: Option<&str>| -> String {
        if let Some(l) = current_label {
            l.to_string()
        } else {
            format!("label_{}", index)
        }
    };
    let mut current_label: Option<&str> = None;
    for (index, instruction) in instructions.iter().enumerate() {
        match instruction {
            Code::Label { label, pos: _ } => {
                blocks.push(BasicBlock {
                    name: get_current_label(index, current_label.clone()),
                    instruction_stream: &instructions[current_basic_block_start..index],
                });

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
                            name: get_current_label(index, current_label.clone()),
                            instruction_stream: &instructions[current_basic_block_start..index + 1],
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
            name: get_current_label(current_basic_block_start, current_label.clone()),
            instruction_stream: &instructions[current_basic_block_start..],
        });
    }
    return blocks;
}

#[cfg(test)]
mod tests {
    use super::*;
    use bril_rs::Program;
    use indoc::indoc;

    const BRIL_PROGRAM_TEXT: &'static str = indoc! {r#"
        @main {
            v: int = const 4;
            jmp .somewhere;
            v: int = const 2;
        .somewhere:
            print v;
        }"#};

    fn get_test_program() -> Program {
        let parser = bril2json::bril_grammar::AbstractProgramParser::new();
        let abstract_program = parser
            .parse(
                &bril2json::Lines::new(BRIL_PROGRAM_TEXT, true, true, None),
                BRIL_PROGRAM_TEXT,
            )
            .unwrap();
        let json_string =
            serde_json::to_string(&abstract_program).expect("Failed to serialized to JSON string");
        return serde_json::from_str(&json_string)
            .expect("Failed to parse JSON string to a Brill Program");
    }

    #[test]
    fn test_block_map_formation() {
        let program = get_test_program();
        for function in &program.functions {
            let _ = construct_basic_block_stream(&function.instrs);
        }
    }

    #[test]
    fn test_cfg_construction() {
        let program = get_test_program();
        for function in &program.functions {
            let basic_blocks = construct_basic_block_stream(&function.instrs);
            let cfg = construct_cfg(&basic_blocks);
            assert!(cfg.is_some());
        }
    }
}
