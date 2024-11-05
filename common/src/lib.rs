use bril_rs::{Code, Instruction, Program};
use std::{collections::HashMap, error::Error, fmt::Display};

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub name: Option<String>,
    pub instruction_stream: Vec<Code>,
}

#[derive(Default)]
pub struct Cfg {
    pub adjacency_list_per_vertex: Vec<Vec<usize>>,
    pub underlying_basic_blocks: Vec<BasicBlock>,
}

pub fn construct_basic_block_stream<'a>(instructions: &'a [Code]) -> Vec<BasicBlock> {
    let mut current_basic_block_start: usize = 0;
    let mut blocks: Vec<BasicBlock> = Vec::new();
    let mut current_label: Option<&str> = None;
    for (index, instruction) in instructions.iter().enumerate() {
        match instruction {
            Code::Label { label, pos: _ } => {
                if index != current_basic_block_start {
                    blocks.push(BasicBlock {
                        name: current_label.map(|s| s.to_string()),
                        instruction_stream: instructions[current_basic_block_start..index].to_vec(),
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
                                .to_vec(),
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
            instruction_stream: instructions[current_basic_block_start..].to_vec(),
        });
    }
    return blocks;
}

pub fn construct_cfg<'a>(basic_blocks: &[BasicBlock]) -> Cfg {
    let label_map = {
        // Construct map of label name to index
        let mut label_map: HashMap<&str, usize> = HashMap::new();
        label_map.reserve(basic_blocks.len());
        for (index, block) in (&basic_blocks).iter().enumerate() {
            if let Some(name) = &block.name {
                label_map.insert(name.as_str(), index);
            }
        }
        label_map
    };

    let mut adjacency_list_per_vertex: Vec<Vec<usize>> = Vec::new();
    adjacency_list_per_vertex.reserve(basic_blocks.len());

    for (index, block) in (&basic_blocks).iter().enumerate() {
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
                if index < basic_blocks.len() - 1 {
                    adjacency_list_per_vertex.push(vec![index + 1]);
                }
                continue;
            }
        };
        match effect_instruction_op {
            bril_rs::EffectOps::Return => {
                adjacency_list_per_vertex.push(vec![]);
            }
            bril_rs::EffectOps::Jump => {
                assert!(
                    destination_labels.len() == 1,
                    "Invalid number of destination labels for EffectOps::Jump"
                );
                adjacency_list_per_vertex.push(vec![label_map
                    .get(destination_labels[0].as_str())
                    .unwrap()
                    .clone()])
            }
            bril_rs::EffectOps::Branch => {
                assert!(
                    destination_labels.len() == 2,
                    "Invalid number of destination labels for EffectOps::Branch"
                );
                adjacency_list_per_vertex.push(vec![
                    label_map
                        .get(destination_labels[0].as_str())
                        .unwrap()
                        .clone(),
                    label_map
                        .get(destination_labels[1].as_str())
                        .unwrap()
                        .clone(),
                ])
            }
            _ => {
                adjacency_list_per_vertex.push(Vec::new());
            }
        }
    }
    assert_eq!(basic_blocks.len(), adjacency_list_per_vertex.len());
    Cfg {
        adjacency_list_per_vertex,
        underlying_basic_blocks: basic_blocks.to_vec(),
    }
}

impl<'a> std::fmt::Display for Cfg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (index, children) in self.adjacency_list_per_vertex.iter().enumerate() {
            write!(f, "{:#?}: ", self.underlying_basic_blocks[index].name)?;
            for child_index in children {
                write!(f, "{} ", child_index)?;
            }
            write!(f, "\n")?;
        }
        Ok(())
    }
}

impl Cfg {
    pub fn get_dot_representation(&self) -> String {
        let mut output: String = "digraph{".to_string();
        for (index, block) in self.underlying_basic_blocks.iter().enumerate() {
            let name = match &block.name {
                Some(name) => name.clone(),
                None => format!("label_{}", index),
            };
            output.push_str(&name);
            output.push_str(" [label=\"");
            output.push_str(&name);
            output.push_str("\", shape=box];");
        }
        for (index, children) in self.adjacency_list_per_vertex.iter().enumerate() {
            if !children.is_empty() {
                let parent_name = match &self.underlying_basic_blocks[index].name {
                    Some(name) => name.clone(),
                    None => format!("label_{}", index),
                };
                for child in children {
                    let child_name = match &self.underlying_basic_blocks[*child].name {
                        Some(name) => name.clone(),
                        None => format!("label_{}", *child),
                    };
                    output.push_str(&parent_name);
                    output.push_str(" -> ");
                    output.push_str(&child_name);
                    output.push(';');
                }
            }
        }
        output.push('}');
        return output;
    }
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
    fn test_block_map_formation() {
        let program = parse_bril_text(BRIL_PROGRAM_TEXT).unwrap();
        for function in &program.functions {
            let blocks = construct_basic_block_stream(&function.instrs);
            println!("{:#?}", blocks);
        }
    }

    #[test]
    fn test_cfg_construction() {
        let program = parse_bril_text(BRIL_PROGRAM_TEXT).unwrap();
        for function in &program.functions {
            let basic_blocks = construct_basic_block_stream(&function.instrs);
            let cfg = construct_cfg(&basic_blocks);
            println!("{}", cfg.get_dot_representation());
        }
    }

    #[test]
    fn test_cfg_construction2() {
        let program_text = indoc::indoc! {r#"
            # ARGS: 23
            @main(n: float) {
                v0: float = id n;
                c: float = call @probability v0;
                c: float = id c;
                v1: float = id c;
                print v1;
                v2: int = const 0;
            }
            @probability(n: float): float {
                v0: float = const 1;
                prob: float = id v0;
                v2: float = const 1;
                i: float = id v2;
                .for.cond.1:
                v3: float = id i;
                v4: float = id n;
                v5: bool = flt v3 v4;
                br v5 .for.body.1 .for.end.1;
                .for.body.1:
                v6: float = const 365;
                v7: float = id i;
                v8: float = fsub v6 v7;
                log: float = id v8;
                v9: float = id log;
                v10: float = const 365;
                v11: float = fdiv v9 v10;
                logUpdated: float = id v11;
                v12: float = id prob;
                v13: float = id logUpdated;
                v14: float = fmul v12 v13;
                prob: float = id v14;
                v15: float = id i;
                v16: float = const 1;
                v17: float = fadd v15 v16;
                i: float = id v17;
                jmp .for.cond.1;
                .for.end.1:
                v18: float = const 1;
                v19: float = id prob;
                v20: float = const 100;
                v21: float = fmul v19 v20;
                v22: float = const 100;
                v23: float = fdiv v21 v22;
                v24: float = fsub v18 v23;
                ret v24;
            }
    "#};
        let program = parse_bril_text(program_text).unwrap();
        for function in &program.functions {
            let basic_blocks = construct_basic_block_stream(&function.instrs);
            let cfg = construct_cfg(&basic_blocks);
            println!("{}", cfg.get_dot_representation());
        }
    }
}
