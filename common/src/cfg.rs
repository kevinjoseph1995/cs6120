use bril_rs::Function;
use std::collections::HashMap;

use crate::BasicBlock;
use smallvec::SmallVec;

struct Node {
    basic_block: BasicBlock,
    name: String,
    successor_indices: SmallVec<[usize; 2]>,
    predecessor_indices: SmallVec<[usize; 2]>,
}

pub struct Cfg {
    nodes: Vec<Node>,
    function_name: String,
}

pub struct CfgIterator<'a> {
    cfg: &'a Cfg,
    node_indices: &'a [usize],
    current_index: usize,
}

impl<'a> Iterator for &'a mut CfgIterator<'a> {
    type Item = &'a BasicBlock;

    fn next(&mut self) -> Option<Self::Item> {
        let current_index = self.current_index;
        self.current_index = self.current_index + 1;
        if current_index == self.node_indices.len() {
            None
        } else {
            Some(self.cfg.get_basic_block(self.node_indices[current_index]))
        }
    }
}

pub type NodeIndex = usize;

impl Cfg {
    pub fn new(function: &Function) -> Self {
        // 1st Pass
        // Extract the CFG nodes and the label map(label_name->index)
        // The CFG nodes still do not have the edge relations but simply contain the associated basic block
        let (mut nodes, label_map) = {
            let basic_blocks = crate::construct_basic_block_stream(&function.instrs);
            // Map of label to node index
            let mut nodes: Vec<Node> = Vec::new();
            let mut label_map: HashMap<String, usize> = HashMap::with_capacity(basic_blocks.len());
            basic_blocks
                .into_iter()
                .enumerate()
                .for_each(|(index, block)| {
                    let node_name = {
                        if let Some(label_name) = &block.name {
                            label_name.clone()
                        } else {
                            format!("label_{}", index)
                        }
                    };
                    // Insert into Label_Name->Index map
                    label_map.insert(node_name.clone(), index);
                    // Create a new node entry
                    nodes.push(Node {
                        basic_block: block,
                        name: node_name,
                        successor_indices: SmallVec::new(),
                        predecessor_indices: SmallVec::new(),
                    });
                });
            (nodes, label_map)
        };

        // 2nd Pass
        // Fixup the edge relations
        for index in 0..nodes.len() {
            let last_instr = nodes[index]
                .basic_block
                .instruction_stream
                .last()
                .expect("Expected at least 1 instruction");
            let (effect_instr, dst_labels) = match last_instr {
                bril_rs::Instruction::Effect {
                    args: _,
                    funcs: _,
                    labels,
                    op,
                    pos: _,
                } => (op, labels),
                _ => {
                    if index < (nodes.len() - 1) {
                        // Add an edge to the next basic block which the current block will fall-through from.
                        nodes[index].successor_indices.push(index + 1);
                        nodes[index + 1].predecessor_indices.push(index);
                    }
                    continue;
                }
            };
            match effect_instr {
                bril_rs::EffectOps::Jump => {
                    assert_eq!(dst_labels.len(), 1);
                    let successor_index = *label_map
                        .get(&dst_labels[0])
                        .expect(format!("Did not find label {} in map", dst_labels[0]).as_str());
                    nodes[index].successor_indices.push(successor_index);
                    nodes[successor_index].predecessor_indices.push(index);
                }
                bril_rs::EffectOps::Branch => {
                    assert_eq!(dst_labels.len(), 2);
                    let successor_index1 = *label_map
                        .get(&dst_labels[0])
                        .expect(format!("Did not find label {} in map", dst_labels[0]).as_str());
                    let successor_index2 = *label_map
                        .get(&dst_labels[1])
                        .expect(format!("Did not find label {} in map", dst_labels[0]).as_str());
                    nodes[index]
                        .successor_indices
                        .extend_from_slice(&[successor_index1, successor_index2]);
                    nodes[successor_index1].predecessor_indices.push(index);
                    nodes[successor_index2].predecessor_indices.push(index);
                }
                bril_rs::EffectOps::Return => {
                    // Do not add an edge to the next basic block as control transfers to the caller
                }
                _ => {
                    if index < (nodes.len() - 1) {
                        nodes[index].successor_indices.push(index + 1);
                        nodes[index + 1].predecessor_indices.push(index);
                    }
                }
            }
        }
        Cfg {
            nodes,
            function_name: function.name.clone(),
        }
    }

    pub fn number_of_nodes(&self) -> usize {
        self.nodes.len()
    }

    pub fn get_basic_block(&self, index: NodeIndex) -> &BasicBlock {
        &self.nodes[index].basic_block
    }

    pub fn get_node_name(&self, index: NodeIndex) -> &str {
        &self.nodes[index].name
    }

    pub fn get_successor_iterator(&self, index: NodeIndex) -> CfgIterator {
        CfgIterator {
            cfg: self,
            node_indices: &self.nodes[index].successor_indices,
            current_index: 0,
        }
    }

    pub fn get_predecessor_iterator(&self, index: NodeIndex) -> CfgIterator {
        CfgIterator {
            cfg: self,
            node_indices: &self.nodes[index].predecessor_indices,
            current_index: 0,
        }
    }
}

pub fn get_dot_representation(cfg: &Cfg) -> String {
    let total_number_of_nodes = cfg.number_of_nodes();
    let mut statements: Vec<String> = Vec::new();
    // Add node statements
    for index in 0..total_number_of_nodes {
        let node_name = cfg.get_node_name(index);
        let mut node_text = String::new();
        for instr in cfg.get_basic_block(index).instruction_stream.iter() {
            node_text.push_str(&format!("{}\\n", instr));
        }
        statements.push(format!(
            "\"{node_name}\" [shape=record, label=\"{node_name} | {node_text}\"]",
        ));
        // Add more information for each node
    }
    // Add edge statements
    for index in 0..total_number_of_nodes {
        let node_name = cfg.get_node_name(index);
        for successor_index in cfg.nodes[index].successor_indices.iter() {
            let successor_name = cfg.get_node_name(*successor_index);
            statements.push(format!("\"{}\" -> \"{}\"", node_name, successor_name));
        }
    }
    format!("digraph{{\n{}\n}}", statements.join(";\n"))
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::*;

    #[test]
    fn test_cfg_construction() {
        let program = crate::parse_bril_text(indoc! {"
            @main {
            .entry:
              x: int = const 0;
              i: int = const 0;
              one: int = const 1;

            .loop:
              max: int = const 10;
              cond: bool = lt i max;
              br cond .body .exit;

            .body:
              mid: int = const 5;
              cond: bool = lt i mid;
              br cond .then .endif;

            .then:
              x: int = add x one;
              jmp .endif;

            .endif:
              factor: int = const 2;
              x: int = mul x factor;

              i: int = add i one;
              jmp .loop;

            .exit:
              print x;
            }
            "})
        .unwrap();
        let cfg = Cfg::new(&program.functions[0]);
        println!("{}", get_dot_representation(&cfg));
        for index in 0..cfg.number_of_nodes() {
            if cfg.get_node_name(index) == ".loop" {
                assert_eq!(cfg.nodes[index].successor_indices.len(), 2);
                assert_eq!(cfg.nodes[index].predecessor_indices.len(), 1);
            } else if cfg.get_node_name(index) == ".body" {
                assert_eq!(cfg.nodes[index].successor_indices.len(), 2);
                assert_eq!(cfg.nodes[index].predecessor_indices.len(), 1);
            } else if cfg.get_node_name(index) == ".then" {
                assert_eq!(cfg.nodes[index].successor_indices.len(), 1);
                assert_eq!(cfg.nodes[index].predecessor_indices.len(), 1);
            } else if cfg.get_node_name(index) == ".endif" {
                assert_eq!(cfg.nodes[index].successor_indices.len(), 1);
                assert_eq!(cfg.nodes[index].predecessor_indices.len(), 2);
            } else if cfg.get_node_name(index) == ".exit" {
                assert_eq!(cfg.nodes[index].successor_indices.len(), 0);
                assert_eq!(cfg.nodes[index].predecessor_indices.len(), 1);
            } else if cfg.get_node_name(index) == ".entry" {
                assert_eq!(cfg.nodes[index].successor_indices.len(), 1);
                assert_eq!(cfg.nodes[index].predecessor_indices.len(), 0);
            }
        }
    }
}
