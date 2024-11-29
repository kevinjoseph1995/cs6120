use bril_rs::Function;
use std::collections::HashMap;

use crate::BasicBlock;
use smallvec::SmallVec;

struct Node {
    basic_block: BasicBlock,
    name: String,
    // Since the CFG is a DAG the edge direction is from the current node to the successor node.
    successor_indices: SmallVec<[usize; 2]>,
    // The predecessor_indices are the indices of the nodes that have an edge to the current node.
    predecessor_indices: SmallVec<[usize; 2]>,
}

pub struct Cfg {
    nodes: Vec<Node>,
    function_name: String,
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

    pub fn get_post_order(&self) -> Vec<NodeIndex> {
        let mut visited: Vec<bool> = vec![false; self.nodes.len()];
        let mut post_order: Vec<NodeIndex> = Vec::new();
        fn dfs(
            node_index: NodeIndex,
            cfg: &Cfg,
            visited: &mut Vec<bool>,
            post_order: &mut Vec<NodeIndex>,
        ) {
            visited[node_index] = true;
            for successor_index in cfg.nodes[node_index].successor_indices.iter() {
                if !visited[*successor_index] {
                    dfs(*successor_index, cfg, visited, post_order);
                }
            }
            post_order.push(node_index);
        }
        // We make the assumption that the entry node is the first node in the CFG
        for index in 0..self.nodes.len() {
            if !visited[index] {
                dfs(index, self, &mut visited, &mut post_order);
            }
        }
        assert_eq!(post_order.len(), self.nodes.len());
        return post_order;
    }

    pub fn number_of_nodes(&self) -> usize {
        self.nodes.len()
    }

    pub fn get_function_name(&self) -> &str {
        &self.function_name
    }

    pub fn get_basic_block(&self, index: NodeIndex) -> &BasicBlock {
        &self.nodes[index].basic_block
    }

    pub fn get_node_name(&self, index: NodeIndex) -> &str {
        &self.nodes[index].name
    }

    pub fn get_successor_indices(&self, index: NodeIndex) -> &[usize] {
        &self.nodes[index].successor_indices
    }

    pub fn get_predecessor_indices(&self, index: NodeIndex) -> &[usize] {
        &self.nodes[index].predecessor_indices
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
        assert_eq!(cfg.number_of_nodes(), 6);
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

    #[test]
    fn test_post_order() {
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
        let post_order_indices = cfg.get_post_order();
        assert_eq!(post_order_indices.len(), cfg.number_of_nodes());
        assert_eq!(post_order_indices[0], 4);
        assert_eq!(post_order_indices[1], 3);
        assert_eq!(post_order_indices[2], 2);
        assert_eq!(post_order_indices[3], 5);
        assert_eq!(post_order_indices[4], 1);
        assert_eq!(post_order_indices[5], 0);
    }
}
