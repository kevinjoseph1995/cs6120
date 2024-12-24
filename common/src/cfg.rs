pub mod ssa;

use bril_rs::Function;
use std::{
    collections::{HashMap, HashSet},
    vec,
};

use crate::BasicBlock;
use smallvec::SmallVec;

pub trait NodeEntry {
    fn get_textual_representation(&self) -> String {
        String::new()
    }
}

#[derive(Debug, Clone)]
struct Node<Data: NodeEntry> {
    data: Data,
    name: String,
    // Since the CFG is a DAG the edge direction is from the current node to the successor node.
    successor_indices: SmallVec<[usize; 2]>,
    // The predecessor_indices are the indices of the nodes that have an edge to the current node.
    predecessor_indices: SmallVec<[usize; 2]>,
}

#[derive(Debug, Clone)]
pub struct DirectedGraph<Data: NodeEntry> {
    nodes: Vec<Node<Data>>,
}

#[derive(Debug, Clone)]
pub struct Cfg {
    pub dag: DirectedGraph<BasicBlock>,
    pub function_name: String,
}

impl NodeEntry for BasicBlock {
    fn get_textual_representation(&self) -> String {
        let mut text = String::new();
        for instr in self.instruction_stream.iter() {
            text.push_str(&format!("{}\\n", instr));
        }
        text
    }
}

pub struct Dominators<'a> {
    cfg: &'a Cfg,
    // The dominator set for each node
    pub set_per_node: Vec<HashSet<NodeIndex>>,
}

pub struct DominanceFrontiers<'a> {
    _dominators: &'a Dominators<'a>,
    // The dominance frontier set for each node
    pub set_per_node: Vec<HashSet<NodeIndex>>,
}

pub type NodeIndex = usize;

impl<Data: NodeEntry> DirectedGraph<Data> {
    pub fn number_of_nodes(&self) -> usize {
        self.nodes.len()
    }
    pub fn get_post_order(&self) -> Vec<NodeIndex> {
        let mut visited: Vec<bool> = vec![false; self.nodes.len()];
        let mut post_order: Vec<NodeIndex> = Vec::new();
        fn dfs<Data: NodeEntry>(
            node_index: NodeIndex,
            dag: &DirectedGraph<Data>,
            visited: &mut Vec<bool>,
            post_order: &mut Vec<NodeIndex>,
        ) {
            visited[node_index] = true;
            for successor_index in dag.nodes[node_index].successor_indices.iter() {
                if !visited[*successor_index] {
                    dfs(*successor_index, dag, visited, post_order);
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
    pub fn get_node_name(&self, index: NodeIndex) -> &str {
        &self.nodes[index].name
    }

    pub fn get_successor_indices(&self, index: NodeIndex) -> &[usize] {
        &self.nodes[index].successor_indices
    }

    pub fn get_predecessor_indices(&self, index: NodeIndex) -> &[usize] {
        &self.nodes[index].predecessor_indices
    }
    pub fn get_dot_representation(&self) -> String {
        let total_number_of_nodes = self.number_of_nodes();
        let mut statements: Vec<String> = Vec::new();
        // Add node statements
        for index in 0..total_number_of_nodes {
            let node_name = self.get_node_name(index);
            let node_text = self.nodes[index].data.get_textual_representation();
            statements.push(format!(
                "\"{node_name}\" [shape=record, label=\"{node_name} | {node_text}\"]",
            ));
            // Add more information for each node
        }
        // Add edge statements
        for index in 0..total_number_of_nodes {
            let node_name = self.get_node_name(index);
            for successor_index in self.nodes[index].successor_indices.iter() {
                let successor_name = self.get_node_name(*successor_index);
                statements.push(format!("\"{}\" -> \"{}\"", node_name, successor_name));
            }
        }
        format!("digraph{{\n{}\n}}", statements.join(";\n"))
    }
}

impl Cfg {
    pub fn new(function: &Function) -> Self {
        // 1st Pass
        // Extract the CFG nodes and the label map(label_name->index)
        // The CFG nodes still do not have the edge relations but simply contain the associated basic block
        let (mut nodes, label_map) = {
            let basic_blocks = crate::construct_basic_block_stream(&function.instrs);
            // Map of label to node index
            let mut nodes: Vec<Node<BasicBlock>> = Vec::new();
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
                        data: block,
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
                .data
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
            dag: DirectedGraph { nodes },
            function_name: function.name.clone(),
        }
    }

    pub fn get_basic_block(&self, index: NodeIndex) -> &BasicBlock {
        &self.dag.nodes[index].data
    }
    pub fn get_basic_block_mut(&mut self, index: NodeIndex) -> &mut BasicBlock {
        &mut self.dag.nodes.get_mut(index).unwrap().data
    }
}

impl<'a> Dominators<'a> {
    pub fn new(cfg: &'a Cfg) -> Self {
        let mut dominators: Vec<HashSet<NodeIndex>> =
            vec![HashSet::new(); cfg.dag.number_of_nodes()];
        // The entry node is the only node that dominates itself
        dominators[0].insert(0);
        // Initialize the dominator sets
        // The dominator set of each node is the set of all nodes in the CFG
        for index in 1..cfg.dag.number_of_nodes() {
            dominators[index].extend(0..cfg.dag.number_of_nodes());
        }
        // We use post order traversal to compute the dominator sets
        let post_order_node_indices = cfg.dag.get_post_order();
        loop {
            let mut changed = false;
            for node_index in post_order_node_indices.iter().rev() {
                if *node_index == 0 {
                    // The entry node is the only node that dominates itself
                    continue;
                }
                let current_node_dominator_set_size = dominators[*node_index].len();
                // Dom(n) = {n} union with intersection over Dom(p) for all p in pred(n)
                dominators[*node_index] = HashSet::new();
                dominators[*node_index].insert(*node_index);
                let predecessor_indices = cfg.dag.get_predecessor_indices(*node_index);
                // Intersect the dominator sets of the predecessors
                // If there is only one predecessor then the dominator set of the current node is the predecessor itself
                if !predecessor_indices.is_empty() {
                    let mut intersection: HashSet<NodeIndex> =
                        dominators[predecessor_indices[0]].clone();
                    for predecessor_index in predecessor_indices.iter().skip(1) {
                        let predecesor_dominator_set = &dominators[*predecessor_index];
                        intersection = intersection
                            .intersection(predecesor_dominator_set)
                            .copied()
                            .collect();
                    }
                    dominators[*node_index].extend(intersection);
                }
                // If the size of the dominator set has changed then we need to recompute the dominator set
                if dominators[*node_index].len() != current_node_dominator_set_size {
                    changed = true;
                }
            }
            // If no changes were made then we have reached a fixed point
            if !changed {
                break;
            }
        }
        Dominators {
            cfg,
            set_per_node: dominators,
        }
    }

    pub fn build_dom_tree(&self) -> DirectedGraph<BasicBlock> {
        let mut nodes = self.cfg.dag.nodes.clone();
        for node_index in 0..nodes.len() {
            nodes[node_index].predecessor_indices.clear();
            nodes[node_index].successor_indices.clear();
        }
        for node_index in 0..nodes.len() {
            let mut current_dominator_set = self.set_per_node[node_index].clone();
            current_dominator_set.remove(&node_index); // Remove trivial dominators
            let mut nodes_to_exclude: HashSet<usize> = HashSet::new();
            for dominator in &current_dominator_set {
                let mut other_dominators = self.set_per_node[*dominator].clone();
                other_dominators.remove(&dominator); // Remove trivial dominators
                for node_to_exclude in current_dominator_set.intersection(&other_dominators) {
                    nodes_to_exclude.insert(*node_to_exclude);
                }
            }
            for node in current_dominator_set.difference(&nodes_to_exclude) {
                nodes[*node].successor_indices.push(node_index);
                nodes[node_index].predecessor_indices.push(*node);
            }
        }
        DirectedGraph { nodes }
    }

    pub fn build_dom_frontiers(&self) -> DominanceFrontiers {
        // This implementation is based on the paper "A Simple, Fast Dominance Algorithm" by Cooper et al.
        // The details were explained in the following Youtube video: https://www.youtube.com/watch?v=q3YexEYB_ko
        let cfg = self.cfg;
        let dominator_tree = self.build_dom_tree(); // The dominator tree is the immediate dominator tree

        // The dominance frontier of a node n is the set of nodes where n is not a strict-dominator but has a predecessor that is a dominator
        let mut dominance_frontiers: Vec<HashSet<NodeIndex>> =
            vec![HashSet::new(); cfg.dag.number_of_nodes()]; // DF(X) = ∅

        // Post order traversal of the dominator tree
        for node_index in dominator_tree.get_post_order() {
            // Compute DF_local(X)
            //         DF_local(X) = {Y ∈ succ(X) | idom(Y) ≠ X}
            // In other words the local dominance frontier of a node X is the set of all successors of X where X is not the immediate dominator of Y
            for succsessor_index in cfg.dag.get_successor_indices(node_index) {
                // If X is not the immediate dominator of Y
                if !dominator_tree
                    .get_successor_indices(node_index)
                    .contains(succsessor_index)
                {
                    dominance_frontiers[node_index].insert(*succsessor_index);
                }
            }
            // For each child(Z) of X(in the dominator tree)
            //         For each Y ∈ DF(Z)
            //             If idom(Y) ≠ X; then DF(X) = DF(X) ∪ {Y}
            for child in dominator_tree.get_successor_indices(node_index) {
                let mut dominator_up: Vec<usize> = Vec::new();
                for y in dominance_frontiers[*child].iter() {
                    if !dominator_tree.get_successor_indices(node_index).contains(y) {
                        dominator_up.push(*y);
                    }
                }
                dominance_frontiers[node_index].extend(dominator_up);
            }
        }
        DominanceFrontiers {
            _dominators: self,
            set_per_node: dominance_frontiers,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bril_rs::Program;
    use indoc::indoc;
    use std::sync::LazyLock;

    static PROGRAM: LazyLock<Program> = LazyLock::new(|| {
        crate::parse_bril_text(indoc! {"
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
        .unwrap()
    });

    #[test]
    fn test_cfg_construction() {
        let cfg = Cfg::new(&PROGRAM.functions[0]);
        assert_eq!(cfg.dag.number_of_nodes(), 6);
        for index in 0..cfg.dag.number_of_nodes() {
            if cfg.dag.get_node_name(index) == ".loop" {
                assert_eq!(cfg.dag.nodes[index].successor_indices.len(), 2);
                assert_eq!(cfg.dag.nodes[index].predecessor_indices.len(), 1);
            } else if cfg.dag.get_node_name(index) == ".body" {
                assert_eq!(cfg.dag.nodes[index].successor_indices.len(), 2);
                assert_eq!(cfg.dag.nodes[index].predecessor_indices.len(), 1);
            } else if cfg.dag.get_node_name(index) == ".then" {
                assert_eq!(cfg.dag.nodes[index].successor_indices.len(), 1);
                assert_eq!(cfg.dag.nodes[index].predecessor_indices.len(), 1);
            } else if cfg.dag.get_node_name(index) == ".endif" {
                assert_eq!(cfg.dag.nodes[index].successor_indices.len(), 1);
                assert_eq!(cfg.dag.nodes[index].predecessor_indices.len(), 2);
            } else if cfg.dag.get_node_name(index) == ".exit" {
                assert_eq!(cfg.dag.nodes[index].successor_indices.len(), 0);
                assert_eq!(cfg.dag.nodes[index].predecessor_indices.len(), 1);
            } else if cfg.dag.get_node_name(index) == ".entry" {
                assert_eq!(cfg.dag.nodes[index].successor_indices.len(), 1);
                assert_eq!(cfg.dag.nodes[index].predecessor_indices.len(), 0);
            }
        }
    }

    #[test]
    fn test_post_order() {
        let cfg = Cfg::new(&PROGRAM.functions[0]);
        let post_order_indices = cfg.dag.get_post_order();
        assert_eq!(post_order_indices.len(), cfg.dag.number_of_nodes());
        assert_eq!(post_order_indices[0], 4);
        assert_eq!(post_order_indices[1], 3);
        assert_eq!(post_order_indices[2], 2);
        assert_eq!(post_order_indices[3], 5);
        assert_eq!(post_order_indices[4], 1);
        assert_eq!(post_order_indices[5], 0);
    }

    #[test]
    fn test_dominators() {
        let cfg = Cfg::new(&PROGRAM.functions[0]);
        let dominators = Dominators::new(&cfg);
        for node in 0..cfg.dag.number_of_nodes() {
            let node_dominators = &dominators.set_per_node[node];
            if cfg.dag.get_node_name(node) == "entry" {
                assert_eq!(node_dominators.len(), 1);
                assert!(node_dominators.contains(&0));
            } else if cfg.dag.get_node_name(node) == "loop" {
                assert_eq!(node_dominators.len(), 2);
                assert!(node_dominators.contains(&0));
                assert!(node_dominators.contains(&1));
            } else if cfg.dag.get_node_name(node) == "body" {
                assert_eq!(node_dominators.len(), 3);
                assert!(node_dominators.contains(&0));
                assert!(node_dominators.contains(&1));
                assert!(node_dominators.contains(&2));
            } else if cfg.dag.get_node_name(node) == "then" {
                assert_eq!(node_dominators.len(), 4);
                assert!(node_dominators.contains(&0));
                assert!(node_dominators.contains(&1));
                assert!(node_dominators.contains(&2));
                assert!(node_dominators.contains(&3));
            } else if cfg.dag.get_node_name(node) == "endif" {
                assert_eq!(node_dominators.len(), 4);
                assert!(node_dominators.contains(&0));
                assert!(node_dominators.contains(&1));
                assert!(node_dominators.contains(&2));
                assert!(node_dominators.contains(&4));
            } else if cfg.dag.get_node_name(node) == "exit" {
                assert_eq!(node_dominators.len(), 3);
                assert!(node_dominators.contains(&0));
                assert!(node_dominators.contains(&1));
                assert!(node_dominators.contains(&5));
            }
        }

        let domination_frontiers = dominators.build_dom_frontiers();
        for node in 0..cfg.dag.number_of_nodes() {
            let node_frontiers = &domination_frontiers.set_per_node[node];
            if cfg.dag.get_node_name(node) == "entry" {
                assert_eq!(node_frontiers.len(), 0);
            } else if cfg.dag.get_node_name(node) == "loop" {
                assert_eq!(node_frontiers.len(), 1);
                assert!(node_frontiers.contains(&1));
            } else if cfg.dag.get_node_name(node) == "body" {
                assert_eq!(node_frontiers.len(), 1);
                assert!(node_frontiers.contains(&1));
            } else if cfg.dag.get_node_name(node) == "then" {
                assert_eq!(node_frontiers.len(), 1);
                assert!(node_frontiers.contains(&4));
            } else if cfg.dag.get_node_name(node) == "endif" {
                assert_eq!(node_frontiers.len(), 1);
                assert!(node_frontiers.contains(&1));
            } else if cfg.dag.get_node_name(node) == "exit" {
                assert_eq!(node_frontiers.len(), 0);
            }
        }
    }
}
