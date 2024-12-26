use bril_rs::{Instruction, Type, ValueOps};

use super::{Cfg, DirectedGraph, DominanceFrontiers};
use crate::{cfg::Dominators, BasicBlock};
use std::collections::{HashMap, HashSet};

pub struct SsaBuilderState {
    cfg: Cfg,                                  // The cfg in ssa form, to be built incrementally.
    dominator_tree: DirectedGraph<BasicBlock>, // The dominator-tree of the input cfg.
    per_variable_stack: HashMap<String, Vec<String>>, // The stack of names for each variable. The top of the stack is the latest version of the variable.
    per_variable_index: HashMap<String, usize>, // A map from variable name to the index of the next version of the variable.
    phi_nodes_per_block: HashMap<usize, Vec<bril_rs::Instruction>>, // The phi nodes to be inserted in each block.
}

/// Extracts the definition sites of each variable in the cfg.
fn extract_variable_definition_sites(
    cfg: &Cfg,
) -> HashMap<
    String,                          /* Variable Name */
    (bril_rs::Type, HashSet<usize>), /* Block's where variable is defined */
> {
    let mut defintion_sites: HashMap<String, (bril_rs::Type, HashSet<usize>)> = HashMap::new();
    for block in 0..cfg.dag.number_of_nodes() {
        for instr in cfg.get_basic_block(block).instruction_stream.iter() {
            let (destination, type_t) = {
                if let bril_rs::Instruction::Value { dest, op_type, .. } = instr {
                    (dest.clone(), op_type.clone())
                } else if let bril_rs::Instruction::Constant {
                    dest, const_type, ..
                } = instr
                {
                    (dest.clone(), const_type.clone())
                } else {
                    continue;
                }
            };
            if let Some((stored_type_t, blocks)) = defintion_sites.get_mut(&destination) {
                assert!(stored_type_t == &type_t);
                blocks.insert(block);
            } else {
                defintion_sites.insert(destination, (type_t, HashSet::from([block])));
            }
        }
    }
    defintion_sites
}

/// Returns the blocks where phi functions need to be inserted for a given variable.
fn get_phi_insertion_sites_for_variable(
    definition_sites: HashSet<usize>,
    domination_frontiers: &DominanceFrontiers,
) -> Vec<usize> {
    // Worklist algorithm to find all the blocks where phi functions need to be inserted
    let mut workset = definition_sites;
    let mut already_considered = workset.clone();
    let mut phi_bool = vec![false; domination_frontiers.set_per_node.len()]; // phi_bool[i] = true if phi function is inserted in block i

    while !workset.is_empty() {
        let block = workset.iter().next().unwrap().clone();
        workset.remove(&block);

        for frontier in domination_frontiers.set_per_node.get(block).unwrap() {
            if !phi_bool[*frontier] {
                phi_bool[*frontier] = true;
                if !already_considered.contains(frontier) {
                    workset.insert(*frontier);
                    already_considered.insert(*frontier);
                }
            }
        }
    }

    phi_bool
        .iter()
        .enumerate()
        .filter(|(_, contains_phi)| **contains_phi)
        .map(|(index, _)| index)
        .collect()
}

/// Generates the phi nodes to be inserted in each block.
fn generate_phi_nodes_per_block(
    input_cfg: &Cfg,
    per_variables_phi_insertion_sites: &HashMap<String, (bril_rs::Type, Vec<usize>)>,
) -> HashMap<
    usize,                     /*Block ID */
    Vec<bril_rs::Instruction>, /*Phi instructions to be inserted */
> {
    let mut phi_nodes_per_block: HashMap<usize, Vec<bril_rs::Instruction>> = HashMap::new();
    for (variable, (variable_type, insertion_sites)) in per_variables_phi_insertion_sites {
        for block in insertion_sites {
            let predecessors: Vec<String> = input_cfg
                .dag
                .get_predecessor_indices(*block)
                .iter()
                .map(|pred_index| {
                    let pred_name = input_cfg.dag.get_node_name(*pred_index).to_string();
                    pred_name
                })
                .collect();
            let phi_node = bril_rs::Instruction::Value {
                args: vec![variable.clone(); predecessors.len()],
                dest: variable.clone(),
                funcs: vec![],
                labels: predecessors,
                op: bril_rs::ValueOps::Phi,
                pos: None,
                op_type: variable_type.clone(),
            };
            if let Some(existing_phi_nodes) = phi_nodes_per_block.get_mut(&block) {
                existing_phi_nodes.push(phi_node);
            } else {
                phi_nodes_per_block.insert(*block, vec![phi_node]);
            }
        }
    }
    phi_nodes_per_block
}

impl SsaBuilderState {
    /// Creates a new instance of the SsaConverter.
    pub fn new(cfg: Cfg) -> Self {
        let dominators = Dominators::new(&cfg);
        let dominator_tree: DirectedGraph<BasicBlock> = dominators.build_dom_tree();
        let domination_frontiers: DominanceFrontiers<'_> = dominators.build_dom_frontiers();
        let per_variables_phi_insertion_sites: HashMap<String, (bril_rs::Type, Vec<usize>)> =
            extract_variable_definition_sites(&cfg)
                .into_iter()
                .map(|(variable, (type_t, definition_sites))| {
                    let insertion_sites = get_phi_insertion_sites_for_variable(
                        definition_sites,
                        &domination_frontiers,
                    );
                    (variable, (type_t, insertion_sites))
                })
                .collect();
        let phi_nodes_per_block =
            generate_phi_nodes_per_block(&cfg, &per_variables_phi_insertion_sites);
        let per_variable_stack: HashMap<String, Vec<String>> = per_variables_phi_insertion_sites
            .iter()
            .map(|(variable, _)| (variable.clone(), vec![variable.clone()]))
            .collect();
        let per_variable_index: HashMap<String, usize> = per_variables_phi_insertion_sites
            .iter()
            .map(|(variable, _)| (variable.clone(), 0))
            .collect();
        SsaBuilderState {
            cfg,
            dominator_tree,
            per_variable_stack,
            per_variable_index,
            phi_nodes_per_block,
        }
    }

    fn rename_dfs(&mut self, block: usize) {
        let per_variable_stack_snapshot = self.per_variable_stack.clone();

        for phi_node in self
            .phi_nodes_per_block
            .get_mut(&block)
            .unwrap_or(&mut Vec::new())
        {
            let destination = {
                if let bril_rs::Instruction::Value {
                    dest,
                    op: bril_rs::ValueOps::Phi,
                    ..
                } = phi_node
                {
                    dest
                } else {
                    panic!("Unexpected; Phi node not found");
                }
            };
            let new_name = format!(
                "{}_{}",
                destination,
                self.per_variable_index.get(destination).unwrap()
            );
            *self.per_variable_index.get_mut(destination).unwrap() += 1;
            self.per_variable_stack
                .get_mut(destination)
                .unwrap()
                .push(new_name.clone());
            *destination = new_name.clone();
        }

        for instruction in self
            .cfg
            .get_basic_block_mut(block)
            .instruction_stream
            .iter_mut()
        {
            let (destination, args) = {
                match instruction {
                    bril_rs::Instruction::Constant { dest, .. } => (Some(dest), None),
                    bril_rs::Instruction::Value { args, dest, .. } => (Some(dest), Some(args)),
                    bril_rs::Instruction::Effect { args, .. } => (None, Some(args)),
                }
            };
            if let Some(arguments) = args {
                for arg in arguments.iter_mut() {
                    if !self.per_variable_stack.contains_key(arg) {
                        // Don't rename function arguments
                        continue;
                    }
                    let new_name = self
                        .per_variable_stack
                        .get(arg)
                        .expect("Variable not found")
                        .last()
                        .expect("Unexpected empty stack");
                    *arg = new_name.clone();
                }
            }
            if let Some(dest) = destination {
                let new_name = format!("{}_{}", dest, self.per_variable_index.get(dest).unwrap());
                *self.per_variable_index.get_mut(dest).unwrap() += 1;
                self.per_variable_stack
                    .get_mut(dest)
                    .unwrap()
                    .push(new_name.clone());
                *dest = new_name.clone();
            }
        }

        for successor in self.cfg.dag.get_successor_indices(block).iter() {
            for phi_node in self
                .phi_nodes_per_block
                .get_mut(&successor)
                .unwrap_or(&mut Vec::new())
            {
                let (args, labels) = {
                    if let bril_rs::Instruction::Value {
                        args,
                        labels,
                        op: bril_rs::ValueOps::Phi,
                        ..
                    } = phi_node
                    {
                        (args, labels)
                    } else {
                        panic!("Unexpected; Phi node not found");
                    }
                };
                let position = labels
                    .iter()
                    .position(|label| label == self.cfg.dag.get_node_name(block))
                    .expect("Label not found");
                let arg_to_rename = args.get_mut(position).expect("Position out of bounds");
                *arg_to_rename = self
                    .per_variable_stack
                    .get(arg_to_rename)
                    .expect("Variable not found")
                    .last()
                    .expect("Unexpected empty stack")
                    .clone();
            }
        }
        let dom_tree_successors: Vec<usize> = self
            .dominator_tree
            .get_successor_indices(block)
            .iter()
            .cloned()
            .collect();
        for successor in dom_tree_successors {
            self.rename_dfs(successor);
        }
        self.per_variable_stack = per_variable_stack_snapshot;
    }
    pub fn get_ssa_cfg(mut self) -> Cfg {
        self.rename_dfs(0);
        for (block, phi_nodes) in self.phi_nodes_per_block {
            let instruction_stream = self
                .cfg
                .get_basic_block_mut(block)
                .instruction_stream
                .clone();
            self.cfg.get_basic_block_mut(block).instruction_stream =
                [phi_nodes, instruction_stream].concat();
        }
        self.cfg
    }
}

/// Extracts the phi nodes and the remaining instructions in a basic block.
pub fn extract_phi_nodes<'a>(
    basic_block: BasicBlock,
) -> (
    Vec<Instruction>, /*Phi Instructions */
    Vec<Instruction>, /*Remaining instructions in basic block */
) {
    basic_block
        .instruction_stream
        .into_iter()
        .partition(|instruction| {
            if let Instruction::Value {
                op: bril_rs::ValueOps::Phi,
                ..
            } = instruction
            {
                true
            } else {
                false
            }
        })
}

pub fn extract_phi_node_instrction(
    instruction: &Instruction,
) -> (
    &Vec<std::string::String>,
    &std::string::String,
    &Vec<std::string::String>,
    &Type,
) {
    if let Instruction::Value {
        op: ValueOps::Phi,
        args,
        dest,
        labels,
        op_type,
        ..
    } = instruction
    {
        (args, dest, labels, op_type)
    } else {
        panic!("Expected Phi node")
    }
}
