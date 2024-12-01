use super::{Cfg, DirectedGraph, DominanceFrontiers};
use crate::{cfg::Dominators, BasicBlock};
use bril_rs::{Code, Program};
use std::collections::{HashMap, HashSet};

struct SsaConverter<'a> {
    _input_cfg: &'a Cfg,                                            // The input cfg.
    cfg: Cfg, // The cfg in ssa form, to be built incrementally.
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

impl<'a> SsaConverter<'a> {
    /// Creates a new instance of the SsaConverter.
    fn new(input_cfg: &'a Cfg) -> Self {
        let dominators: Dominators<'a> = Dominators::new(input_cfg);
        let dominator_tree: DirectedGraph<BasicBlock> = dominators.build_tree();
        let domination_frontiers: DominanceFrontiers<'_> = dominators.build_dom_frontiers();
        let per_variables_phi_insertion_sites: HashMap<String, (bril_rs::Type, Vec<usize>)> =
            extract_variable_definition_sites(input_cfg)
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
            generate_phi_nodes_per_block(input_cfg, &per_variables_phi_insertion_sites);
        let per_variable_stack: HashMap<String, Vec<String>> = per_variables_phi_insertion_sites
            .iter()
            .map(|(variable, _)| (variable.clone(), vec![variable.clone()]))
            .collect();
        let per_variable_index: HashMap<String, usize> = per_variables_phi_insertion_sites
            .iter()
            .map(|(variable, _)| (variable.clone(), 0))
            .collect();
        SsaConverter {
            _input_cfg: input_cfg,
            cfg: input_cfg.clone(),
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
    fn get_ssa_cfg(mut self) -> Cfg {
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

pub fn convert_to_ssa(program: Program) -> Program {
    let mut ssa_form_program = program;
    for function in ssa_form_program.functions.iter_mut() {
        let cfg = Cfg::new(function);
        let ssa_cfg = SsaConverter::new(&cfg).get_ssa_cfg();
        function.instrs = ssa_cfg
            .dag
            .nodes
            .into_iter()
            .map(|node| {
                let mut instructions: Vec<Code> = Vec::new();
                instructions.push(Code::Label {
                    label: node.name.clone(),
                    pos: None,
                });
                let basic_block = node.data;
                for instruction in basic_block.instruction_stream {
                    instructions.push(Code::Instruction(instruction));
                }
                instructions
            })
            .flatten()
            .collect::<Vec<Code>>();
    }
    ssa_form_program
}

pub fn convert_from_ssa(_ssa_cfg: &Cfg) -> Cfg {
    todo!()
}

#[cfg(test)]
mod tests {
    use crate::cfg::ssa::convert_to_ssa;
    use bril_rs::Program;
    use brilirs::{basic_block::BBProgram, interp};
    use indoc::indoc;
    use std::collections::HashSet;

    fn get_program_output(program: Program, input_args: &[String]) -> String {
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

    fn is_ssa(program: &Program) -> bool {
        let mut assigned: HashSet<&str> = HashSet::new();
        for function in program.functions.iter() {
            for instr in function.instrs.iter() {
                if let bril_rs::Code::Instruction(instruction) = instr {
                    if let bril_rs::Instruction::Value { dest, .. } = instruction {
                        if assigned.contains(dest.as_str()) {
                            return false;
                        }
                        assigned.insert(dest);
                    } else if let bril_rs::Instruction::Constant { dest, .. } = instruction {
                        if assigned.contains(dest.as_str()) {
                            return false;
                        }
                        assigned.insert(dest);
                    }
                }
            }
        }
        true
    }

    #[test]
    fn test_ssa_construction1() {
        let program = crate::parse_bril_text(indoc! {"
                @main(flag: bool) {
                .entry:
                  x: int = const 0;
                  br flag .left .right;

                .left:
                  one: int = const 1;
                  x: int = add x one;
                  jmp .join;

                .right:
                  two: int = const 2;
                  x: int = add x two;
                  jmp .join;

                .join:
                  x: int = add x x;

                .exit:
                  print x;
                }
            "})
        .unwrap();
        let ssa_program = convert_to_ssa(program.clone());
        assert!(is_ssa(&ssa_program), "{}", ssa_program);
        assert!(
            get_program_output(program, &["true".to_string()])
                == get_program_output(ssa_program, &["true".to_string()])
        );
    }

    #[test]
    fn test_ssa_construction2() {
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
        let ssa_program = convert_to_ssa(program.clone());
        assert!(is_ssa(&ssa_program), "{}", ssa_program);
        assert!(get_program_output(program, &[]) == get_program_output(ssa_program, &[]));
    }
}
