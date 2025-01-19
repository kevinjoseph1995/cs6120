use crate::Pass;
use bril_rs::{Instruction, ValueOps};
use common::{
    cfg::{self, Cfg, Dominators},
    BasicBlock,
};
use dataflow_analysis::{Definition, LiveVariableAnalysis, ReachingDefinitions};
use std::collections::{HashMap, HashSet};

pub struct LoopInvariantCodeMotionPass {}

impl Pass for LoopInvariantCodeMotionPass {
    fn apply(&mut self, program: bril_rs::Program) -> bril_rs::Program {
        let mut output_program = program;
        for function in output_program.functions.iter_mut() {
            function.instrs = common::cfg::convert_cfg_to_instruction_stream(
                self.process_cfg(Cfg::new(function)),
            );
        }
        output_program
    }
}

fn find_back_edges(
    cfg: &Cfg,
    dominators: &Dominators,
) -> HashSet<(usize /*Start index*/, usize /*End index*/)> {
    if cfg.dag.number_of_nodes() == 0 {
        return HashSet::new();
    }
    let mut back_edges = HashSet::new();
    let mut visited = vec![false; cfg.dag.number_of_nodes()];
    let mut nodes_to_visit = vec![0];
    while !nodes_to_visit.is_empty() {
        let node = nodes_to_visit.pop().unwrap();
        visited[node] = true;
        for &successor in cfg.dag.get_successor_indices(node) {
            // If the successor is visited and is a dominator of the current node, then it is a back edge.
            if visited[successor] && dominators.set_per_node[node].contains(&successor) {
                back_edges.insert((node, successor));
            } else {
                nodes_to_visit.push(successor);
            }
        }
    }
    back_edges
}

fn find_loop_nodes(
    cfg: &Cfg,
    dominators: &Dominators,
    loop_header: usize,
    seed: usize,
) -> HashSet<usize> {
    assert!(
        dominators.set_per_node[seed].contains(&loop_header),
        "{seed}->{loop_header}| dominators of {} are: {:#?}",
        loop_header,
        dominators.set_per_node[loop_header]
    );
    let mut loop_nodes = HashSet::from([loop_header]);
    let mut visited = vec![false; cfg.dag.number_of_nodes()];
    visited[loop_header] = true;
    let mut nodes_to_visit = vec![seed];
    while !nodes_to_visit.is_empty() {
        let node = nodes_to_visit.pop().unwrap();
        visited[node] = true;
        loop_nodes.insert(node);
        for &predecessor in cfg.dag.get_predecessor_indices(node) {
            // If the predecessor is not visited and if the loop header dominates the predecessor, then add it to the list of nodes to visit.
            // All nodes in the loop should have the loop header as a dominator.
            if !visited[predecessor] && dominators.set_per_node[predecessor].contains(&loop_header)
            {
                nodes_to_visit.push(predecessor);
            }
        }
    }
    loop_nodes
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstructionSite {
    destination_variable: String,
    basic_block_index: usize,
    instruction_index: usize,
}

#[derive(Debug, Clone)]
struct LoopMetadata {
    loop_header: usize,                                // The index of the loop header.
    loop_invariant_instructions: Vec<InstructionSite>, // The set of loop invariant instructions.
    loop_nodes: HashSet<usize>,                        // The set of nodes in the loop.
}

fn find_loop_invariant_instructions(
    cfg: &Cfg,
    loop_header: usize,
    loop_nodes: &HashSet<usize>,
    reaching_definitions_in: &Vec<HashSet<Definition>>,
    dominators: &Dominators,
    live_variables_in: &Vec<HashSet<&str>>,
) -> Vec<InstructionSite> {
    assert!(loop_nodes.contains(&loop_header));
    // We use a hashset to keep track of the loop invariant instructions. We use a hashset to do quick lookups.
    let mut loop_invariant_instructions = HashSet::new();
    // We use a vector to keep track of the order in which the loop invariant instructions are found.
    let mut loop_invariant_instructions_vec = Vec::<InstructionSite>::new();
    loop {
        let current_size = loop_invariant_instructions.len();
        for loop_node in loop_nodes {
            for (index, instruction) in cfg
                .get_basic_block(*loop_node)
                .instruction_stream
                .iter()
                .enumerate()
            {
                let (args, dest) = match instruction {
                    bril_rs::Instruction::Value {
                        op: ValueOps::Phi, ..
                    } => continue,
                    bril_rs::Instruction::Value { args, dest, .. } => (args, dest),
                    bril_rs::Instruction::Constant { dest, .. } => (&vec![], dest),
                    _ => continue,
                };
                if loop_invariant_instructions.contains(&InstructionSite {
                    destination_variable: dest.clone(),
                    basic_block_index: *loop_node,
                    instruction_index: index,
                }) {
                    // The instruction is already marked as loop invariant.
                    continue;
                }
                // A instruction is loop invariant when all of its arguments is either constant or variable "var" satisfying:
                //      1. All reaching definitions of var are outside the loop.
                //      2. There is exactly one reaching definition of var and the definition is loop-invariant.
                let is_loop_invariant: bool = {
                    args.is_empty() || // This is a constant instruction as there are no arguments
                    args.iter().all(|argument| {
                        let incoming_definitions = &reaching_definitions_in[*loop_node];
                        let matching_definitions: Vec<&Definition> =
                            incoming_definitions.iter().filter(|definition| {
                                definition.destination_variable == argument
                            }).collect();
                        if matching_definitions.len() == 0 {
                            return false
                        } else if matching_definitions.len() > 1 {
                            return false;
                        } else if !loop_nodes.contains(&matching_definitions[0].basic_block_index) {
                            return true;
                        } else {
                            let definition = &matching_definitions[0];
                            // The argument is already marked as loop invariant
                            return loop_invariant_instructions.contains(&InstructionSite {
                                destination_variable: definition.destination_variable.to_string(),
                                basic_block_index: definition.basic_block_index,
                                instruction_index: definition.instruction_index
                            });
                        }
                    })
                };
                if is_loop_invariant {
                    let site = InstructionSite {
                        destination_variable: dest.clone(),
                        basic_block_index: *loop_node,
                        instruction_index: index,
                    };
                    loop_invariant_instructions.insert(site.clone());
                    loop_invariant_instructions_vec.push(site);
                }
            }
        }

        if current_size == loop_invariant_instructions.len() {
            // No new loop invariant instructions were found.
            break;
        }
    }
    return filter_loop_invariant_instructions(
        loop_invariant_instructions_vec,
        cfg,
        loop_nodes,
        dominators,
        live_variables_in,
    );
}

fn filter_loop_invariant_instructions(
    instructions: Vec<InstructionSite>,
    cfg: &Cfg,
    loop_nodes: &HashSet<usize>,
    dominators: &Dominators,
    live_variables_in: &Vec<HashSet<&str>>,
) -> Vec<InstructionSite> {
    // Need to filter the loop invariant instructions.
    // If the destination of an LII is d, it needs to satisfy the following condition:
    // 1. The instruction should not have any side effects(Already satisfied as the candidate instructions are Value instructions). ✅
    // 2  There is only one definition of d in the loop. ⏳
    // 3. d's block dominates all loop exits. ⏳
    // 4. The definition of d dominates all uses of d in the loop (Already satisfied by being SSA). ⏳

    // We need to find the loop exits.
    let loop_exits = loop_nodes
        .iter()
        .filter(|node| {
            cfg.dag.get_successor_indices(**node).iter().any(
                |successor| !loop_nodes.contains(successor), /* The successor is not in the loop. */
            )
        })
        .cloned()
        .collect::<HashSet<_>>();
    let loop_defitntions = {
        let mut loop_defitntions: HashMap<String, Vec<(usize, usize)>> = HashMap::new();
        loop_nodes
            .iter()
            .map(|loop_node| {
                cfg.get_basic_block(*loop_node)
                    .instruction_stream
                    .iter()
                    .filter(|instruction| match instruction {
                        Instruction::Constant { .. } => true,
                        Instruction::Value { .. } => true,
                        Instruction::Effect { .. } => false,
                    })
                    .enumerate()
                    .map(|(instruction_index, instruction)| match instruction {
                        Instruction::Constant { dest, .. } => {
                            (dest.clone(), instruction_index, *loop_node)
                        }
                        Instruction::Value { dest, .. } => {
                            (dest.clone(), instruction_index, *loop_node)
                        }
                        _ => {
                            panic!(
                                "Unexpected effect instruction found in loop node: {:?}",
                                instruction
                            );
                        }
                    })
            })
            .flatten()
            .for_each(|(dest, instruction_index, loop_node)| {
                loop_defitntions
                    .entry(dest)
                    .or_insert_with(Vec::new)
                    .push((loop_node, instruction_index));
            });
        loop_defitntions
    };

    let uses = {
        let mut uses: HashMap<String, Vec<(usize, usize)>> = HashMap::new();
        (0..cfg.dag.number_of_nodes())
            .map(|node| {
                cfg.get_basic_block(node)
                    .instruction_stream
                    .iter()
                    .filter(|instruction| match instruction {
                        Instruction::Constant { .. } => false,
                        Instruction::Value { .. } => true,
                        Instruction::Effect { .. } => false,
                    })
                    .enumerate()
                    .map(move |(instruction_index, instruction)| match instruction {
                        Instruction::Value { args, .. } => (args.iter(), instruction_index, node),
                        Instruction::Effect { args, .. } => (args.iter(), instruction_index, node),
                        _ => panic!(
                            "Unexpected constant instruction found in loop node: {:?}",
                            instruction
                        ),
                    })
            })
            .flatten()
            .for_each(|(args, instruction_index, loop_node)| {
                args.for_each(|arg| {
                    uses.entry(arg.to_string())
                        .or_insert_with(Vec::new)
                        .push((loop_node, instruction_index));
                });
            });
        uses
    };

    return instructions
        .into_iter()
        .filter(|instruction| {
            let instruction_block = instruction.basic_block_index;
            let instruction_index = instruction.instruction_index;
            let destination_variable = instruction.destination_variable.as_str();
            loop_defitntions[destination_variable].len() == 1 // There is only one definition of d in the loop ✅
                && loop_exits.iter().all(|exit| { // d's block dominates all loop exits ✅
                    if cfg
                        .dag
                        .get_successor_indices(*exit)
                        .iter()
                        .filter(|&successor| !loop_nodes.contains(successor))
                        .any(|successor| {
                            live_variables_in[*successor].contains(destination_variable)
                        })
                    {
                        // The destination variable is live at the exit.
                        dominators.set_per_node[*exit].contains(&instruction_block)
                    } else {
                        // The destination variable is not live at the exit.
                        true
                    }
                }) && {
                    if uses.contains_key(destination_variable) {
                        uses[destination_variable].iter().all(|(use_block, use_index)| {
                            // The definition of d dominates all uses of d in the loop ✅
                            dominators.set_per_node[*use_block].contains(&instruction_block)
                                || (instruction_block == *use_block
                                    && instruction_index < *use_index) // The definition is before the use in the same block.
                        })
                    } else {
                        // The destination variable is not used. So, it is safe to move it.
                        true
                    }
                }
        })
        .collect();
}

impl LoopInvariantCodeMotionPass {
    pub fn new() -> Self {
        LoopInvariantCodeMotionPass {}
    }
    fn process_cfg(&mut self, mut cfg: Cfg) -> Cfg {
        // Precondition: We make the assumption that the CFG is reducible.
        let dominators = cfg::Dominators::new(&cfg);
        let (reaching_definitions_in, _reaching_definitions_out) =
            ReachingDefinitions {}.run_analysis(&cfg, Some(false));
        let (live_variables_in, _live_variables_out) =
            LiveVariableAnalysis {}.run_analysis(&cfg, Some(false));
        let loop_metadata_vector: Vec<LoopMetadata> = find_back_edges(&cfg, &dominators)
            .iter()
            .map(|(src, loop_header)| {
                let loop_nodes = find_loop_nodes(&cfg, &dominators, *loop_header, *src);
                // For each loop, we need to find the loop invariant instructions and move them to the preheader.
                // The preheader is the node that dominates the loop header and has only one successor, which is the loop header.
                let loop_invariant_instructions = find_loop_invariant_instructions(
                    &cfg,
                    *loop_header,
                    &loop_nodes,
                    &reaching_definitions_in,
                    &dominators,
                    &live_variables_in,
                );
                LoopMetadata {
                    loop_header: *loop_header,
                    loop_invariant_instructions,
                    loop_nodes,
                }
            })
            .collect();
        for loop_metadata in loop_metadata_vector {
            let mut instructions = Vec::<Instruction>::new();
            for site in &loop_metadata.loop_invariant_instructions {
                let instruction = cfg
                    .get_basic_block(site.basic_block_index)
                    .instruction_stream[site.instruction_index]
                    .clone();
                instructions.push(instruction);
            }
            loop_metadata
                .loop_invariant_instructions
                .iter()
                .for_each(|site| {
                    let basic_block = cfg.get_basic_block_mut(site.basic_block_index);
                    basic_block
                        .instruction_stream
                        .remove(site.instruction_index);
                });

            let new_node_name = format!(
                "preheader_{}",
                cfg.dag.get_node_name(loop_metadata.loop_header)
            );
            cfg.insert_new_parent(
                loop_metadata.loop_header,
                BasicBlock {
                    name: Some(new_node_name.clone()),
                    instruction_stream: instructions,
                },
                new_node_name,
                loop_metadata.loop_nodes,
            );
        }
        cfg
    }
}

#[cfg(test)]
mod tests {
    use crate::Pass;
    use bril_rs::Program;
    use common::get_program_output;

    fn parse_program(text: &str) -> Program {
        let program = common::parse_bril_text(text);
        assert!(program.is_ok(), "{}", program.err().unwrap());
        program.unwrap()
    }

    #[test]
    fn test_loop_invariant_code_motion() {
        let program = parse_program(indoc::indoc! {r#"
        @main {
            n: int = const 10;
            inc: int = const 5;
            one: int = const 1;
            invariant: int = const 100;
            i: int = const 0;
            sum: int = const 0;
        .loop:
            cond: bool = lt i n;
            temp66: int = add invariant inc;
            br cond .body .done;
        .body:
            temp: int = add invariant inc;
            sum: int = add sum temp;
            i: int = add i one;
            body_cond: bool = lt temp sum;
            br body_cond .body_left .body_right;
        .body_left:
            temp2: int = add temp invariant;
            jmp .body_join;
        .body_right:
            temp2: int = add temp inc;
            dead_store: int = const 0;
            jmp .body_join;
        .body_join:
            jmp .loop;
        .done:
            print temp66;
            print sum;
            ret;
        }
        "#});
        let output_original = get_program_output(program.clone(), &[]);
        let optimized_program = super::LoopInvariantCodeMotionPass::new().apply(program);
        let output = get_program_output(optimized_program.clone(), &[]);
        assert_eq!(output_original, output, "{}", optimized_program);
    }

    #[test]
    fn test_loop_invariant_code_motion2() {
        let program = parse_program(indoc::indoc! {r#"
        @main {
            #--------------------------------
            # Constants
            #--------------------------------
            outerLimit: int = const 3;
            innerLimit: int = const 2;
            one: int       = const 1;
            offset: int    = const 10;

            #--------------------------------
            # Variables
            #--------------------------------
            i: int   = const 0;
            j: int   = const 0;
            sum: int = const 0;

            #--------------------------------
            # Outer loop
            #--------------------------------
            .outerLoop:
                condOuter: bool = lt i outerLimit;
                br condOuter .outerBody .outerDone;

            .outerBody:
                # Reset j for the inner loop
                j: int = const 0;

                #-----------------------------
                # Inner loop
                #-----------------------------
                .innerLoop:
                    condInner: bool = lt j innerLimit;
                    br condInner .innerBody .innerDone;

                .innerBody:
                    # Example partial-invariant expression for the inner loop
                    temp: int = add i offset;     # i + offset is invariant wrt j
                    sum: int  = add sum temp;     # Accumulate it
                    sum: int  = add sum j;        # Also add j (changes each iteration of inner loop)

                    # Increment j
                    j: int = add j one;
                    jmp .innerLoop;

                .innerDone:
                    # Increment i before repeating outer loop
                    i: int = add i one;
                    jmp .outerLoop;

            .outerDone:
                # Print sum and return
                print sum;
                ret;
        }
        "#});
        let output_original = get_program_output(program.clone(), &[]);
        let optimized_program = super::LoopInvariantCodeMotionPass::new().apply(program);
        let output = get_program_output(optimized_program.clone(), &[]);
        assert_eq!(output_original, output, "{}", optimized_program);
    }
}
