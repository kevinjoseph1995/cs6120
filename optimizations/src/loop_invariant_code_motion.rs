use crate::Pass;
use common::cfg::{self, Cfg, Dominators};
use dataflow_analysis::{run_analysis, DataflowAnalyses, ReachingDefinitions};
use std::collections::HashSet;

pub struct LoopInvariantCodeMotionPass {}

impl Pass for LoopInvariantCodeMotionPass {
    fn apply(&mut self, mut program: bril_rs::Program) -> bril_rs::Program {
        let mut output_program = cfg::convert_to_ssa(program);
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
) -> Vec<usize> {
    let mut loop_nodes = vec![loop_header];
    let mut visited = vec![false; cfg.dag.number_of_nodes()];
    visited[loop_header] = true;
    let mut nodes_to_visit = vec![seed];
    while !nodes_to_visit.is_empty() {
        let node = nodes_to_visit.pop().unwrap();
        visited[node] = true;
        loop_nodes.push(node);
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

impl LoopInvariantCodeMotionPass {
    pub fn new() -> Self {
        LoopInvariantCodeMotionPass {}
    }
    fn process_cfg(&mut self, cfg: Cfg) -> Cfg {
        // Precondition: We make the assumption that the CFG is reducible.
        let dominators = cfg::Dominators::new(&cfg);
        let (reaching_definitions_in, reaching_definitions_out) =
            ReachingDefinitions {}.run_analysis(&cfg, Some(false));
        find_back_edges(&cfg, &dominators)
            .iter()
            .map(|(src, loop_header)| {
                // For each back edge, find the loop nodes.
                assert!(
                    dominators.set_per_node[*src].contains(&loop_header),
                    "{src}->{loop_header}| dominators of {} are: {:#?}",
                    loop_header,
                    dominators.set_per_node[*loop_header]
                );
                (
                    *loop_header,
                    find_loop_nodes(&cfg, &dominators, *loop_header, *src),
                )
            })
            .for_each(
                |(loop_header, loop_nodes)| // For each loop, find the loop invariant instructions.
            {
                // todo!("Find loop invariant instructions for loop: {:#?}", loop_nodes);
            },
            );

        cfg
    }
}

#[cfg(test)]
mod tests {
    use crate::Pass;
    use bril_rs::Program;

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
            br cond .body .done;
        .body:
            temp: int = add invariant inc;
            sum: int = add sum temp;
            i: int = add i one;
            body_cond: bool = lt temp sum;
            br body_cond .body_left .body_right;
        .body_left:
            jmp .body_join;
        .body_right:
            dead_store: int = const 0;
            jmp .body_join;
        .body_join:
            jmp .loop;
        .done:
            print sum;
            ret;
        }
        "#});
        let optimized_program = super::LoopInvariantCodeMotionPass::new().apply(program);
        println!("{}", optimized_program);
    }
}
