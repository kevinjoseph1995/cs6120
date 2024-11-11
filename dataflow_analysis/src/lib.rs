use std::collections::HashSet;
use std::fmt::Display;
use std::hash::Hash;

use bril_rs::Program;
use clap::ValueEnum;
use common::cfg::{Cfg, NodeIndex};

#[derive(ValueEnum, Clone, Debug, PartialEq, Copy)]
pub enum DataflowAnalyses {
    LiveVariable,
}

enum Direction {
    Forward,
    Backward,
}

trait Analysis<'a, ValueType: Clone + Hash + Eq + Display> {
    fn run(&self, cfg: &'a Cfg, init: HashSet<ValueType>, direction: Direction) -> () {
        let all_predecessors: Vec<&[usize]> = (0..cfg.number_of_nodes())
            .map(|node_index| cfg.get_predecessor_indices(node_index))
            .collect();
        let all_successors: Vec<&[usize]> = (0..cfg.number_of_nodes())
            .map(|node_index| cfg.get_successor_indices(node_index))
            .collect();
        let (input_edges, output_edges) = match direction {
            Direction::Forward => (all_predecessors, all_successors),
            Direction::Backward => (all_successors, all_predecessors),
        };

        let mut worklist: Vec<usize> = (0..cfg.number_of_nodes()).collect();

        let mut input_list: Vec<HashSet<ValueType>> = (0..cfg.number_of_nodes())
            .map(|_| HashSet::<ValueType>::new() /*Empty set */)
            .collect();
        let mut output_list: Vec<HashSet<ValueType>> =
            (0..cfg.number_of_nodes()).map(|_| init.clone()).collect();
        input_list[0] = init;

        while !worklist.is_empty() {
            // Pick any node from the worklist and pop it out
            let node_index = worklist.pop().expect("Worklist is empty");
            input_list[node_index] = input_edges[node_index]
                .iter()
                .fold(HashSet::<ValueType>::new(), |acc, predecessor_index| {
                    self.merge(acc, &output_list[*predecessor_index])
                });
            // Apply transfer function
            let new_output = self.transfer(cfg, node_index, &input_list[node_index]);
            if new_output != output_list[node_index] {
                // If the output has changed, update the output and add all successors to the worklist
                output_list[node_index] = new_output;
                worklist.extend(output_edges[node_index]);
            }
        }
        self.display(cfg, &input_list, &output_list);
    }

    fn display(
        &self,
        cfg: &Cfg,
        inputs: &Vec<HashSet<ValueType>>,
        outputs: &Vec<HashSet<ValueType>>,
    ) -> () {
        let total_number_of_nodes = cfg.number_of_nodes();
        let mut statements: Vec<String> = Vec::new();
        // Add node statements
        for index in 0..total_number_of_nodes {
            let node_name = cfg.get_node_name(index);
            let mut node_text = String::new();
            // Add more information for each node
            for instr in cfg.get_basic_block(index).instruction_stream.iter() {
                node_text.push_str(&format!("{}\\n", instr));
            }
            let formatted_values: Vec<String> = inputs[index]
                .iter()
                .map(|value| format!("{}", value))
                .collect();
            let in_ = format!("  in: {}", {
                if formatted_values.is_empty() {
                    "∅".to_string()
                } else {
                    formatted_values.join(", ")
                }
            });
            let formatted_values: Vec<String> = outputs[index]
                .iter()
                .map(|value| format!("{}", value))
                .collect();
            let out = format!("  out: {}", {
                if formatted_values.is_empty() {
                    "∅".to_string()
                } else {
                    formatted_values.join(", ")
                }
            });
            statements.push(format!(
                "\"{node_name}\" [shape=record, label=\"{node_name} \\n {in_} {out}| {node_text}\"]",
            ));
        }
        // Add edge statements
        for index in 0..total_number_of_nodes {
            let node_name = cfg.get_node_name(index);
            for successor_index in cfg.get_successor_indices(index) {
                let successor_name = cfg.get_node_name(*successor_index);
                statements.push(format!("\"{}\" -> \"{}\"", node_name, successor_name));
            }
        }
        println!("digraph{{{}}}", statements.join(";"))
    }

    fn merge(
        &self,
        accumulator: HashSet<ValueType>,
        new_value: &HashSet<ValueType>,
    ) -> HashSet<ValueType>;

    fn transfer(
        &self,
        cfg: &'a Cfg,
        index: NodeIndex,
        input: &HashSet<ValueType>,
    ) -> HashSet<ValueType>;
}

struct LiveVariableAnalysis {}

impl<'a> Analysis<'a, &'a str> for LiveVariableAnalysis {
    fn merge(
        &self,
        accumulator: HashSet<&'a str>,
        new_value: &HashSet<&'a str>,
    ) -> HashSet<&'a str> {
        accumulator.union(new_value).map(|a| *a).collect()
    }

    fn transfer(
        &self,
        cfg: &'a Cfg,
        node_index: NodeIndex,
        input: &HashSet<&'a str>,
    ) -> HashSet<&'a str> {
        let mut output = input.clone();
        let basic_block = cfg.get_basic_block(node_index);
        for instruction in basic_block.instruction_stream.iter().rev() {
            match instruction {
                bril_rs::Instruction::Constant {
                    dest,
                    op: _,
                    pos: _,
                    const_type: _,
                    value: _,
                } => {
                    output.remove(dest.as_str());
                }
                bril_rs::Instruction::Value {
                    args,
                    dest,
                    funcs: _,
                    labels: _,
                    op: _,
                    pos: _,
                    op_type: _,
                } => {
                    output.remove(dest.as_str());
                    args.iter().for_each(|arg| {
                        output.insert(&arg);
                    });
                }
                bril_rs::Instruction::Effect {
                    args,
                    funcs: _,
                    labels: _,
                    op: _,
                    pos: _,
                } => {
                    args.iter().for_each(|arg| {
                        output.insert(&arg);
                    });
                }
            }
        }
        return output;
    }
}

pub fn run_analysis(dataflow_analysis_name: DataflowAnalyses, program: &Program) -> () {
    program
        .functions
        .iter()
        .map(|f| Cfg::new(f))
        .for_each(|cfg| match dataflow_analysis_name {
            DataflowAnalyses::LiveVariable => {
                LiveVariableAnalysis {}.run(&cfg, HashSet::new(), Direction::Backward);
            }
        });
}
