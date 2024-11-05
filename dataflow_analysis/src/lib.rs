use bril_rs::Program;
use clap::ValueEnum;

#[derive(ValueEnum, Clone, Debug, PartialEq, Copy)]
pub enum DataflowAnalyses {
    LiveVariable,
}

pub fn run_analysis(dataflow_analysis_name: DataflowAnalyses, program: &Program) -> () {
    for (function_name, args, cfg) in program.functions.iter().map(|function| {
        let basic_blocks = common::construct_basic_block_stream(&function.instrs);
        let cfg = common::construct_cfg(&basic_blocks);
        (&function.name, &function.args, cfg)
    }) {
        println!("{}", function_name);
        println!("{}", cfg.get_dot_representation());
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {}
}
