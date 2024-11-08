use bril_rs::Program;
use clap::ValueEnum;

#[derive(ValueEnum, Clone, Debug, PartialEq, Copy)]
pub enum DataflowAnalyses {
    LiveVariable,
}

pub fn run_analysis(dataflow_analysis_name: DataflowAnalyses, program: &Program) -> () {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {}
}
