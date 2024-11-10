use std::{error::Error, io::Read};

use clap::Parser;
use dataflow_analysis::DataflowAnalyses;
use optimizations::{OptimizationPass, PassManager};

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(short, long, value_name = "INPUT_BRILL_TEXT_FILE")]
    input_file: Option<String>,

    #[arg(long, value_enum)]
    optimizations: Vec<OptimizationPass>,

    #[arg(short, long, value_enum, help = "Type of dataflow analysis to run")]
    dataflow_analysis: Option<DataflowAnalyses>,

    #[arg(long, help = "Dump the AST as a DOT file")]
    dump_ast_as_dot: bool,

    #[arg(long, help = "Output the program after optimizations")]
    output_program: bool,
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();
    let program_text_raw_bytes = {
        if let Some(filepath) = args.input_file {
            let file_contents = std::fs::read(filepath)?;
            file_contents
        } else {
            let mut stdio = std::io::stdin();
            let mut buffer: Vec<u8> = Vec::new();
            let _ = stdio.read_to_end(&mut buffer)?;
            buffer
        }
    };

    let mut program = match std::str::from_utf8(&program_text_raw_bytes) {
        Ok(valid_utf8) => common::parse_bril_text(valid_utf8)?,
        Err(error) => return Err(Box::new(error)),
    };

    let mut optimizations = args.optimizations;
    optimizations.dedup_by(|a, b| a == b);
    let mut pass_manager = PassManager::new();
    for optimization in optimizations.iter() {
        pass_manager.register_pass(*optimization);
    }
    program = pass_manager.run(program);
    if let Some(dataflow_analysis_name) = args.dataflow_analysis {
        dataflow_analysis::run_analysis(dataflow_analysis_name, &program);
    }
    if args.dump_ast_as_dot {
        println!("DOT representation of the CFG's of the program functions");
        for function in &program.functions {
            println!(
                "{}\n {}",
                function.name,
                common::cfg::get_dot_representation(&common::cfg::Cfg::new(function))
            );
            println!("=========================================================");
        }
    }
    if args.output_program {
        println!("Program{}", program);
    }
    Ok(())
}
