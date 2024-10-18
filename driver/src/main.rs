use std::{error::Error, io::Read};

use clap::Parser;
use optimizations::{apply_optimization, OptimizationPass};

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(short, long, value_name = "INPUT_BRILL_TEXT_FILE")]
    input_file: Option<String>,

    #[arg(long, value_enum)]
    optimizations: Vec<OptimizationPass>,
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
    for optimization in optimizations.iter() {
        apply_optimization(&mut program, optimization.clone());
    }

    Ok(())
}
