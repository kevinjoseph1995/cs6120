use bril_rs::load_program;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let program = load_program();
    std::println!("{:#?}", program);
    Ok(())
}
