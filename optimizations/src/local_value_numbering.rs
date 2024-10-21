use common::BasicBlock;



fn local_value_numbering(block: &BasicBlock) -> BasicBlock {
    todo!()
}


pub fn apply(program: &mut bril_rs::Program) {
   crate::apply_for_each_block(program, local_value_numbering);
}