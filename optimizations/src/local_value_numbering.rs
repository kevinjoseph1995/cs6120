use std::{collections::HashMap, fmt::Display};

use bril_rs::{Code, Instruction, Program, ValueOps};
use common::BasicBlock;
use smallstr::SmallString;
use smallvec::{smallvec, SmallVec};

use crate::{LocalScopePass, Pass};

type InternalString = SmallString<[u8; 8]>;

#[derive(PartialEq, Debug, Clone)]
enum ValueGeneratingOp {
    Value(ValueOps),
    Const(bril_rs::Literal),
}

type TableIndex = usize;

#[derive(Debug, Clone)]
struct ValueTuple {
    operation: ValueGeneratingOp,
    operands: SmallVec<[TableIndex; 2]>, // Indices into the primary table referencing other entries.
}

#[derive(Clone, Debug)]
struct TableEntry {
    value_tuple: ValueTuple,
    variable_destinations: SmallVec<[InternalString; 2]>,
}

type Table = Vec<TableEntry>;

pub struct LocalValueNumberingPass {
    environment: HashMap<InternalString, TableIndex>,
    table: Table,
}

#[allow(dead_code)]
fn dump_table(table: &Table) {
    for entry in table {
        println!("{}", entry);
    }
}

impl Display for ValueTuple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.operation {
            ValueGeneratingOp::Value(value_ops) => write!(f, "{} ", value_ops)?,
            ValueGeneratingOp::Const(literal) => write!(f, "Const_{} ", literal)?,
        };

        for operand in &self.operands {
            write!(f, "{} ", operand)?;
        }
        Ok(())
    }
}

impl Display for TableEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.value_tuple)?;
        write!(f, "|")?;
        for dst in &self.variable_destinations {
            write!(f, "{} ", dst)?
        }
        Ok(())
    }
}

impl LocalScopePass for LocalValueNumberingPass {
    fn apply(&mut self, mut input_block: BasicBlock) -> BasicBlock {
        self.reset_state();
        input_block
            .instruction_stream
            .iter_mut()
            .map(|instr| match instr {
                Code::Label { label: _, pos: _ } => {
                    panic!("Invalid pre-condition; Found a unexpected label in basic block")
                }
                Code::Instruction(instruction) => instruction,
            })
            .for_each(|instruction| self.process_instruction(instruction));
        return input_block;
    }
}

impl Pass for LocalValueNumberingPass {
    fn apply(&mut self, program: bril_rs::Program) -> Program {
        return crate::apply_for_each_block(program, self);
    }
}

impl PartialEq for ValueTuple {
    fn eq(&self, other: &Self) -> bool {
        if self.operation != other.operation {
            return false;
        }
        let value_generating_operation = match &self.operation {
            ValueGeneratingOp::Value(value_op) => value_op,
            ValueGeneratingOp::Const(literal_value) => {
                // We don't need to check "other.operation" as the previous check would have failed if the underlying literals are not the same.
                assert!(matches!(
                    &other.operation,
                    ValueGeneratingOp::Const(x) if x == literal_value
                ));
                return true;
            }
        };
        match value_generating_operation {
            // Commutative operations
            ValueOps::Add
            | ValueOps::Mul
            | ValueOps::Eq
            | ValueOps::Not
            | ValueOps::And
            | ValueOps::Or
            | ValueOps::Fadd
            | ValueOps::Fmul
            | ValueOps::Feq => {
                assert!(self.operands.len() == 2);
                return (self.operands[0] == other.operands[0]
                    && self.operands[1] == other.operands[1])
                    || (self.operands[0] == other.operands[1]
                        && self.operands[1] == other.operands[0]);
            }
            // Non commutative operations
            ValueOps::Sub
            | ValueOps::Div
            | ValueOps::Lt
            | ValueOps::Gt
            | ValueOps::Le
            | ValueOps::Ge
            | ValueOps::Id
            | ValueOps::Call
            | ValueOps::Phi
            | ValueOps::Fsub
            | ValueOps::Fdiv
            | ValueOps::Flt
            | ValueOps::Fgt
            | ValueOps::Fle
            | ValueOps::Fge
            | ValueOps::Ceq
            | ValueOps::Clt
            | ValueOps::Cgt
            | ValueOps::Cle
            | ValueOps::Cge
            | ValueOps::Char2int
            | ValueOps::Int2char
            | ValueOps::Alloc
            | ValueOps::Load
            | ValueOps::PtrAdd => return self.operands.iter().eq(other.operands.iter()),
        }
    }
}

fn find_value_tuple_in_table<'a>(
    table: &'a Table,
    candidate: &ValueTuple,
) -> Option<(TableIndex, &'a TableEntry)> {
    table
        .iter()
        .enumerate()
        .find(|(_table_index, table_entry)| table_entry.value_tuple == *candidate)
}

impl LocalValueNumberingPass {
    pub fn new() -> Self {
        Self {
            environment: HashMap::new(),
            table: Table::new(),
        }
    }

    fn reset_state(&mut self) {
        self.environment.clear();
        self.table.clear();
    }

    fn get_value_tuple_and_destination(
        &self,
        instruction: &Instruction,
    ) -> (ValueTuple, InternalString) {
        match instruction {
            Instruction::Constant {
                dest,
                op: _,
                pos: _,
                const_type: _,
                value,
            } => (
                ValueTuple {
                    operation: ValueGeneratingOp::Const(value.clone()),
                    operands: smallvec![],
                },
                InternalString::from_str(&dest),
            ),
            Instruction::Value {
                args,
                dest,
                funcs: _,
                labels: _,
                op,
                pos: _,
                op_type: _,
            } => (
                ValueTuple {
                    operation: ValueGeneratingOp::Value(op.clone()),
                    operands: args
                        .iter()
                        .map(|arg_name| {
                            self.environment
                                .get(arg_name.as_str())
                                .expect("Expected to find argument in environment")
                                .clone()
                        })
                        .collect::<SmallVec<[TableIndex; 2]>>(),
                },
                InternalString::from_str(&dest),
            ),
            _ => panic!("Invalid precondition. Should not reach this branch"),
        }
    }

    fn process_instruction(&mut self, instruction: &mut Instruction) {
        if let Instruction::Effect {
            args: _,
            funcs: _,
            labels: _,
            op: _,
            pos: _,
        } = instruction
        {
            // Nothing to do this instruction does not produce a value
            return;
        }
        let (value_tuple, destination_variable) = self.get_value_tuple_and_destination(instruction);
        // Check if the value tuple is in the LVN table
        if let Some((table_index, table_entry)) =
            find_value_tuple_in_table(&self.table, &value_tuple)
        {
            self.environment
                .insert(destination_variable.clone(), table_index);
            let new_instruction = Instruction::Value {
                args: vec![table_entry.variable_destinations[0].to_string()],
                dest: destination_variable.to_string(),
                funcs: vec![],
                labels: vec![],
                op: ValueOps::Id,
                pos: None,
                op_type: match &instruction {
                    Instruction::Value {
                        args: _,
                        dest: _,
                        funcs: _,
                        labels: _,
                        op: _,
                        pos: _,
                        op_type,
                    } => op_type.clone(),
                    _ => panic!(),
                },
            };
            *instruction = new_instruction;
        } else {
            // New value computation
            self.table.push(TableEntry {
                value_tuple,
                variable_destinations: smallvec![destination_variable.clone()],
            });
            self.environment
                .insert(destination_variable, self.table.len() - 1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smallvec::smallvec;

    #[test]
    fn test_value_tuple_eq() {
        let tuple1: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Const(bril_rs::Literal::Float(1.5)),
            operands: smallvec![],
        };
        let tuple2: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Const(bril_rs::Literal::Float(1.5)),
            operands: smallvec![],
        };
        assert_eq!(tuple1, tuple2);
        let tuple1: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Value(ValueOps::Add),
            operands: smallvec![0, 2],
        };
        let tuple2: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Value(ValueOps::Add),
            operands: smallvec![2, 0],
        };
        assert_eq!(tuple1, tuple2);
        let tuple1: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Value(ValueOps::Add),
            operands: smallvec![0, 2],
        };
        let tuple2: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Value(ValueOps::Add),
            operands: smallvec![1, 3],
        };
        assert_ne!(tuple1, tuple2);
        let tuple1: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Value(ValueOps::Sub),
            operands: smallvec![1, 2],
        };
        let tuple2: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Value(ValueOps::Sub),
            operands: smallvec![2, 1],
        };
        assert_ne!(tuple1, tuple2);
        let tuple1: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Value(ValueOps::Add),
            operands: smallvec![1, 2],
        };
        let tuple2: ValueTuple = ValueTuple {
            operation: ValueGeneratingOp::Value(ValueOps::Sub),
            operands: smallvec![1, 2],
        };
        assert_ne!(tuple1, tuple2);
    }

    #[test]
    fn test_local_lvn_1() {
        const BRIL_PROGRAM_TEXT: &'static str = indoc::indoc! {r#"
            @main() {
                a: int = const 1;
                b: int = const 2;
                c: int = add a b;
                b: int = const 3;
                d: int = add a b;
                print d;
            }
        "#};
        let program = common::parse_bril_text(&BRIL_PROGRAM_TEXT);
        assert!(program.is_ok());
        let program = program.unwrap();
        let mut manager = LocalValueNumberingPass::new();
        let program = Pass::apply(&mut manager, program);
        println!("\n\n{}", program);
    }

    #[test]
    fn test_local_lvn_2() {
        const BRIL_PROGRAM_TEXT: &'static str = indoc::indoc! {r#"
            @main() {
                a: int = const 1;
                b: int = id a;
                c: int = add a b;
                print c;
            }
        "#};
        let program = common::parse_bril_text(&BRIL_PROGRAM_TEXT);
        assert!(program.is_ok());
        let program = program.unwrap();
        let mut manager = LocalValueNumberingPass::new();
        let program = Pass::apply(&mut manager, program);
        println!("\n\n{}", program);
    }
}
