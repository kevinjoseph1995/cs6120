use core::panic;
use std::{collections::HashMap, fmt::Display, usize};

use bril_rs::{ConstOps, Instruction, Literal, Program, ValueOps};
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
    constant_map: HashMap<InternalString, Literal>,
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
            constant_map: HashMap::new(),
        }
    }

    fn reset_state(&mut self) {
        self.environment.clear();
        self.table.clear();
        self.constant_map.clear();
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

    fn process_undefined_arguments(&mut self, instruction: &Instruction) {
        let args = match instruction {
            Instruction::Constant {
                dest: _,
                op: _,
                pos: _,
                const_type: _,
                value: _,
            } => &[],
            Instruction::Value {
                args,
                dest: _,
                funcs: _,
                labels: _,
                op: _,
                pos: _,
                op_type: _,
            } => args.as_slice(),
            Instruction::Effect {
                args,
                funcs: _,
                labels: _,
                op: _,
                pos: _,
            } => args.as_slice(),
        };
        for arg in args {
            if !self.environment.contains_key(arg.as_str()) {
                self.environment
                    .insert(arg.clone().try_into().unwrap(), usize::MAX);
                self.table.push(TableEntry {
                    value_tuple: self
                        .get_value_tuple_and_destination(&Instruction::Value {
                            args: vec![arg.clone()],
                            dest: arg.clone(),
                            funcs: Vec::new(),
                            labels: Vec::new(),
                            op: ValueOps::Id,
                            pos: None,
                            op_type: bril_rs::Type::Bool, // This is incorrect
                        })
                        .0,
                    variable_destinations: smallvec![InternalString::from_str(arg.as_str())],
                });
                *(self.environment.get_mut(arg.as_str()).unwrap()) = self.table.len() - 1;
            }
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
        self.process_undefined_arguments(instruction);
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
                    Instruction::Constant {
                        dest: _,
                        op: _,
                        pos: _,
                        const_type,
                        value: _,
                    } => const_type.clone(),
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

        self.constant_fold(instruction);
    }

    fn constant_fold(&mut self, instruction: &mut Instruction) {
        if let Instruction::Constant {
            dest,
            op: _,
            pos: _,
            const_type: _,
            value,
        } = instruction
        {
            // Bind variable to the latest constant that's being assigned to it
            self.constant_map
                .insert(InternalString::from_str(dest.as_str()), value.clone());
            return;
        }
        // Check if we can produce a new constant instruction if the arguments to the current value producing instruction are all constants
        let new_instruction: Option<Instruction> = self.generate_constant_instruction(instruction);

        if let Some(new_instruction) = new_instruction {
            *instruction = new_instruction;
        }
    }

    fn generate_constant_instruction(&mut self, instruction: &Instruction) -> Option<Instruction> {
        let (args, dest, op, op_type) = match instruction {
            Instruction::Value {
                args,
                dest,
                funcs: _,
                labels: _,
                op,
                pos: _,
                op_type,
            } => (args, dest, op, op_type),
            _ => panic!("Unexpected branch"),
        };

        if *op == ValueOps::Call {
            return None;
        }

        let const_args = {
            let mut const_args: SmallVec<[Literal; 2]> = SmallVec::new();
            for arg in args {
                if let Some(literal) = self.constant_map.get(arg.as_str()) {
                    const_args.push(literal.clone());
                } else {
                    // Argument cannot be reduced to a constant:_
                    return None;
                }
            }
            const_args
        };

        let new_const_literal: Literal = match op {
            ValueOps::Add => {
                assert!(const_args.len() == 2);
                if let (Literal::Int(value1), Literal::Int(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Int(value1 + value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Sub => {
                assert!(const_args.len() == 2);
                if let (Literal::Int(value1), Literal::Int(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Int(value1 - value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Mul => {
                assert!(const_args.len() == 2);
                if let (Literal::Int(value1), Literal::Int(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Int(value1 * value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Div => {
                assert!(const_args.len() == 2);
                if let (Literal::Int(value1), Literal::Int(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Int(value1 / value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Eq => {
                assert!(const_args.len() == 2);
                match (&const_args[0], &const_args[1]) {
                    (Literal::Int(v1), Literal::Int(v2)) => Literal::Bool(v1 == v2),
                    (Literal::Bool(v1), Literal::Bool(v2)) => Literal::Bool(v1 == v2),
                    (Literal::Float(v1), Literal::Float(v2)) => Literal::Bool(v1 == v2),
                    (Literal::Char(v1), Literal::Char(v2)) => Literal::Bool(v1 == v2),
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Lt => {
                assert!(const_args.len() == 2);
                match (&const_args[0], &const_args[1]) {
                    (Literal::Int(value1), Literal::Int(value2)) => Literal::Bool(value1 < value2),
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Gt => {
                assert!(const_args.len() == 2);
                match (&const_args[0], &const_args[1]) {
                    (Literal::Int(value1), Literal::Int(value2)) => Literal::Bool(value1 > value2),
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Le => {
                assert!(const_args.len() == 2);
                match (&const_args[0], &const_args[1]) {
                    (Literal::Int(value1), Literal::Int(value2)) => Literal::Bool(value1 <= value2),
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Ge => {
                assert!(const_args.len() == 2);
                match (&const_args[0], &const_args[1]) {
                    (Literal::Int(value1), Literal::Int(value2)) => Literal::Bool(value1 >= value2),
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Not => {
                assert!(const_args.len() == 1);
                match const_args[0] {
                    Literal::Bool(val) => Literal::Bool(!val),
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::And => {
                assert!(const_args.len() == 2);
                match (&const_args[0], &const_args[1]) {
                    (Literal::Bool(value1), Literal::Bool(value2)) => {
                        Literal::Bool(*value1 && *value2)
                    }
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Or => {
                assert!(const_args.len() == 2);
                match (&const_args[0], &const_args[1]) {
                    (Literal::Bool(value1), Literal::Bool(value2)) => {
                        Literal::Bool(*value1 || *value2)
                    }
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Id => {
                assert!(const_args.len() == 1);
                const_args[0].clone()
            }
            ValueOps::Char2int => {
                assert!(const_args.len() == 1);
                match &const_args[0] {
                    Literal::Char(c) => Literal::Int(u32::from(*c).into()),
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Int2char => {
                assert!(const_args.len() == 1);
                match &const_args[0] {
                    Literal::Int(value) => {
                        Literal::Char(u32::try_from(*value).ok().and_then(char::from_u32).unwrap())
                    }
                    _ => panic!("Unreachable branch"),
                }
            }
            ValueOps::Fadd => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Float(value1 + value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Fsub => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Float(value1 - value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Fmul => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Float(value1 * value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Fdiv => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Float(value1 / value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Feq => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 == value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Flt => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 < value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Fgt => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 > value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Fle => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 <= value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Fge => {
                assert!(const_args.len() == 2);
                if let (Literal::Float(value1), Literal::Float(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 >= value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Ceq => {
                assert!(const_args.len() == 2);
                if let (Literal::Char(value1), Literal::Char(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 == value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Clt => {
                assert!(const_args.len() == 2);
                if let (Literal::Char(value1), Literal::Char(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 < value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Cgt => {
                assert!(const_args.len() == 2);
                if let (Literal::Char(value1), Literal::Char(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 > value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Cle => {
                assert!(const_args.len() == 2);
                if let (Literal::Char(value1), Literal::Char(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 <= value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::Cge => {
                assert!(const_args.len() == 2);
                if let (Literal::Char(value1), Literal::Char(value2)) =
                    (&const_args[0], &const_args[1])
                {
                    Literal::Bool(value1 >= value2)
                } else {
                    panic!("Unreachable branch");
                }
            }
            ValueOps::PtrAdd => panic!("Unreachable branch"),
            ValueOps::Call => panic!("Unreachable branch"),
            ValueOps::Alloc => todo!(),
            ValueOps::Load => todo!(),
            ValueOps::Phi => todo!(),
        };
        // Update the constant map
        self.constant_map.insert(
            SmallString::from_str(dest.as_str()),
            new_const_literal.clone(),
        );
        return Some(Instruction::Constant {
            dest: dest.clone(),
            op: ConstOps::Const,
            pos: None,
            const_type: op_type.clone(),
            value: new_const_literal,
        });
    }
}

#[cfg(test)]
mod tests {
    use core::str;

    use super::*;
    use brilirs::{basic_block::BBProgram, check, interp};
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

    fn parse_program(text: &str) -> Program {
        let program = common::parse_bril_text(text);
        assert!(program.is_ok(), "{}", program.err().unwrap());
        program.unwrap()
    }

    #[test]
    fn test_local_lvn_no_redundant_computation_1() {
        let program = parse_program(indoc::indoc! {r#"
            @main() {
                a: int = const 1;
                b: int = const 2;
                c: int = add a b;
                b: int = const 3;
                d: int = add a b;
                print d;
            }
        "#});
        let mut manager = LocalValueNumberingPass::new();
        let program = Pass::apply(&mut manager, program);
        let bbprog: BBProgram = program.try_into().expect("Invalid program");
        assert!(check::type_check(&bbprog).is_ok());
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        assert!(interp::execute_main(&bbprog, &mut stdout, &[], true, &mut stderr).is_ok());
        assert!(
            String::from_utf8(stdout).unwrap() == "4\n",
            "Error={}",
            String::from_utf8(stderr).unwrap()
        );
    }

    #[test]
    fn test_local_lvn_no_redundant_computation_2() {
        let program = parse_program(indoc::indoc! {r#"
           @main() {
                a: int = const 1;
                b: int = id a;
                c: int = add a b;
                print c;
            }
        "#});
        let mut manager = LocalValueNumberingPass::new();
        let program = Pass::apply(&mut manager, program);
        let bbprog: BBProgram = program.try_into().expect("Invalid program");
        assert!(check::type_check(&bbprog).is_ok());
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        assert!(interp::execute_main(&bbprog, &mut stdout, &[], true, &mut stderr).is_ok());
        assert!(
            String::from_utf8(stdout).unwrap() == "2\n",
            "Error={}",
            String::from_utf8(stderr).unwrap()
        );
    }

    #[test]
    fn test_local_lvn_3() {
        let program = parse_program(indoc::indoc! {r#"
            @main() {
                a: int = const 1;
                b: int = id a;
                c: int = add a b;
                x: int = id a;
                y: int = id a;
                z: int = id a;
                d: int = add a b;
                print d;
            }
        "#});
        let mut manager = LocalValueNumberingPass::new();
        let program = Pass::apply(&mut manager, program);
        let bbprog: BBProgram = program.try_into().expect("Invalid program");
        assert!(check::type_check(&bbprog).is_ok());
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        assert!(interp::execute_main(&bbprog, &mut stdout, &[], true, &mut stderr).is_ok());
        assert!(
            String::from_utf8(stdout).unwrap() == "2\n",
            "Error={}",
            String::from_utf8(stderr).unwrap()
        );
    }

    #[test]
    fn test_local_lvn_4() {
        let program = parse_program(indoc::indoc! {r#"
            @main(a: int, b:int) {
                c: int = add a b;
                d: int = add a b;
                e: int = add c d;
                print e;
            }
        "#});
        let mut manager = LocalValueNumberingPass::new();
        let program = Pass::apply(&mut manager, program);
        let bbprog: BBProgram = program.try_into().expect("Invalid program");
        assert!(check::type_check(&bbprog).is_ok());
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        assert!(interp::execute_main(
            &bbprog,
            &mut stdout,
            &["1".to_string(), "2".to_string()],
            true,
            &mut stderr
        )
        .is_ok());
        assert!(
            String::from_utf8(stdout).unwrap() == "6\n",
            "Error={}",
            String::from_utf8(stderr).unwrap()
        );
    }

    #[test]
    fn test_local_lvn_5() {
        let program = parse_program(indoc::indoc! {r#"
            @main {
                a: int = const 4;
                b: int = const 6;
                c: int = add a b;
            jmp .somewhere;
            .somewhere:
                d: int = add a b;
                print c;
            }
        "#});
        let mut manager = LocalValueNumberingPass::new();
        let program = Pass::apply(&mut manager, program);
        let bbprog: BBProgram = program.try_into().expect("Invalid program");
        assert!(check::type_check(&bbprog).is_ok());
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        assert!(interp::execute_main(&bbprog, &mut stdout, &[], true, &mut stderr).is_ok());
        assert!(
            String::from_utf8(stdout).unwrap() == "10\n",
            "Error={}",
            String::from_utf8(stderr).unwrap()
        );
    }

    #[test]
    fn test_local_lvn_6() {
        let program = parse_program(indoc::indoc! {r#"
            @main {
            v1: int = const 1;
            v2: int = const 0;
            counter: int = const 0;

            .loop_start:
            v7: int = id counter;
            v8: int = const 99;
            v9: bool = lt v7 v8;
            br v9 .loop_body .loop_end;

            .loop_body:
            v3: bool = eq v1 v2;  # Always false
            br v3 .then .else;  # .then is a dead branch - this br instruction can be optimized out by a smart compiler

            .then:
            v4: int = const 100;
            print v4;

            .else:
            v4: int = const 50;

            v10: int = id counter;
            v11: int = const 1;
            v12: int = add v10 v11;
            counter: int = id v12;

            jmp .loop_start;

            .loop_end:
            print v4;
            }
        "#});
        let mut manager = LocalValueNumberingPass::new();
        let program = Pass::apply(&mut manager, program);
        println!("{}", program);
        let bbprog: BBProgram = program.try_into().expect("Invalid program");
        // TODO: The following should compile but there seems to be a bug in check::type_check
        // let type_check_result = check::type_check(&bbprog);
        // assert!(
        //     type_check_result.is_ok(),
        //     "Type-check error= {}",
        //     type_check_result.err().unwrap()
        // );
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        assert!(interp::execute_main(&bbprog, &mut stdout, &[], true, &mut stderr).is_ok());
        assert!(
            String::from_utf8(stdout).unwrap() == "50\n",
            "Error={}",
            String::from_utf8(stderr).unwrap()
        );
    }
}
