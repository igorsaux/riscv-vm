use crate::registers::Register;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionR {
    pub rd: Register,
    pub rs1: Register,
    pub rs2: Register,
}

impl InstructionR {
    pub const fn new(rd: Register, rs1: Register, rs2: Register) -> Self {
        Self { rd, rs1, rs2 }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionI {
    pub rd: Register,
    pub rs1: Register,
    pub imm: i16,
}

impl InstructionI {
    pub const fn new(rd: Register, rs1: Register, imm: i16) -> Self {
        Self { rd, rs1, imm }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionIAlt {
    pub rd: Register,
    pub rs1: Register,
    pub imm: u8,
}

impl InstructionIAlt {
    pub const fn new(rd: Register, rs1: Register, imm: u8) -> Self {
        Self { rd, rs1, imm }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionS {
    pub rs1: Register,
    pub rs2: Register,
    pub imm: i16,
}

impl InstructionS {
    pub const fn new(rs1: Register, rs2: Register, imm: i16) -> Self {
        Self { rs1, rs2, imm }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionB {
    pub rs1: Register,
    pub rs2: Register,
    pub imm: i16,
}

impl InstructionB {
    pub const fn new(rs1: Register, rs2: Register, imm: i16) -> Self {
        Self { rs1, rs2, imm }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionU {
    pub rd: Register,
    pub imm: i32,
}

impl InstructionU {
    pub const fn new(rd: Register, imm: i32) -> Self {
        Self { rd, imm }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionJ {
    pub rd: Register,
    pub imm: i32,
}

impl InstructionJ {
    pub const fn new(rd: Register, imm: i32) -> Self {
        Self { rd, imm }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionFence {
    pub rd: Register,
    pub rs1: Register,
    pub succ: u8,
    pub pred: u8,
    pub fm: u8,
}

impl InstructionFence {
    pub const fn new(rd: Register, rs1: Register, succ: u8, pred: u8, fm: u8) -> Self {
        Self {
            rd,
            rs1,
            succ,
            pred,
            fm,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Instruction {
    LUI(InstructionU),
    AUIPC(InstructionU),
    JAL(InstructionJ),
    JALR(InstructionI),
    BEQ(InstructionB),
    BNE(InstructionB),
    BLT(InstructionB),
    BGE(InstructionB),
    BLTU(InstructionB),
    BGEU(InstructionB),
    LB(InstructionI),
    LH(InstructionI),
    LW(InstructionI),
    LBU(InstructionI),
    LHU(InstructionI),
    SB(InstructionS),
    SH(InstructionS),
    SW(InstructionS),
    ADDI(InstructionI),
    SLTI(InstructionI),
    SLTIU(InstructionI),
    XORI(InstructionI),
    ORI(InstructionI),
    ANDI(InstructionI),
    SLLI(InstructionIAlt),
    SRLI(InstructionIAlt),
    SRAI(InstructionIAlt),
    ADD(InstructionR),
    SUB(InstructionR),
    SLL(InstructionR),
    SLT(InstructionR),
    SLTU(InstructionR),
    XOR(InstructionR),
    SRL(InstructionR),
    SRA(InstructionR),
    OR(InstructionR),
    AND(InstructionR),
    FENCE(InstructionFence),
    ECALL,
    EBREAK,
}
