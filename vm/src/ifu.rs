use crate::{
    isa::{
        Instruction, InstructionB, InstructionFence, InstructionI, InstructionIAlt,
        InstructionICSR, InstructionICSRImm, InstructionJ, InstructionR, InstructionS,
        InstructionU,
    },
    mmu::MMUError,
    registers::Register,
};
use thiserror::Error;

#[derive(Debug, Clone, Error, PartialEq)]
pub enum IFUError {
    #[error(transparent)]
    MMUError(#[from] MMUError),
    #[error("Unknown instruction '0x{instruction:0X}'")]
    UnknownInstruction { instruction: i32 },
    #[error("Invalid register at {index} in '0x{instruction:0X}'")]
    InvalidRegister { index: u8, instruction: i32 },
}

const fn cut_move(value: i32, len: usize, pos: usize, target_pos: usize) -> i32 {
    let xlen = std::mem::size_of::<i32>() * 8;
    let mut result;

    let sl = xlen - len - pos;

    if sl > 0 {
        result = value << sl;
    } else {
        result = value;
    }

    let sr = xlen - len;

    if sr > 0 {
        result >>= sr;
    }

    if target_pos > 0 {
        result <<= target_pos;
    }

    result
}

const fn fetch_funct3(instruction: i32) -> i32 {
    (instruction >> 12) & 0b111
}

const fn fetch_funct7(instruction: i32) -> i32 {
    instruction >> 25
}

const fn fetch_rd(instruction: i32) -> Option<Register> {
    let value = ((instruction >> 7) & 0b11111) as u8;

    Register::new(value)
}

const fn fetch_rs1(instruction: i32) -> Option<Register> {
    let value = ((instruction >> 15) & 0b11111) as u8;

    Register::new(value)
}

const fn fetch_rs1_uimm(instruction: i32) -> u8 {
    ((instruction >> 15) & 0b11111) as u8
}

const fn fetch_rs2(instruction: i32) -> Option<Register> {
    let value = ((instruction >> 20) & 0b11111) as u8;

    Register::new(value)
}

const fn fetch_imm_i(instruction: i32) -> i16 {
    cut_move(instruction, 12, 20, 0) as i16
}

const fn fetch_imm_s(instruction: i32) -> i16 {
    // [4:0]
    let mut result = cut_move(instruction, 5, 7, 0);
    // [11:5]
    result |= cut_move(instruction, 7, 25, 5);

    result as i16
}

const fn fetch_imm_b(instruction: i32) -> i16 {
    // [4:1]
    let mut result = cut_move(instruction, 4, 8, 1);
    // [10:5]
    result |= cut_move(instruction, 6, 25, 5);
    // [11]
    result |= cut_move(instruction, 1, 7, 11);
    // [12]
    result |= cut_move(instruction, 1, 31, 12);

    result as i16
}

const fn fetch_imm_u(instruction: i32) -> i32 {
    cut_move(instruction, 20, 12, 12)
}

const fn fetch_imm_j(instruction: i32) -> i32 {
    // [10:1]
    let mut result = cut_move(instruction, 10, 21, 1);
    // [11]
    result |= cut_move(instruction, 1, 20, 11);
    // [19:12]
    result |= cut_move(instruction, 8, 12, 12);
    // [20]
    result |= cut_move(instruction, 1, 30, 20);

    result
}

fn fetch_instruction_r(instruction: i32) -> Result<InstructionR, IFUError> {
    let rd = fetch_rd(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let rs1 = fetch_rs1(instruction).ok_or(IFUError::InvalidRegister {
        index: 2,
        instruction,
    })?;
    let rs2 = fetch_rs2(instruction).ok_or(IFUError::InvalidRegister {
        index: 3,
        instruction,
    })?;

    Ok(InstructionR::new(rd, rs1, rs2))
}

fn fetch_instruction_i(instruction: i32) -> Result<InstructionI, IFUError> {
    let rd = fetch_rd(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let rs1 = fetch_rs1(instruction).ok_or(IFUError::InvalidRegister {
        index: 2,
        instruction,
    })?;
    let imm = fetch_imm_i(instruction);

    Ok(InstructionI::new(rd, rs1, imm))
}

fn fetch_instruction_i_alt(instruction: i32) -> Result<InstructionIAlt, IFUError> {
    let rd = fetch_rd(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let rs1 = fetch_rs1(instruction).ok_or(IFUError::InvalidRegister {
        index: 2,
        instruction,
    })?;
    let shamt = ((instruction >> 20) & 0b11111) as u8;

    Ok(InstructionIAlt::new(rd, rs1, shamt))
}

fn fetch_instruction_i_csr(instruction: i32) -> Result<InstructionICSR, IFUError> {
    let rd = fetch_rd(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let rs1 = fetch_rs1(instruction).ok_or(IFUError::InvalidRegister {
        index: 2,
        instruction,
    })?;
    let csr = fetch_imm_i(instruction) as u16;

    Ok(InstructionICSR::new(rd, rs1, csr))
}

fn fetch_instruction_i_csr_imm(instruction: i32) -> Result<InstructionICSRImm, IFUError> {
    let rd = fetch_rd(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let imm = fetch_rs1_uimm(instruction);
    let csr = fetch_imm_i(instruction) as u16;

    Ok(InstructionICSRImm::new(rd, imm, csr))
}

fn fetch_instruction_s(instruction: i32) -> Result<InstructionS, IFUError> {
    let rs1 = fetch_rs1(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let rs2 = fetch_rs2(instruction).ok_or(IFUError::InvalidRegister {
        index: 2,
        instruction,
    })?;
    let imm = fetch_imm_s(instruction);

    Ok(InstructionS::new(rs1, rs2, imm))
}

fn fetch_instruction_b(instruction: i32) -> Result<InstructionB, IFUError> {
    let rs1 = fetch_rs1(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let rs2 = fetch_rs2(instruction).ok_or(IFUError::InvalidRegister {
        index: 2,
        instruction,
    })?;
    let imm = fetch_imm_b(instruction);

    Ok(InstructionB::new(rs1, rs2, imm))
}

fn fetch_instruction_u(instruction: i32) -> Result<InstructionU, IFUError> {
    let rd = fetch_rd(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let imm = fetch_imm_u(instruction);

    Ok(InstructionU::new(rd, imm))
}

fn fetch_instruction_j(instruction: i32) -> Result<InstructionJ, IFUError> {
    let rd = fetch_rd(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let imm = fetch_imm_j(instruction);

    Ok(InstructionJ::new(rd, imm))
}

fn fetch_instruction_fence(instruction: i32) -> Result<InstructionFence, IFUError> {
    let rd = fetch_rd(instruction).ok_or(IFUError::InvalidRegister {
        index: 1,
        instruction,
    })?;
    let rs1 = fetch_rs1(instruction).ok_or(IFUError::InvalidRegister {
        index: 2,
        instruction,
    })?;

    let succ = ((instruction >> 20) & 0b1111) as u8;
    let pred = ((instruction >> 24) & 0b1111) as u8;
    let fm = (instruction >> 28) as u8;

    Ok(InstructionFence::new(rd, rs1, succ, pred, fm))
}

#[derive(Debug, Clone)]
pub struct IFU;

impl IFU {
    pub fn fetch(&mut self, instruction: i32) -> Result<Instruction, IFUError> {
        let opcode = instruction & 0b111_1111;

        match opcode {
            0b0110111 => Ok(Instruction::LUI(fetch_instruction_u(instruction)?)),
            0b0010111 => Ok(Instruction::AUIPC(fetch_instruction_u(instruction)?)),
            0b1101111 => Ok(Instruction::JAL(fetch_instruction_j(instruction)?)),
            0b1100111 => {
                let funct3 = fetch_funct3(instruction);

                match funct3 {
                    0b000 => Ok(Instruction::JALR(fetch_instruction_i(instruction)?)),
                    _ => Err(IFUError::UnknownInstruction { instruction }),
                }
            }
            0b1100011 => {
                let funct3 = fetch_funct3(instruction);

                match funct3 {
                    0b000 => Ok(Instruction::BEQ(fetch_instruction_b(instruction)?)),
                    0b001 => Ok(Instruction::BNE(fetch_instruction_b(instruction)?)),
                    0b100 => Ok(Instruction::BLT(fetch_instruction_b(instruction)?)),
                    0b101 => Ok(Instruction::BGE(fetch_instruction_b(instruction)?)),
                    0b110 => Ok(Instruction::BLTU(fetch_instruction_b(instruction)?)),
                    0b111 => Ok(Instruction::BGEU(fetch_instruction_b(instruction)?)),
                    _ => Err(IFUError::UnknownInstruction { instruction }),
                }
            }
            0b0000011 => {
                let funct3 = fetch_funct3(instruction);

                match funct3 {
                    0b000 => Ok(Instruction::LB(fetch_instruction_i(instruction)?)),
                    0b001 => Ok(Instruction::LH(fetch_instruction_i(instruction)?)),
                    0b010 => Ok(Instruction::LW(fetch_instruction_i(instruction)?)),
                    0b100 => Ok(Instruction::LBU(fetch_instruction_i(instruction)?)),
                    0b101 => Ok(Instruction::LHU(fetch_instruction_i(instruction)?)),
                    _ => Err(IFUError::UnknownInstruction { instruction }),
                }
            }
            0b0100011 => {
                let funct3 = fetch_funct3(instruction);

                match funct3 {
                    0b000 => Ok(Instruction::SB(fetch_instruction_s(instruction)?)),
                    0b001 => Ok(Instruction::SH(fetch_instruction_s(instruction)?)),
                    0b010 => Ok(Instruction::SW(fetch_instruction_s(instruction)?)),
                    _ => Err(IFUError::UnknownInstruction { instruction }),
                }
            }
            0b0010011 => {
                let funct3 = fetch_funct3(instruction);
                let funct7 = fetch_funct7(instruction);

                match (funct7, funct3) {
                    (_, 0b000) => Ok(Instruction::ADDI(fetch_instruction_i(instruction)?)),
                    (_, 0b010) => Ok(Instruction::SLTI(fetch_instruction_i(instruction)?)),
                    (_, 0b011) => Ok(Instruction::SLTIU(fetch_instruction_i(instruction)?)),
                    (_, 0b100) => Ok(Instruction::XORI(fetch_instruction_i(instruction)?)),
                    (_, 0b110) => Ok(Instruction::ORI(fetch_instruction_i(instruction)?)),
                    (_, 0b111) => Ok(Instruction::ANDI(fetch_instruction_i(instruction)?)),
                    (0b0000000, 0b001) => {
                        Ok(Instruction::SLLI(fetch_instruction_i_alt(instruction)?))
                    }
                    (0b0000000, 0b101) => {
                        Ok(Instruction::SRLI(fetch_instruction_i_alt(instruction)?))
                    }
                    (0b0100000, 0b101) => {
                        Ok(Instruction::SRAI(fetch_instruction_i_alt(instruction)?))
                    }
                    _ => Err(IFUError::UnknownInstruction { instruction }),
                }
            }
            0b0110011 => {
                let funct3 = fetch_funct3(instruction);
                let funct7 = fetch_funct7(instruction);

                match (funct7, funct3) {
                    (0b0000000, 0b000) => Ok(Instruction::ADD(fetch_instruction_r(instruction)?)),
                    (0b0100000, 0b000) => Ok(Instruction::SUB(fetch_instruction_r(instruction)?)),
                    (0b0000000, 0b001) => Ok(Instruction::SLL(fetch_instruction_r(instruction)?)),
                    (0b0000000, 0b010) => Ok(Instruction::SLT(fetch_instruction_r(instruction)?)),
                    (0b0000000, 0b011) => Ok(Instruction::SLTU(fetch_instruction_r(instruction)?)),
                    (0b0000000, 0b100) => Ok(Instruction::XOR(fetch_instruction_r(instruction)?)),
                    (0b0000000, 0b101) => Ok(Instruction::SRL(fetch_instruction_r(instruction)?)),
                    (0b0100000, 0b101) => Ok(Instruction::SRA(fetch_instruction_r(instruction)?)),
                    (0b0000000, 0b110) => Ok(Instruction::OR(fetch_instruction_r(instruction)?)),
                    (0b0000000, 0b111) => Ok(Instruction::AND(fetch_instruction_r(instruction)?)),
                    // M Extension
                    (0b0000001, 0b000) => Ok(Instruction::MUL(fetch_instruction_r(instruction)?)),
                    (0b0000001, 0b001) => Ok(Instruction::MULH(fetch_instruction_r(instruction)?)),
                    (0b0000001, 0b010) => {
                        Ok(Instruction::MULHSU(fetch_instruction_r(instruction)?))
                    }
                    (0b0000001, 0b011) => Ok(Instruction::MULHU(fetch_instruction_r(instruction)?)),
                    (0b0000001, 0b100) => Ok(Instruction::DIV(fetch_instruction_r(instruction)?)),
                    (0b0000001, 0b101) => Ok(Instruction::DIVU(fetch_instruction_r(instruction)?)),
                    (0b0000001, 0b110) => Ok(Instruction::REM(fetch_instruction_r(instruction)?)),
                    (0b0000001, 0b111) => Ok(Instruction::REMU(fetch_instruction_r(instruction)?)),
                    // None
                    _ => Err(IFUError::UnknownInstruction { instruction }),
                }
            }
            0b0001111 => Ok(Instruction::FENCE(fetch_instruction_fence(instruction)?)),
            0b1110011 => {
                let imm = fetch_imm_i(instruction);
                let funct3 = fetch_funct3(instruction);

                match (imm, funct3) {
                    (0b000000000000, 0b000) => Ok(Instruction::ECALL),
                    (0b000000000001, 0b000) => Ok(Instruction::EBREAK),
                    (_, 0b001) => Ok(Instruction::CSRRW(fetch_instruction_i_csr(instruction)?)),
                    (_, 0b010) => Ok(Instruction::CSRRS(fetch_instruction_i_csr(instruction)?)),
                    (_, 0b011) => Ok(Instruction::CSRRC(fetch_instruction_i_csr(instruction)?)),
                    (_, 0b101) => Ok(Instruction::CSRRWI(fetch_instruction_i_csr_imm(
                        instruction,
                    )?)),
                    (_, 0b110) => Ok(Instruction::CSRRSI(fetch_instruction_i_csr_imm(
                        instruction,
                    )?)),
                    (_, 0b111) => Ok(Instruction::CSRRCI(fetch_instruction_i_csr_imm(
                        instruction,
                    )?)),
                    _ => Err(IFUError::UnknownInstruction { instruction }),
                }
            }
            _ => Err(IFUError::UnknownInstruction { instruction }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::IFU;
    use crate::isa::{
        Instruction, InstructionB, InstructionI, InstructionJ, InstructionR, InstructionS,
        InstructionU,
    };

    #[test]
    fn instruction_r() {
        let mut ifu = IFU;

        assert_eq!(
            ifu.fetch(0x003100b3),
            Ok(Instruction::ADD(InstructionR::new(
                crate::registers::RA,
                crate::registers::SP,
                crate::registers::GP
            )))
        )
    }

    #[test]
    fn instruction_i() {
        let mut ifu = IFU;

        assert_eq!(
            ifu.fetch(0x7d008113),
            Ok(Instruction::ADDI(InstructionI::new(
                crate::registers::SP,
                crate::registers::RA,
                2000
            )))
        );
    }

    #[test]
    fn instruction_s() {
        let mut ifu = IFU;

        assert_eq!(
            ifu.fetch(0xfef42623 as u32 as i32),
            Ok(Instruction::SW(InstructionS::new(
                crate::registers::S0,
                crate::registers::A5,
                -20
            )))
        );
    }

    #[test]
    fn instruction_b() {
        let mut ifu = IFU;

        assert_eq!(
            ifu.fetch(0x00208463),
            Ok(Instruction::BEQ(InstructionB::new(
                crate::registers::RA,
                crate::registers::SP,
                8
            )))
        );
    }

    #[test]
    fn instruction_u() {
        let mut ifu = IFU;

        assert_eq!(
            ifu.fetch(0x000320b7),
            Ok(Instruction::LUI(InstructionU::new(
                crate::registers::RA,
                204800
            )))
        );
    }

    #[test]
    fn instruction_j() {
        let mut ifu = IFU;

        assert_eq!(
            ifu.fetch(0x004000ef),
            Ok(Instruction::JAL(InstructionJ::new(crate::registers::RA, 4)))
        );
    }
}
