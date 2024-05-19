use crate::{
    csr::{CSRError, CSRMode, CSR},
    ifu::IFU,
    isa::{
        Instruction, InstructionB, InstructionI, InstructionIAlt, InstructionICSR,
        InstructionICSRImm, InstructionJ, InstructionR, InstructionS, InstructionU,
    },
    mmu::{RAMConfig, MMU},
    privilege_level::PrivilegeLevel,
    registers::Registers,
};

#[derive(Debug, Default, Clone)]
pub struct MachineInfo {
    pub vendor_id: u32,
    pub arch_id: u32,
    pub impl_id: u32,
}

#[derive(Debug, Clone)]
pub struct CPUConfig {
    pub machine_info: MachineInfo,
    pub ram: RAMConfig,
}

#[derive(Debug, Clone)]
pub struct CPU {
    pub privilege_level: PrivilegeLevel,
    pub registers: Registers,
    pub mmu: MMU,
    pub ifu: IFU,
    pub csr: CSR,
}

impl CPU {
    pub fn new(config: CPUConfig) -> Result<Self, anyhow::Error> {
        let mmu = MMU::new(config.ram)?;
        let ifu = IFU;
        let mut csr = CSR::new();

        unsafe {
            let mut misa = 0;

            // I Extension
            misa |= 0b1 << 8;
            // M Extension
            misa |= 0b1 << 12;
            // Supervisor
            misa |= 0b1 << 18;
            // User
            misa |= 0b1 << 20;
            // Z Extension
            misa |= 0b1 << 25;
            // 32-bit
            misa |= 1 << 30;

            csr.set_unchecked(crate::csr::MISA, misa);

            let minfo = config.machine_info;

            csr.set_unchecked(crate::csr::MVENDORID, minfo.vendor_id);
            csr.set_unchecked(crate::csr::MARCHID, minfo.arch_id);
            csr.set_unchecked(crate::csr::MIMPID, minfo.impl_id);
        };

        Ok(Self {
            privilege_level: PrivilegeLevel::Machine,
            registers: Registers::default(),
            mmu,
            ifu,
            csr,
        })
    }

    fn check_csr(&self, csr: u16, mode: CSRMode) -> Result<(), CSRError> {
        self.csr.check_bounds(csr)?;

        if unsafe { self.csr.mode(csr) } < mode {
            return Err(CSRError::IsReadOnly { address: csr });
        }

        if self.privilege_level < unsafe { self.csr.min_privilege(csr) } {
            return Err(CSRError::MissingPrivilege { address: csr });
        }

        Ok(())
    }

    pub fn csrrw(&mut self, csr: u16, value: u32) -> Result<u32, CSRError> {
        self.check_csr(csr, CSRMode::ReadWrite)?;

        let old_value = unsafe { self.csr.get_unchecked(csr) };

        unsafe { self.csr.set_unchecked(csr, value) };

        Ok(old_value)
    }

    pub fn csrrs(&mut self, csr: u16, bits: u32) -> Result<u32, CSRError> {
        let result = if bits == 0 {
            self.check_csr(csr, CSRMode::ReadOnly)?;

            unsafe { self.csr.get_unchecked(csr) }
        } else {
            self.check_csr(csr, CSRMode::ReadWrite)?;

            let old_value = unsafe { self.csr.get_unchecked(csr) };

            unsafe { self.csr.set_unchecked(csr, old_value | bits) };

            old_value
        };

        Ok(result)
    }

    pub fn csrrc(&mut self, csr: u16, bits: u32) -> Result<u32, CSRError> {
        let result = if bits == 0 {
            self.check_csr(csr, CSRMode::ReadOnly)?;

            unsafe { self.csr.get_unchecked(csr) }
        } else {
            self.check_csr(csr, CSRMode::ReadWrite)?;

            let old_value = unsafe { self.csr.get_unchecked(csr) };

            unsafe { self.csr.set_unchecked(csr, old_value & (!bits)) };

            old_value
        };

        Ok(result)
    }

    pub fn tick(&mut self) -> Result<(), anyhow::Error> {
        let pc = self.registers.pc();
        let npc = pc.wrapping_add(std::mem::size_of::<i32>() as u32);

        let instruction = self.mmu.read_i32(pc)?;
        let instruction = self.ifu.fetch(instruction)?;

        match instruction {
            Instruction::LUI(InstructionU { rd, imm }) => {
                self.registers.set(rd, imm);
            }
            Instruction::AUIPC(InstructionU { rd, imm }) => {
                let result = pc.wrapping_add_signed(imm) as i32;

                self.registers.set(rd, result);
            }
            Instruction::JAL(InstructionJ { rd, imm }) => {
                self.registers.set(rd, npc as i32);
                *self.registers.pc_mut() = pc.wrapping_add_signed(imm);

                return Ok(());
            }
            Instruction::JALR(InstructionI { rd, rs1, imm }) => {
                let result = self.registers.get(rs1).wrapping_add(imm as i32);

                self.registers.set(rd, npc as i32);
                *self.registers.pc_mut() = pc.wrapping_add_signed(result);

                return Ok(());
            }
            Instruction::BEQ(InstructionB { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);

                if rs1 == rs2 {
                    *self.registers.pc_mut() = pc.wrapping_add_signed(imm as i32);

                    return Ok(());
                }
            }
            Instruction::BNE(InstructionB { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);

                if rs1 != rs2 {
                    *self.registers.pc_mut() = pc.wrapping_add_signed(imm as i32);

                    return Ok(());
                }
            }
            Instruction::BLT(InstructionB { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);

                if rs1 < rs2 {
                    *self.registers.pc_mut() = pc.wrapping_add_signed(imm as i32);

                    return Ok(());
                }
            }
            Instruction::BGE(InstructionB { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);

                if rs1 >= rs2 {
                    *self.registers.pc_mut() = pc.wrapping_add_signed(imm as i32);

                    return Ok(());
                }
            }
            Instruction::BLTU(InstructionB { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1) as u32;
                let rs2 = self.registers.get(rs2) as u32;

                if rs1 < rs2 {
                    *self.registers.pc_mut() = pc.wrapping_add_signed(imm as i32);

                    return Ok(());
                }
            }
            Instruction::BGEU(InstructionB { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1) as u32;
                let rs2 = self.registers.get(rs2) as u32;

                if rs1 >= rs2 {
                    *self.registers.pc_mut() = pc.wrapping_add_signed(imm as i32);

                    return Ok(());
                }
            }
            Instruction::LB(InstructionI { rd, rs1, imm }) => {
                let rs1 = self.registers.get(rs1);
                let addr = rs1.wrapping_add(imm as i32) as u32;

                self.registers.set(rd, self.mmu.read_i8(addr)? as i32);
            }
            Instruction::LH(InstructionI { rd, rs1, imm }) => {
                let rs1 = self.registers.get(rs1);
                let addr = rs1.wrapping_add(imm as i32) as u32;

                self.registers.set(rd, self.mmu.read_i16(addr)? as i32);
            }
            Instruction::LW(InstructionI { rd, rs1, imm }) => {
                let rs1 = self.registers.get(rs1);
                let addr = rs1.wrapping_add(imm as i32) as u32;

                self.registers.set(rd, self.mmu.read_i32(addr)?);
            }
            Instruction::LBU(InstructionI { rd, rs1, imm }) => {
                let rs1 = self.registers.get(rs1);
                let addr = rs1.wrapping_add(imm as i32) as u32;

                self.registers.set(rd, self.mmu.read_i8(addr)? as u8 as i32);
            }
            Instruction::LHU(InstructionI { rd, rs1, imm }) => {
                let rs1 = self.registers.get(rs1);
                let addr = rs1.wrapping_add(imm as i32) as u32;

                self.registers
                    .set(rd, self.mmu.read_i16(addr)? as u16 as i32);
            }
            Instruction::SB(InstructionS { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2) as i8;
                let addr = rs1.wrapping_add(imm as i32) as u32;

                self.mmu.write_i8(rs2, addr)?;
            }
            Instruction::SH(InstructionS { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2) as i16;
                let addr = rs1.wrapping_add(imm as i32) as u32;

                self.mmu.write_i16(rs2, addr)?;
            }
            Instruction::SW(InstructionS { rs1, rs2, imm }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let addr = rs1.wrapping_add(imm as i32) as u32;

                self.mmu.write_i32(rs2, addr)?;
            }
            Instruction::ADDI(InstructionI { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1);
                let result = rs1_value.wrapping_add(imm as i32);

                self.registers.set(rd, result);
            }
            Instruction::SLTI(InstructionI { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1);
                let result = if rs1_value < imm as i32 { 1 } else { 0 };

                self.registers.set(rd, result);
            }
            Instruction::SLTIU(InstructionI { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1) as u32;
                let result = if rs1_value < imm as u32 { 1 } else { 0 };

                self.registers.set(rd, result);
            }
            Instruction::XORI(InstructionI { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1);
                let result = rs1_value ^ (imm as i32);

                self.registers.set(rd, result);
            }
            Instruction::ORI(InstructionI { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1);
                let result = rs1_value | (imm as i32);

                self.registers.set(rd, result);
            }
            Instruction::ANDI(InstructionI { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1);
                let result = rs1_value & (imm as i32);

                self.registers.set(rd, result);
            }
            Instruction::SLLI(InstructionIAlt { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1) as u32;
                let result = rs1_value.wrapping_shl(imm as u32);

                self.registers.set(rd, result as i32);
            }
            Instruction::SRLI(InstructionIAlt { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1) as u32;
                let result = rs1_value.wrapping_shr(imm as u32);

                self.registers.set(rd, result as i32);
            }
            Instruction::SRAI(InstructionIAlt { rd, rs1, imm }) => {
                let rs1_value = self.registers.get(rs1);
                let result = rs1_value.wrapping_shr(imm as u32);

                self.registers.set(rd, result);
            }
            Instruction::ADD(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let result = rs1.wrapping_add(rs2);

                self.registers.set(rd, result);
            }
            Instruction::SUB(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let result = rs1.wrapping_sub(rs2);

                self.registers.set(rd, result);
            }
            Instruction::SLL(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as u32;
                let rs2 = self.registers.get(rs2) as u32;
                let result = rs1.wrapping_shl(rs2);

                self.registers.set(rd, result as i32);
            }
            Instruction::SLT(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let result = if rs1 < rs2 { 1 } else { 2 };

                self.registers.set(rd, result);
            }
            Instruction::SLTU(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as u32;
                let rs2 = self.registers.get(rs2) as u32;
                let result = if rs1 < rs2 { 1 } else { 2 };

                self.registers.set(rd, result);
            }
            Instruction::XOR(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let result = rs1 ^ rs2;

                self.registers.set(rd, result);
            }
            Instruction::SRL(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as u32;
                let rs2 = self.registers.get(rs2) as u32;
                let result = rs1.wrapping_shr(rs2);

                self.registers.set(rd, result as i32);
            }
            Instruction::SRA(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2) as u32;
                let result = rs1.wrapping_shr(rs2);

                self.registers.set(rd, result);
            }
            Instruction::OR(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let result = rs1 | rs2;

                self.registers.set(rd, result);
            }
            Instruction::AND(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let result = rs1 & rs2;

                self.registers.set(rd, result);
            }
            Instruction::FENCE(_) => {}
            Instruction::ECALL => {}
            Instruction::EBREAK => {}
            // M Extension
            Instruction::MUL(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as i64;
                let rs2 = self.registers.get(rs2) as i64;
                let result = rs1.wrapping_mul(rs2) as i32;

                self.registers.set(rd, result);
            }
            Instruction::MULH(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as i64;
                let rs2 = self.registers.get(rs2) as i64;
                let result = (rs1.wrapping_mul(rs2) >> 32) as i32;

                self.registers.set(rd, result);
            }
            Instruction::MULHSU(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as i64;
                let rs2 = self.registers.get(rs2) as u32 as u64;
                let result = (rs1.wrapping_mul(rs2 as i64) >> 32) as i32;

                self.registers.set(rd, result);
            }
            Instruction::MULHU(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as u32 as u64;
                let rs2 = self.registers.get(rs2) as u32 as u64;
                let result = (rs1.wrapping_mul(rs2) >> 32) as i32;

                self.registers.set(rd, result);
            }
            Instruction::DIV(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let result = rs1.wrapping_div(rs2);

                self.registers.set(rd, result);
            }
            Instruction::DIVU(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as u32;
                let rs2 = self.registers.get(rs2) as u32;
                let result = rs1.wrapping_div(rs2) as i32;

                self.registers.set(rd, result);
            }
            Instruction::REM(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1);
                let rs2 = self.registers.get(rs2);
                let result = rs1.wrapping_rem(rs2);

                self.registers.set(rd, result);
            }
            Instruction::REMU(InstructionR { rd, rs1, rs2 }) => {
                let rs1 = self.registers.get(rs1) as u32;
                let rs2 = self.registers.get(rs2) as u32;
                let result = rs1.wrapping_rem(rs2) as i32;

                self.registers.set(rd, result);
            }
            Instruction::CSRRW(InstructionICSR { rd, rs1, csr }) => {
                let new_value = self.registers.get(rs1) as u32;
                let result = self.csrrw(csr, new_value)? as i32;

                self.registers.set(rd, result);
            }
            Instruction::CSRRS(InstructionICSR { rd, rs1, csr }) => {
                let bits = self.registers.get(rs1) as u32;
                let result = self.csrrs(csr, bits)? as i32;

                self.registers.set(rd, result);
            }
            Instruction::CSRRC(InstructionICSR { rd, rs1, csr }) => {
                let bits = self.registers.get(rs1) as u32;
                let result = self.csrrc(csr, bits)? as i32;

                self.registers.set(rd, result);
            }
            Instruction::CSRRWI(InstructionICSRImm { rd, imm, csr }) => {
                let result = self.csrrw(csr, imm as u32)? as i32;

                self.registers.set(rd, result);
            }
            Instruction::CSRRSI(InstructionICSRImm { rd, imm, csr }) => {
                let result = self.csrrs(csr, imm as u32)? as i32;

                self.registers.set(rd, result);
            }
            Instruction::CSRRCI(InstructionICSRImm { rd, imm, csr }) => {
                let result = self.csrrc(csr, imm as u32)? as i32;

                self.registers.set(rd, result);
            }
        }

        *self.registers.pc_mut() = npc;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{CPUConfig, CPU};
    use crate::{cpu::MachineInfo, mmu::RAMConfig};

    fn make_cpu(program: &[u8]) -> CPU {
        assert!(program.len() % std::mem::size_of::<i32>() == 0);

        let mut cpu = CPU::new(CPUConfig {
            machine_info: MachineInfo::default(),
            ram: RAMConfig {
                start_address: 0,
                size: program.len() as u32,
            },
        })
        .unwrap();

        let (_, program, _) = unsafe { program.align_to::<u32>() };

        for (idx, byte) in program.iter().enumerate() {
            let byte = byte.to_be_bytes();

            cpu.mmu
                .ram_mut()
                .write_i32(
                    i32::from_ne_bytes(byte),
                    (idx * std::mem::size_of::<i32>()) as u32,
                )
                .unwrap();
        }

        *cpu.registers.pc_mut() = 0;

        cpu
    }

    mod i_extension {
        use crate::cpu::tests::make_cpu;
        use hex_literal::hex;

        #[test]
        fn lui() {
            // lui x1, 1
            let mut cpu = make_cpu(&hex!("000010b7"));

            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 4096);
        }

        #[test]
        fn auipc() {
            // addi x1, x0, 0
            // auipc x1, 15
            let mut cpu = make_cpu(&hex!("00000093 0000f0b7"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 61440);
        }

        #[test]
        fn jal() {
            // jal x1, 8
            // addi x2, x0, 1024
            // addi x2, x2, 1
            let mut cpu = make_cpu(&hex!("008000ef 40000113 00110113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 4);
            assert_eq!(cpu.registers.get(crate::registers::SP), 1);
        }

        #[test]
        fn jalr() {
            // addi x1, x0, 4
            // jalr x2, x1, 4
            // addi x3, x0, 1024
            // addi x3, x3, 1
            let mut cpu = make_cpu(&hex!("00400093 00408167 40000193 00118193"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 4);
            assert_eq!(cpu.registers.get(crate::registers::SP), 8);
            assert_eq!(cpu.registers.get(crate::registers::GP), 1);
        }

        #[test]
        fn beq() {
            // addi x1, x0, 2
            // addi x2, x0, 2
            // beq x1, x2, 8
            // addi x2, x1, 0
            // addi x3, x0, 1024
            let mut cpu = make_cpu(&hex!("00200093 00200113 00208463 00008113 40000193"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1024);
        }

        #[test]
        fn bne() {
            // addi x1, x0, 1
            // addi x2, x0, 2
            // bne x1, x2, 8
            // addi x2, x1, 0
            // addi x3, x0, 1024
            let mut cpu = make_cpu(&hex!("00100093 00200113 00209463 00008113 40000193"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1024);
        }

        #[test]
        fn blt() {
            // addi x1, x0, -10
            // addi x2, x0, 5
            // blt x1, x2, 8
            // addi x2, x1, 0
            // addi x3, x0, 1024
            let mut cpu = make_cpu(&hex!("ff600093 00500113 0020c463 00008113 40000193"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1024);
        }

        // TODO: BGE, BLTU, BGEU

        #[test]
        fn sb_lb() {
            // addi x1, x0, 0xFF
            // sb x1, 0(x0)
            // lb x2, 0(x0)
            let mut cpu = make_cpu(&hex!("0ff00093 00100023 00000103"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 0xFF);
            assert_eq!(cpu.registers.get(crate::registers::SP), -1);
        }

        #[test]
        fn sh_lh() {
            // lui x1, 0x10
            // add x1, x1, -86
            // sh x1, 2(x0)
            // lh x2, 2(x0)
            let mut cpu = make_cpu(&hex!("000100b7 faa08093 00101123 00201103"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 0xFFAA);
            assert_eq!(cpu.registers.get(crate::registers::SP), -86);
        }

        #[test]
        fn sw_lw() {
            // lui x1, 0x1000
            // addi x1, x1, -1
            // sw x1, 4(x0)
            // lw x2, 4(x0)
            let mut cpu = make_cpu(&hex!("010000b7 fff08093 00102223 00402103"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 0xFFFFFF);
            assert_eq!(cpu.registers.get(crate::registers::SP), 16777215);
        }

        #[test]
        fn lbu() {
            // addi x1, x0, 0xFF
            // sb x1, 0(x0)
            // lbu x2, 0(x0)
            let mut cpu = make_cpu(&hex!("0ff00093 00100023 00004103"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 0xFF);
            assert_eq!(cpu.registers.get(crate::registers::SP), 0xFF);
        }

        #[test]
        fn lhu() {
            // lui x1, 0x10
            // addi x1, x1, -86
            // sh x1, 0(x0)
            // lhu x2, 0(x0)
            let mut cpu = make_cpu(&hex!("000100b7 faa08093 00101023 00005103"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 0xFFAA);
            assert_eq!(cpu.registers.get(crate::registers::SP), 0xFFAA);
        }

        #[test]
        fn addi() {
            // addi x1, x0, 5
            // addi x1, x1, 5
            let mut cpu = make_cpu(&hex!("00500093 00508093"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 10);
        }

        #[test]
        fn slti() {
            // addi x1, x0, 5
            // slti x2, x1, 10
            // slti x2, x1, 2
            let mut cpu = make_cpu(&hex!("00500093 00a0a113 0020a113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 1);

            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 0);
        }

        #[test]
        fn sltiu() {
            // addi x1, x0, 5
            // sltiu x2, x1, 10
            // sltiu x2, x1, 2
            // addi x1, x0, 0
            // sltiu x2, x1, 1
            let mut cpu = make_cpu(&hex!("00500093 00a0b113 0020b113 00000093 0010b113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 1);

            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 0);

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 1);
        }

        #[test]
        fn xori() {
            // addi x1, x0, 5
            // xori x2, x1, 1
            // xori x2, x1, -1
            let mut cpu = make_cpu(&hex!("00500093 0010c113 fff0c113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 4);

            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), -6);
        }

        #[test]
        fn ori() {
            // addi x1, x0, 5
            // ori x2, x1, 1
            let mut cpu = make_cpu(&hex!("00500093 0010e113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 5);
        }

        #[test]
        fn andi() {
            // addi x1, x0, 5
            // andi x2, x1, 1
            let mut cpu = make_cpu(&hex!("00500093 0010f113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 1);
        }

        #[test]
        fn slli() {
            // addi x1, x0, 1024
            // slli x2, x1, 2
            let mut cpu = make_cpu(&hex!("40000093 00209113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 4096);
        }

        #[test]
        fn srli() {
            // addi x1, x0, -10
            // srli x2, x1, 2
            let mut cpu = make_cpu(&hex!("ff600093 0020d113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 1073741821);
        }

        #[test]
        fn srai() {
            // addi x1, x0, -10
            // srai x2, x1, 2
            let mut cpu = make_cpu(&hex!("ff600093 4020d113"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), -3);
        }

        #[test]
        fn add() {
            // addi x1, x0, 1
            // addi x2, x0, 1
            // add x3, x1, x2
            let mut cpu = make_cpu(&hex!("00100093 00100113 002081b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 2);
        }

        #[test]
        fn sub() {
            // addi x1, x0, 1
            // addi x2, x0, 2
            // sub x3, x1, x2
            let mut cpu = make_cpu(&hex!("00100093 00200113 402081b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), -1);
        }

        #[test]
        fn sll() {
            // addi x1, x0, 1
            // addi x2, x0, 3
            // sll x3, x1, x2
            let mut cpu = make_cpu(&hex!("00100093 00300113 002091b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 8);
        }

        #[test]
        fn slt() {
            // addi x1, x0, 1
            // addi x2, x0, 3
            // slt x3, x1, x2
            let mut cpu = make_cpu(&hex!("00100093 00300113 0020a1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1);
        }

        #[test]
        fn sltu() {
            // addi x1, x0, 1
            // addi x2, x0, -3
            // sltu x3, x1, x2
            let mut cpu = make_cpu(&hex!("00100093 ffd00113 0020b1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1);
        }

        #[test]
        fn xor() {
            // addi x1, x0, 1
            // addi x2, x0, -3
            // xor x3, x1, x2
            let mut cpu = make_cpu(&hex!("00100093 ffd00113 0020c1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), -4);
        }

        #[test]
        fn srl() {
            // addi x1, x0, 1
            // addi x2, x0, 4
            // srl x3, x2, x1
            let mut cpu = make_cpu(&hex!("00100093 00400113 001151b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 2);
        }

        #[test]
        fn sra() {
            // addi x1, x0, 2
            // addi x2, x0, -4
            // sra x3, x2, x1
            let mut cpu = make_cpu(&hex!("00200093 ffc00113 401151b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), -1);
        }

        #[test]
        fn or() {
            // addi x1, x0, 1
            // addi x2, x0, 2
            // or x3, x1, x2
            let mut cpu = make_cpu(&hex!("00100093 00200113 0020e1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 3);
        }

        #[test]
        fn and() {
            // addi x1, x0, 1
            // addi x2, x0, 3
            // and x3, x1, x2
            // addi x1, x0, 1
            // addi x2, x0, 2
            // or x3, x1, x2
            let mut cpu = make_cpu(&hex!("00100093 00300113 0020f1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1);
        }
    }

    mod m_extension {
        use crate::cpu::tests::make_cpu;
        use hex_literal::hex;

        #[test]
        fn mul() {
            // lui x1, 0x8
            // li x2, 256
            // mul x3, x1, x2
            let mut cpu = make_cpu(&hex!("000080b7 10000113 022081b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 8388608);

            // li x1, -1
            // li x2, -1
            // mul x3, x1, x2
            let mut cpu = make_cpu(&hex!("fff00093 fff00113 022081b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1);
        }

        #[test]
        fn mulh() {
            // li x1, 32768
            // slli x1, x1, 16
            // li x2, 2
            // mulh x3, x1, x2
            let mut cpu = make_cpu(&hex!("000080b7 01009093 00200113 022091b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), -1);
        }

        #[test]
        fn mulhsu() {
            // li x1, -3
            // li x2, 2
            // mulhsu x3, x1, x2
            let mut cpu = make_cpu(&hex!("ffd00093 00200113 0220a1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), -3);
            assert_eq!(cpu.registers.get(crate::registers::GP), -1);
        }

        #[test]
        fn mulhu() {
            // li x1, -3
            // li x2, 2
            // mulhu x3, x1, x2
            let mut cpu = make_cpu(&hex!("ffd00093 00200113 0220b1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), -3);
            assert_eq!(cpu.registers.get(crate::registers::SP), 2);
            assert_eq!(cpu.registers.get(crate::registers::GP), 1);
        }

        #[test]
        fn div() {
            // li x1, 3
            // li x2, 2
            // div x3, x1, x2
            let mut cpu = make_cpu(&hex!("00300093 00200113 0220c1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1);

            //li x1, 3
            //li x2, -2
            //div x4, x1, x2
            let mut cpu = make_cpu(&hex!("00300093 ffe00113 0220c233"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::TP), -1);
        }

        #[test]
        fn divu() {
            // li x1, 3
            // li x2, -2
            // divu x3, x1, x2
            let mut cpu = make_cpu(&hex!("00300093 ffe00113 0220d1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 0);
        }

        #[test]
        fn rem() {
            // li x1, 3
            // li x2, -2
            // rem x3, x1, x2
            let mut cpu = make_cpu(&hex!("00300093 ffe00113 0220e1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 1);

            // li x1, 4
            // li x2, 2
            // rem x3, x1, x2
            let mut cpu = make_cpu(&hex!("00400093 00200113 0220e233"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::TP), 0);
        }

        #[test]
        fn remu() {
            // li x1, 3
            // li x2, -2
            // remu x3, x1, x2
            let mut cpu = make_cpu(&hex!("00300093 ffe00113 0220f1b3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 3);

            // li x1, -4
            // li x2, 2
            // remu x4, x1, x2
            let mut cpu = make_cpu(&hex!("ffc00093 00200113 0220f233"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::GP), 0);
        }
    }

    mod zicsr_extension {
        use super::make_cpu;
        use crate::privilege_level::PrivilegeLevel;
        use hex_literal::hex;

        #[test]
        fn cssrw() {
            // addi x1, x0, 0
            // csrrw x0, 0x301, x1
            // csrrs x2, 0x301, x0
            let mut cpu = make_cpu(&hex!("00000093 30109073 30102173"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 0);
        }

        #[test]
        fn csrrc() {
            // csrrc x1, 0x301, x0
            let mut cpu = make_cpu(&hex!("301030f3"));

            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 0x42141100);

            // lui x1, 1
            // csrrc x0, 0xF11, x1
            // csrrc x2, 0xF11, x0
            let mut cpu = make_cpu(&hex!("000010b7 3010b073 30103173"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 0x42140100);
        }

        #[test]
        fn csrrs() {
            // addi x1, x0, 0x10
            // csrrs x0, 0x301, x1
            // csrrs x2, 0x301, x0
            let mut cpu = make_cpu(&hex!("01000093 3010a073 30102173"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 0x42141110);
        }

        #[test]
        fn csrrwi() {
            // csrrwi x0, 0x301, 0
            // csrrs x1, 0x301, x0
            let mut cpu = make_cpu(&hex!("30105073 301020f3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::SP), 0);
        }

        #[test]
        fn csrrsi_csrrci() {
            // csrrsi x0, 0x301, 1
            // csrrs x1, 0x301, x0
            let mut cpu = make_cpu(&hex!("3010e073 301020f3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 0x42141101);

            // csrrci x0, 0x301, 1
            // csrrs x1, 0x301, x0
            let mut cpu = make_cpu(&hex!("3010f073 301020f3"));

            cpu.tick().unwrap();
            cpu.tick().unwrap();

            assert_eq!(cpu.registers.get(crate::registers::RA), 0x42141100);
        }

        #[test]
        fn missing_privilege() {
            // csrrc x1, 0x301, x0
            let mut cpu = make_cpu(&hex!("301030f3"));

            cpu.privilege_level = PrivilegeLevel::User;

            assert!(cpu.tick().is_err());
        }

        #[test]
        fn writing_read_only() {
            // csrrc x1, 0xF11, x0
            let mut cpu = make_cpu(&hex!("f11030f3"));

            assert!(cpu.tick().is_err());
        }
    }
}
