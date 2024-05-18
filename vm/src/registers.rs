/// Hardwired to 0, ignores writes
pub const ZERO: Register = unsafe { Register::new_unchecked(0) };
/// Return address for jumps
pub const RA: Register = unsafe { Register::new_unchecked(1) };
/// Stack pointer
pub const SP: Register = unsafe { Register::new_unchecked(2) };
/// Global pointer
pub const GP: Register = unsafe { Register::new_unchecked(3) };
/// Thread pointer
pub const TP: Register = unsafe { Register::new_unchecked(4) };
/// Temporary register 0
pub const T0: Register = unsafe { Register::new_unchecked(5) };
/// Temporary register 1
pub const T1: Register = unsafe { Register::new_unchecked(6) };
/// Temporary register 2
pub const T2: Register = unsafe { Register::new_unchecked(7) };
/// Saved register 0 or frame pointer
pub const S0: Register = unsafe { Register::new_unchecked(8) };
/// Saved register 1
pub const S1: Register = unsafe { Register::new_unchecked(9) };
/// Return value or function argument 0
pub const A0: Register = unsafe { Register::new_unchecked(10) };
/// Return value or function argument 1
pub const A1: Register = unsafe { Register::new_unchecked(11) };
/// Function argument 2
pub const A2: Register = unsafe { Register::new_unchecked(12) };
/// Function argument 3
pub const A3: Register = unsafe { Register::new_unchecked(13) };
/// Function argument 4
pub const A4: Register = unsafe { Register::new_unchecked(14) };
/// Function argument 5
pub const A5: Register = unsafe { Register::new_unchecked(15) };
/// Function argument 6
pub const A6: Register = unsafe { Register::new_unchecked(16) };
/// Function argument 7
pub const A7: Register = unsafe { Register::new_unchecked(17) };
/// Saved register 2
pub const S2: Register = unsafe { Register::new_unchecked(18) };
/// Saved register 3
pub const S3: Register = unsafe { Register::new_unchecked(19) };
/// Saved register 4
pub const S4: Register = unsafe { Register::new_unchecked(20) };
/// Saved register 5
pub const S5: Register = unsafe { Register::new_unchecked(21) };
/// Saved register 6
pub const S6: Register = unsafe { Register::new_unchecked(22) };
/// Saved register 7
pub const S7: Register = unsafe { Register::new_unchecked(23) };
/// Saved register 8
pub const S8: Register = unsafe { Register::new_unchecked(24) };
/// Saved register 9
pub const S9: Register = unsafe { Register::new_unchecked(25) };
/// Saved register 10
pub const S10: Register = unsafe { Register::new_unchecked(26) };
/// Saved register 11
pub const S11: Register = unsafe { Register::new_unchecked(27) };
/// Temporary register 3
pub const T3: Register = unsafe { Register::new_unchecked(28) };
/// Temporary register 4
pub const T4: Register = unsafe { Register::new_unchecked(29) };
/// Temporary register 5
pub const T5: Register = unsafe { Register::new_unchecked(30) };
/// Temporary register 6
pub const T6: Register = unsafe { Register::new_unchecked(31) };

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Register(u8);

impl Register {
    pub const fn new(i: u8) -> Option<Self> {
        if i < 32 {
            Some(Self(i))
        } else {
            None
        }
    }

    pub const unsafe fn new_unchecked(i: u8) -> Self {
        Self(i)
    }

    pub const fn as_u8(&self) -> u8 {
        self.0
    }
}

/// See [ASM Manual](https://github.com/riscv-non-isa/riscv-asm-manual/blob/main/riscv-asm.md#general-registers)
#[derive(Debug, Default, Clone)]
pub struct Registers {
    registers: [i32; 31],
    pc: u32,
}

impl Registers {
    pub fn get(&self, register: Register) -> i32 {
        let i = register.as_u8() as usize;

        if i == 0 {
            0
        } else {
            unsafe { *self.registers.get_unchecked(i - 1) }
        }
    }

    pub fn set(&mut self, register: Register, value: i32) {
        let i = register.as_u8() as usize;

        if i == 0 {
            return;
        }

        unsafe { *self.registers.get_unchecked_mut(i - 1) = value };
    }

    pub fn pc(&self) -> u32 {
        self.pc
    }

    pub fn pc_mut(&mut self) -> &mut u32 {
        &mut self.pc
    }
}
