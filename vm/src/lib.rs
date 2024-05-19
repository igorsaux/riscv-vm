use cpu::CPU;

pub mod cpu;
pub mod csr;
pub mod ifu;
pub mod isa;
pub mod mmu;
pub mod privilege_level;
pub mod ram;
pub mod registers;

#[inline(always)]
pub(crate) fn debug_unreachable() -> ! {
    #[cfg(debug_assertions)]
    unreachable!();
    #[cfg(not(debug_assertions))]
    unreachable_unchecked();
}

#[derive(Debug)]
pub struct VM {
    pub cpu: CPU,
}

impl VM {
    pub fn new(cpu: CPU) -> Self {
        Self { cpu }
    }
}
