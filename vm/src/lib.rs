use cpu::CPU;

pub mod cpu;
pub mod ifu;
pub mod isa;
pub mod mmu;
pub mod ram;
pub mod registers;

#[derive(Debug)]
pub struct VM {
    pub cpu: CPU,
}

impl VM {
    pub fn new(cpu: CPU) -> Self {
        Self { cpu }
    }
}
