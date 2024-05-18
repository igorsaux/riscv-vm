use cpu::CPU;

pub mod cpu;
pub mod ifu;
pub mod isa;
pub mod mmu;
pub mod prof;
pub mod ram;
pub mod registers;

#[derive(Debug)]
pub struct VM {
    pub cpu: CPU,
}

impl VM {
    #[crate::prof::instrument("VM::new", skip_all)]
    pub fn new(cpu: CPU) -> Self {
        Self { cpu }
    }
}
