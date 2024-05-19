use std::path::{Path, PathBuf};

use anyhow::Context;
use clap::Parser;
use object::{Architecture, Object, ObjectSection};
use vm::{
    cpu::{CPUConfig, MachineInfo, CPU},
    mmu::RAMConfig,
};

#[derive(Debug, Parser)]
struct App {
    /// Path to a RISC-V binary file.
    pub elf: PathBuf,
}

#[derive(Debug, Clone)]
struct MachineCode {
    pub entry: u64,
    pub data: Vec<u8>,
}

fn load_elf(path: &Path) -> Result<MachineCode, anyhow::Error> {
    let content = std::fs::read(path)?;
    let elf = object::File::parse(&*content)?;

    if !matches!(elf.architecture(), Architecture::Riscv32) {
        anyhow::bail!("Unsupported architecture: '{:#?}'", elf.architecture());
    }

    if !matches!(elf.endianness(), object::Endianness::Little) {
        anyhow::bail!("Big-Endian is not supported");
    }

    let entry = elf.entry();
    let text = elf
        .section_by_name(".text")
        .context("'.text' section not found")?;
    let data = text.data()?.to_vec();

    Ok(MachineCode { entry, data })
}

fn main() -> Result<(), anyhow::Error> {
    let app = App::parse();
    let machine_code = load_elf(&app.elf)?;
    let code_size = machine_code.data.len() as u32;

    let mut vm = vm::VM::new(CPU::new(CPUConfig {
        machine_info: MachineInfo::default(),
        ram: RAMConfig {
            start_address: 0,
            size: machine_code.data.len() as u32,
        },
    })?);

    {
        let ram = vm.cpu.mmu.ram_mut();

        for (idx, byte) in machine_code.data.into_iter().enumerate() {
            ram.write_i8(byte as i8, idx as u32)?;
        }

        *vm.cpu.registers.pc_mut() = machine_code.entry as u32;
    }

    let mut iters = 100;

    loop {
        if let Err(err) = vm.cpu.tick() {
            eprintln!("{err}");

            break;
        }

        if vm.cpu.registers.pc() == code_size {
            if iters > 0 {
                iters -= 1;

                *vm.cpu.registers.pc_mut() = machine_code.entry as u32;
                continue;
            }

            break;
        }
    }

    println!("VM dump:\n{vm:#?}");

    Ok(())
}
