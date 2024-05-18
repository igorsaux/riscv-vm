use crate::ram::{RAMError, RAM};
use thiserror::Error;

#[derive(Debug, Clone, Error, PartialEq)]
pub enum MMUError {
    #[error(transparent)]
    RAMError(#[from] RAMError),
    #[error("The address '0x{address:0X}' is misaligned")]
    NotAligned { address: u32 },
}

const fn check_align<T>(address: u32) -> Result<(), MMUError> {
    let size = std::mem::size_of::<T>();

    if (address as usize) % size == 0 {
        Ok(())
    } else {
        Err(MMUError::NotAligned { address })
    }
}

#[derive(Debug, Clone)]
pub struct RAMConfig {
    pub start_address: u32,
    pub size: u32,
}

#[derive(Debug, Clone)]
pub struct MMU {
    ram: (u32, RAM),
}

impl MMU {
    pub fn new(ram_config: RAMConfig) -> Result<Self, MMUError> {
        check_align::<i32>(ram_config.start_address)?;

        let ram = (ram_config.start_address, RAM::new(ram_config.size)?);

        Ok(Self { ram })
    }

    pub fn ram_start(&self) -> u32 {
        self.ram.0
    }

    pub fn ram(&self) -> &RAM {
        &self.ram.1
    }

    pub fn ram_mut(&mut self) -> &mut RAM {
        &mut self.ram.1
    }

    pub fn read_i8(&self, address: u32) -> Result<i8, MMUError> {
        if address >= self.ram.0 {
            let translated = address - self.ram.0;
            let value = self.ram.1.read_i8(translated)?;

            Ok(value)
        } else {
            todo!()
        }
    }

    pub fn read_i16(&self, address: u32) -> Result<i16, MMUError> {
        check_align::<i16>(address)?;

        if address >= self.ram.0 {
            let translated = address - self.ram.0;
            let value = self.ram.1.read_i16(translated)?;

            Ok(value)
        } else {
            todo!()
        }
    }

    pub fn read_i32(&self, address: u32) -> Result<i32, MMUError> {
        check_align::<i32>(address)?;

        if address >= self.ram.0 {
            let translated = address - self.ram.0;
            let value = self.ram.1.read_i32(translated)?;

            Ok(value)
        } else {
            todo!()
        }
    }

    pub fn write_i8(&mut self, value: i8, address: u32) -> Result<(), MMUError> {
        if address >= self.ram.0 {
            let translated = address - self.ram.0;

            self.ram.1.write_i8(value, translated)?;

            Ok(())
        } else {
            todo!()
        }
    }

    pub fn write_i16(&mut self, value: i16, address: u32) -> Result<(), MMUError> {
        check_align::<i16>(address)?;

        if address >= self.ram.0 {
            let translated = address - self.ram.0;

            self.ram.1.write_i16(value, translated)?;

            Ok(())
        } else {
            todo!()
        }
    }

    pub fn write_i32(&mut self, value: i32, address: u32) -> Result<(), MMUError> {
        check_align::<i16>(address)?;

        if address >= self.ram.0 {
            let translated = address - self.ram.0;

            self.ram.1.write_i32(value, translated)?;

            Ok(())
        } else {
            todo!()
        }
    }
}
