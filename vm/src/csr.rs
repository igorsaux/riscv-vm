use crate::{debug_unreachable, privilege_level::PrivilegeLevel};
use thiserror::Error;

/// ISA and extensions
pub const MISA: u16 = 0x301;

#[derive(Debug, Clone, Copy, Error)]
pub enum CSRError {
    #[error("Address '0X{address:0X}' is out of bounds")]
    OutOfBounds { address: u16 },
    #[error("Address '0X{address:0X}' is read-only")]
    IsReadOnly { address: u16 },
    #[error("Address '0X{address:0X}' requires a higher privilege")]
    MissingPrivilege { address: u16 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CSRMode {
    ReadOnly = 0,
    ReadWrite = 1,
}

#[derive(Debug, Clone)]
pub struct CSR {
    memory: Vec<u32>,
}

impl CSR {
    pub fn new() -> Self {
        Self {
            memory: vec![0; 4096],
        }
    }

    pub fn memory(&self) -> &[u32] {
        &self.memory
    }

    pub fn memory_mut(&mut self) -> &mut [u32] {
        &mut self.memory
    }

    pub fn check_bounds(&self, csr: u16) -> Result<(), CSRError> {
        if csr as usize >= self.memory.len() {
            Err(CSRError::OutOfBounds { address: csr })
        } else {
            Ok(())
        }
    }

    /// SAFETY: Check `csr` is in bounds with [CSR::check_bounds]
    pub unsafe fn mode(&self, csr: u16) -> CSRMode {
        let bits = ((csr >> 10) & 0b11) as u8;

        match bits {
            0b00 | 0b01 | 0b10 => CSRMode::ReadWrite,
            0b11 => CSRMode::ReadOnly,
            _ => debug_unreachable(),
        }
    }

    /// SAFETY: Check `csr` is in bounds with [CSR::check_bounds]
    pub unsafe fn min_privilege(&self, csr: u16) -> PrivilegeLevel {
        let bits = ((csr >> 8) & 0b11) as u8;

        #[cfg(debug_assertions)]
        return PrivilegeLevel::from_u8(bits).unwrap();
        #[cfg(not(debug_assertions))]
        return PrivilegeLevel::from_u8(bits).unwrap_unchecked();
    }

    /// SAFETY: Check `csr` is in bounds with [CSR::check_bounds]
    pub unsafe fn get_unchecked(&self, csr: u16) -> u32 {
        #[cfg(debug_assertions)]
        return *self.memory.get(csr as usize).unwrap();
        #[cfg(not(debug_assertions))]
        return *self.memory.get_unchecked(csr as usize);
    }

    /// SAFETY: Check `csr` is in bounds with [CSR::check_bounds]
    pub unsafe fn set_unchecked(&mut self, csr: u16, new_value: u32) {
        #[cfg(debug_assertions)]
        let value = self.memory.get_mut(csr as usize).unwrap();
        #[cfg(not(debug_assertions))]
        let value = self.memory.get_unchecked_mut(csr as usize);

        *value = new_value;
    }
}
