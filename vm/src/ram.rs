use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Error)]
pub enum RAMError {
    #[error("Memory size should be power of two, but it is {size}")]
    InvalidSize { size: u32 },
    #[error("Out of bounds")]
    OutOfBounds,
}

const fn check_bounds<T>(address: u32, slice: &[u8]) -> Result<(), RAMError> {
    let address = address as usize;
    let size = std::mem::size_of::<T>();

    if address + size > slice.len() {
        return Err(RAMError::OutOfBounds);
    }

    Ok(())
}

#[derive(Debug, Clone)]
pub struct RAM {
    memory: Vec<u8>,
}

impl RAM {
    pub fn new(size: u32) -> Result<Self, RAMError> {
        if size % 2 != 0 {
            return Err(RAMError::InvalidSize { size });
        }

        let memory = vec![0; size as usize];

        Ok(Self { memory })
    }

    pub fn as_slice(&self) -> &[u8] {
        self.memory.as_slice()
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.memory.as_mut_slice()
    }

    pub fn write_i8(&mut self, value: i8, address: u32) -> Result<(), RAMError> {
        check_bounds::<i8>(address, self.memory.as_slice())?;

        let address = address as usize;
        let bytes = value.to_le_bytes();

        self.memory[address..address + bytes.len()].copy_from_slice(&value.to_le_bytes());

        Ok(())
    }

    pub fn write_i16(&mut self, value: i16, address: u32) -> Result<(), RAMError> {
        check_bounds::<i16>(address, self.memory.as_slice())?;

        let address = address as usize;
        let bytes = value.to_le_bytes();

        self.memory[address..address + bytes.len()].copy_from_slice(&value.to_le_bytes());

        Ok(())
    }

    pub fn write_i32(&mut self, value: i32, address: u32) -> Result<(), RAMError> {
        check_bounds::<i32>(address, self.memory.as_slice())?;

        let address = address as usize;
        let bytes = value.to_le_bytes();

        self.memory[address..address + bytes.len()].copy_from_slice(&value.to_le_bytes());

        Ok(())
    }

    pub fn read_i8(&self, address: u32) -> Result<i8, RAMError> {
        check_bounds::<i8>(address, self.memory.as_slice())?;

        let address = address as usize;
        let mem = self.memory.as_slice();
        let value = i8::from_le_bytes([mem[address]]);

        Ok(value)
    }

    pub fn read_i16(&self, address: u32) -> Result<i16, RAMError> {
        check_bounds::<i16>(address, self.memory.as_slice())?;

        let address = address as usize;
        let mem = self.memory.as_slice();
        let value = i16::from_le_bytes([mem[address], mem[address + 1]]);

        Ok(value)
    }

    pub fn read_i32(&self, address: u32) -> Result<i32, RAMError> {
        check_bounds::<i32>(address, self.memory.as_slice())?;

        let address = address as usize;
        let mem = self.memory.as_slice();
        let value = i32::from_le_bytes([
            mem[address],
            mem[address + 1],
            mem[address + 2],
            mem[address + 3],
        ]);

        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use crate::ram::{RAMError, RAM};

    #[test]
    fn invalid_size() {
        let ram = RAM::new(33);

        assert!(ram.is_err());
        assert_eq!(ram.unwrap_err(), RAMError::InvalidSize { size: 33 });
    }

    #[test]
    fn write_read() {
        let mut ram = RAM::new(32).unwrap();

        assert_eq!(ram.write_i8(1, 0x1), Ok(()));
        assert_eq!(ram.read_i8(0x1), Ok(1));

        // i16
        assert_eq!(ram.write_i16(2, 0x0), Ok(()));
        assert_eq!(ram.read_i16(0x0), Ok(2));
        assert_eq!(ram.write_i16(4, 0x2), Ok(()));
        assert_eq!(ram.read_i16(0x2), Ok(4));

        // i32
        assert_eq!(ram.write_i32(8, 0x0), Ok(()));
        assert_eq!(ram.read_i32(0x0), Ok(8));
        assert_eq!(ram.write_i32(32, 0x8), Ok(()));
        assert_eq!(ram.read_i32(0x8), Ok(32));
    }
}
