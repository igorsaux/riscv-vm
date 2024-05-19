#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrivilegeLevel {
    User = 0,
    Supervisor = 1,
    Machine = 3,
}

impl PrivilegeLevel {
    pub fn as_u8(self) -> u8 {
        match self {
            PrivilegeLevel::User => 0b00,
            PrivilegeLevel::Supervisor => 0b01,
            PrivilegeLevel::Machine => 0b11,
        }
    }

    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0b00 => Some(Self::User),
            0b01 => Some(Self::Supervisor),
            0b11 => Some(Self::Machine),
            _ => None,
        }
    }
}
