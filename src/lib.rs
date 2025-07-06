use std::{
    fmt,
    fs::{self, File},
    io::{BufRead, BufReader, Read, Seek, Write},
};

/// Macro for converting hex strings to u64 values at compile time
#[macro_export]
macro_rules! hex {
    ($hex:expr) => {
        u64::from_str_radix($hex, 16).expect(concat!("Invalid hex: ", $hex))
    };
}

/// Error types for memory operations
#[derive(Debug)]
pub enum MemoryError {
    ProcessNotFound(String),
    BaseAddressNotFound(String),
    InsufficientPermissions,
    IoError(std::io::Error),
    ParseError,
    InvalidAddress,
}

impl fmt::Display for MemoryError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MemoryError::ProcessNotFound(name) => write!(f, "Process '{name}' not found"),
            MemoryError::BaseAddressNotFound(name) => {
                write!(f, "Base address for '{name}' not found")
            }
            MemoryError::InsufficientPermissions => {
                write!(f, "Insufficient permissions to access memory")
            }
            MemoryError::IoError(e) => write!(f, "IO error: {e}"),
            MemoryError::ParseError => write!(f, "Failed to parse data"),
            MemoryError::InvalidAddress => write!(f, "Invalid memory address"),
        }
    }
}

impl std::error::Error for MemoryError {}

/// Main struct for game memory manipulation utilities
pub struct GameMemUtils {
    handle: File,
    pid: u64,
    base_address: u64,
}

impl GameMemUtils {
    /// Create a new GameMemUtils instance by process name
    ///
    /// # Arguments
    /// * `process_name` - The name of the process to attach to
    ///
    /// # Returns
    /// * `Result<Self, MemoryError>` - The GameMemUtils instance or an error
    pub fn new(process_name: &str) -> Result<Self, MemoryError> {
        let pid = Self::find_process_id(process_name)?;
        let base_address = Self::find_base_address(pid, process_name)?;
        let handle = Self::get_memory_handle(pid)?;

        Ok(GameMemUtils {
            handle,
            pid,
            base_address,
        })
    }

    /// Create a new GameMemUtils instance from a process ID
    ///
    /// # Arguments
    /// * `pid` - The process ID to attach to
    ///
    /// # Returns
    /// * `Result<Self, MemoryError>` - The GameMemUtils instance or an error
    pub fn from_pid(pid: u64) -> Result<Self, MemoryError> {
        let handle = Self::get_memory_handle(pid)?;

        Ok(GameMemUtils {
            handle,
            pid,
            base_address: 0,
        })
    }

    /// Get the process ID
    pub fn pid(&self) -> u64 {
        self.pid
    }

    /// Get the base address
    pub fn base_address(&self) -> u64 {
        self.base_address
    }

    /// Set the base address manually
    ///
    /// # Arguments
    /// * `address` - The new base address
    pub fn set_base_address(&mut self, address: u64) {
        self.base_address = address;
    }

    /// Find the base address of a specific module
    ///
    /// # Arguments
    /// * `module_name` - The name of the module to find
    ///
    /// # Returns
    /// * `Result<u64, MemoryError>` - The base address or an error
    pub fn find_module_base(&self, module_name: &str) -> Result<u64, MemoryError> {
        Self::find_base_address(self.pid, module_name)
    }

    /// Read a value at a specific absolute address
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to read from
    ///
    /// # Returns
    /// * `Result<T, MemoryError>` - The value read or an error
    pub fn read_at<T>(&mut self, address: u64) -> Result<T, MemoryError>
    where
        T: Copy + Default,
    {
        let size = std::mem::size_of::<T>();
        let mut buffer = vec![0u8; size];

        self.handle
            .seek(std::io::SeekFrom::Start(address))
            .map_err(MemoryError::IoError)?;
        self.handle
            .read_exact(&mut buffer)
            .map_err(MemoryError::IoError)?;

        // Safety: We've read exactly size_of::<T>() bytes and T is Copy
        // This assumes same endianness and alignment between processes
        Ok(unsafe { std::ptr::read_unaligned(buffer.as_ptr() as *const T) })
    }

    /// Read a value at an offset from the base address
    ///
    /// # Arguments
    /// * `offset` - The offset from the base address
    ///
    /// # Returns
    /// * `Result<T, MemoryError>` - The value read or an error
    pub fn read<T>(&mut self, offset: u64) -> Result<T, MemoryError>
    where
        T: Copy + Default,
    {
        self.read_at(self.base_address + offset)
    }

    /// Read a value at a hex offset from the base address
    ///
    /// # Arguments
    /// * `hex_offset` - The hex string offset from the base address
    ///
    /// # Returns
    /// * `Result<T, MemoryError>` - The value read or an error
    pub fn read_hex<T>(&mut self, hex_offset: &str) -> Result<T, MemoryError>
    where
        T: Copy + Default,
    {
        let offset = u64::from_str_radix(hex_offset, 16).map_err(|_| MemoryError::ParseError)?;
        self.read(offset)
    }

    /// Write a value at a specific absolute address
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to write to
    /// * `value` - The value to write
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - Success or an error
    pub fn write_at<T>(&mut self, address: u64, value: T) -> Result<(), MemoryError>
    where
        T: Copy,
    {
        let size = std::mem::size_of::<T>();
        let buffer = unsafe { std::slice::from_raw_parts(&value as *const T as *const u8, size) };

        self.handle
            .seek(std::io::SeekFrom::Start(address))
            .map_err(MemoryError::IoError)?;
        self.handle
            .write_all(buffer)
            .map_err(MemoryError::IoError)?;
        self.handle.flush().map_err(MemoryError::IoError)?;

        Ok(())
    }

    /// Write a value at an offset from the base address
    ///
    /// # Arguments
    /// * `offset` - The offset from the base address
    /// * `value` - The value to write
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - Success or an error
    pub fn write<T>(&mut self, offset: u64, value: T) -> Result<(), MemoryError>
    where
        T: Copy,
    {
        self.write_at(self.base_address + offset, value)
    }

    /// Write a value at a hex offset from the base address
    ///
    /// # Arguments
    /// * `hex_offset` - The hex string offset from the base address
    /// * `value` - The value to write
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - Success or an error
    pub fn write_hex<T>(&mut self, hex_offset: &str, value: T) -> Result<(), MemoryError>
    where
        T: Copy,
    {
        let offset = u64::from_str_radix(hex_offset, 16).map_err(|_| MemoryError::ParseError)?;
        self.write(offset, value)
    }

    /// Read a little-endian u32 value at a specific address
    pub fn read_u32_le(&mut self, address: u64) -> Result<u32, MemoryError> {
        let bytes = self.read_bytes(address, 4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    /// Read a little-endian u64 value at a specific address
    pub fn read_u64_le(&mut self, address: u64) -> Result<u64, MemoryError> {
        let bytes = self.read_bytes(address, 8)?;
        Ok(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    /// Write a little-endian u32 value at a specific address
    pub fn write_u32_le(&mut self, address: u64, value: u32) -> Result<(), MemoryError> {
        let bytes = value.to_le_bytes();
        self.write_bytes(address, &bytes)
    }

    /// Write a little-endian u64 value at a specific address
    pub fn write_u64_le(&mut self, address: u64, value: u64) -> Result<(), MemoryError> {
        let bytes = value.to_le_bytes();
        self.write_bytes(address, &bytes)
    }

    /// Read raw bytes from a specific address
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to read from
    /// * `size` - The number of bytes to read
    ///
    /// # Returns
    /// * `Result<Vec<u8>, MemoryError>` - The bytes read or an error
    pub fn read_bytes(&mut self, address: u64, size: usize) -> Result<Vec<u8>, MemoryError> {
        let mut buffer = vec![0u8; size];
        self.handle
            .seek(std::io::SeekFrom::Start(address))
            .map_err(MemoryError::IoError)?;
        self.handle
            .read_exact(&mut buffer)
            .map_err(MemoryError::IoError)?;
        Ok(buffer)
    }

    /// Write raw bytes to a specific address
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to write to
    /// * `data` - The bytes to write
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - Success or an error
    pub fn write_bytes(&mut self, address: u64, data: &[u8]) -> Result<(), MemoryError> {
        self.handle
            .seek(std::io::SeekFrom::Start(address))
            .map_err(MemoryError::IoError)?;
        self.handle.write_all(data).map_err(MemoryError::IoError)?;
        self.handle.flush().map_err(MemoryError::IoError)?;
        Ok(())
    }

    /// Read a null-terminated string from a specific address
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to read from
    /// * `max_length` - The maximum number of bytes to read
    ///
    /// # Returns
    /// * `Result<String, MemoryError>` - The string read or an error
    pub fn read_string(&mut self, address: u64, max_length: usize) -> Result<String, MemoryError> {
        let bytes = self.read_bytes(address, max_length)?;
        let null_pos = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
        String::from_utf8(bytes[..null_pos].to_vec()).map_err(|_| MemoryError::ParseError)
    }

    fn find_process_id(name: &str) -> Result<u64, MemoryError> {
        let proc_dir = fs::read_dir("/proc").map_err(MemoryError::IoError)?;

        for entry in proc_dir {
            let entry = entry.map_err(MemoryError::IoError)?;
            let dir_name = entry
                .file_name()
                .into_string()
                .map_err(|_| MemoryError::ParseError)?;

            if let Ok(pid) = dir_name.parse::<u64>() {
                let comm_path = format!("/proc/{pid}/comm");
                if let Ok(mut file) = fs::File::open(comm_path) {
                    let mut contents = String::new();
                    if file.read_to_string(&mut contents).is_ok() && contents.trim() == name {
                        return Ok(pid);
                    }
                }
            }
        }

        Err(MemoryError::ProcessNotFound(name.to_string()))
    }

    fn find_base_address(pid: u64, name: &str) -> Result<u64, MemoryError> {
        let maps_path = format!("/proc/{pid}/maps");
        let maps_file = fs::File::open(maps_path).map_err(MemoryError::IoError)?;
        let buf_reader = BufReader::new(maps_file);

        for line_result in buf_reader.lines() {
            let line = line_result.map_err(MemoryError::IoError)?;
            if !line.contains(name) {
                continue;
            }

            let Some(base_memory_range) = line.split_whitespace().next() else {
                continue;
            };
            let Some(base_memory) = base_memory_range.split('-').next() else {
                continue;
            };

            if let Ok(base_memory) = u64::from_str_radix(base_memory, 16) {
                return Ok(base_memory);
            }
        }

        Err(MemoryError::BaseAddressNotFound(name.to_string()))
    }

    fn get_memory_handle(pid: u64) -> Result<File, MemoryError> {
        let proc_mem_path = format!("/proc/{pid}/mem");
        fs::File::options()
            .read(true)
            .write(true)
            .open(proc_mem_path)
            .map_err(|_| MemoryError::InsufficientPermissions)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hex_macro() {
        assert_eq!(hex!("FF"), 255);
        assert_eq!(hex!("100"), 256);
        assert_eq!(hex!("8320b84"), 137497476);
    }

    #[test]
    fn test_memory_error_display() {
        let err = MemoryError::ProcessNotFound("test".to_string());
        assert_eq!(format!("{err}"), "Process 'test' not found");
    }
}
