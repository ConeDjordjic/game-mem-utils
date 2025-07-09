//! # Game Memory Utils
//!
//! A Rust library for reading and writing process memory on Linux, designed for easy trainer
//! creation!
//!
//! ## Features
//!
//! - **Process Memory Access**: Read and write to any process memory using `/proc/pid/mem`
//! - **Pattern Scanning**: Advanced byte pattern matching with wildcard support
//! - **Module Management**: Find and work with loaded modules/libraries
//! - **Safe Memory Operations**: Type-safe memory operations with comprehensive error handling
//! - **Ptrace Integration**: Automatic process attachment and detachment
//! - **Debug Support**: Optional debug output for troubleshooting memory operations
//!
//! ## Quick Start
//! ``` no_run
//! use game_mem_utils::{GameMemUtils, hex};
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // Attach to a process by name (debug mode disabled)
//!     let mut mem = GameMemUtils::new("my_game", false)?;
//!     
//!     // Read a u32 value at absolute address
//!     let gold: u32 = mem.read_at(hex!("8320b84"))?;
//!     println!("Current gold: {gold}");
//!     
//!     // Write a new value
//!     mem.write_at(hex!("8320b84"), 999999u32)?;
//!     
//!     // Pattern scanning across all process memory
//!     if let Some(addr) = mem.pattern_scan_all_process_memory("48 89 ?? ?? ?? C3")? {
//!         println!("Pattern found at: 0x{:x}", addr);
//!     }
//!     
//!     Ok(())
//! }
//! ```
//!
//! ## Memory Operations
//!
//! ### Reading Memory
//!
//! ```rust
//! # use game_mem_utils::{GameMemUtils, hex};
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let mut mem = GameMemUtils::new("game_process", false)?;
//!
//! // Read at absolute address
//! let value: u32 = mem.read_at(0x12345678)?;
//!
//! // Read at offset from base address
//! let value: u32 = mem.read(0x1000)?;
//!
//! // Read using hex string offset
//! let value: u32 = mem.read_hex("1000")?;
//!
//! // Read raw bytes
//! let bytes = mem.read_bytes(0x12345678, 16)?;
//!
//! // Read null-terminated string
//! let text = mem.read_string(0x12345678, 64)?;
//!
//! // Read little-endian integers
//! let val_u32 = mem.read_u32_le(0x12345678)?;
//! let val_u64 = mem.read_u64_le(0x12345678)?;
//! # Ok(())
//! # }
//! ```
//!
//! ### Writing Memory
//!
//! ```rust
//! # use game_mem_utils::{GameMemUtils, hex};
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let mut mem = GameMemUtils::new("game_process", false)?;
//!
//! // Write at absolute address
//! mem.write_at(0x12345678, 42u32)?;
//!
//! // Write at offset from base address
//! mem.write(0x1000, 100i32)?;
//!
//! // Write using hex string offset
//! mem.write_hex("1000", 200u32)?;
//!
//! // Write raw bytes
//! mem.write_bytes(0x12345678, &[0x41, 0x42, 0x43])?;
//!
//! // Write little-endian integers
//! mem.write_u32_le(0x12345678, 12345)?;
//! mem.write_u64_le(0x12345678, 9876543210)?;
//! # Ok(())
//! # }
//! ```
//!
//! ## Pattern Scanning
//!
//! Pattern scanning allows you to find specific byte sequences in memory with support for wildcards:
//!
//! ```rust
//! # use game_mem_utils::{GameMemUtils, hex};
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let mut mem = GameMemUtils::new("game_process", false)?;
//!
//! // Scan all readable+executable memory regions
//! if let Some(addr) = mem.pattern_scan_all_process_memory("48 89 ?? ?? ?? C3")? {
//!     println!("Pattern found at: 0x{:x}", addr);
//! }
//!
//! // Scan specific module
//! if let Some(addr) = mem.pattern_scan_module("game.exe", "89 46 08 ?? C0")? {
//!     println!("Pattern found in module at: 0x{:x}", addr);
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ### Pattern Syntax
//!
//! - `"48 89 E5"` - Exact bytes (hex values separated by spaces)
//! - `"48 ?? E5"` - Wildcard in middle (use `??` or `?` for wildcards)
//! - `"?? 89 ?? ?? ?? C3"` - Multiple wildcards
//!
//! ## Module Management
//!
//! ```rust
//! # use game_mem_utils::{GameMemUtils, hex};
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let mut mem = GameMemUtils::new("game_process", false)?;
//!
//! // Get process info
//! let pid = mem.pid();
//! let base_addr = mem.base_address();
//!
//! // Find module base address
//! let module_base = mem.find_module_base("libgame.so")?;
//!
//! // List all loaded modules
//! let modules = mem.find_loaded_modules()?;
//! for (name, base, end, permissions) in &modules {
//!     println!("{}: 0x{:x}-0x{:x} ({})", name, base, end, permissions);
//! }
//!
//! // Filter modules by regex
//! let filtered = mem.filter_modules_by_regex(&modules, r".*\.so$")?;
//! # Ok(())
//! # }
//! ```
//!
//! ## Error Handling
//!
//! The library provides comprehensive error handling through the [`MemoryError`] enum:
//!
//! ```rust
//! use game_mem_utils::{GameMemUtils, MemoryError};
//!
//! match GameMemUtils::new("nonexistent_process", false) {
//!     Ok(mem) => {
//!         // Use mem...
//!     }
//!     Err(MemoryError::ProcessNotFound(name)) => {
//!         eprintln!("Process '{}' not found", name);
//!     }
//!     Err(MemoryError::InsufficientPermissions) => {
//!         eprintln!("Need sudo or appropriate permissions");
//!     }
//!     Err(e) => eprintln!("Other error: {}", e),
//! }
//! ```
//!
//! ## Debug Mode
//!
//! Enable debug output to troubleshoot memory operations:
//!
//! ```rust
//! # use game_mem_utils::{GameMemUtils, hex};
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! // Enable debug mode (second parameter = true)
//! let mut mem = GameMemUtils::new("my_game", true)?;
//!
//! // Debug output will show:
//! // - Memory region scanning details
//! // - Pattern matching progress
//! // - Ptrace operation results
//! // - Module loading information
//! # Ok(())
//! # }
//! ```
//!
//! ## Requirements
//!
//! - **Linux**: This library is Linux-specific and uses `/proc/pid/mem` and `ptrace`
//! - **Permissions**: May require `sudo` or appropriate capabilities to attach to processes
//! - **Target Process**: The target process should be running and accessible
//!
//! ## Safety Notes
//!
//! - This library directly manipulates process memory, which can cause crashes if used incorrectly
//! - Always validate addresses and data before writing
//! - The target process will be temporarily stopped during attachment
//! - Automatic cleanup ensures processes are properly detached when [`GameMemUtils`] is dropped
//!
//! ## Platform Support
//!
//! - Linux (x86_64, ARM64, and other architectures supported by Rust)
//! - Wine/Proton games (with some limitations on module detection)

use std::{
    error::Error,
    fmt, fs,
    io::{self, BufRead, BufReader, Read, Seek, Write},
    mem,
    num::ParseIntError,
    ptr,
};

// Only PTRACE_ATTACH and PTRACE_DETACH are needed for ptrace
use libc::{PTRACE_ATTACH, PTRACE_DETACH, c_void, pid_t, ptrace};
use memchr::memchr;
use regex::Regex;

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
    ModuleNotFound(String),
    InsufficientPermissions,
    IoError(io::Error),
    ParseError(String),
    PatternParseError(String),
    InvalidAddress,
    PtraceError(String),
}

impl fmt::Display for MemoryError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MemoryError::ProcessNotFound(name) => write!(f, "Process '{name}' not found"),
            MemoryError::BaseAddressNotFound(name) => {
                write!(f, "Base address for '{name}' not found")
            }
            MemoryError::ModuleNotFound(name) => write!(f, "Module '{name}' not found"),
            MemoryError::InsufficientPermissions => {
                write!(f, "Insufficient permissions to access memory")
            }
            MemoryError::IoError(e) => write!(f, "IO error: {e}"),
            MemoryError::ParseError(e) => write!(f, "Failed to parse data: {e}"),
            MemoryError::PatternParseError(e) => write!(f, "Couldn't parse pattern: {e}"),
            MemoryError::InvalidAddress => write!(f, "Invalid memory address"),
            MemoryError::PtraceError(e) => write!(f, "Ptrace error: {e}"),
        }
    }
}

impl Error for MemoryError {}

// Allow easy conversion from io::Error to MemoryError using `?`
impl From<io::Error> for MemoryError {
    fn from(e: io::Error) -> Self {
        MemoryError::IoError(e)
    }
}

// Allow easy conversion from ParseIntError to MemoryError using `?`
impl From<ParseIntError> for MemoryError {
    fn from(e: ParseIntError) -> Self {
        MemoryError::ParseError(e.to_string())
    }
}

/// Main struct for game memory manipulation utilities using ptrace and /proc/pid/mem
pub struct GameMemUtils {
    pid: pid_t,
    base_address: u64,
    attached: bool,
    mem_file: fs::File,
    debug_enabled: bool, // NEW: Debug flag
}

impl GameMemUtils {
    /// Create a new GameMemUtils instance by process name
    ///
    /// # Arguments
    /// * `process_name` - The name of the process to attach to
    /// * `debug_enabled` - Whether to enable debug output for internal operations.
    ///
    /// # Returns
    /// * `Result<Self, MemoryError>` - The GameMemUtils instance or an error
    pub fn new(process_name: &str, debug_enabled: bool) -> Result<Self, MemoryError> {
        let pid = Self::find_process_id(process_name)?;
        let base_address = Self::find_base_address(pid, process_name)?;

        let mut utils = GameMemUtils {
            pid: pid_t::try_from(pid).map_err(|e| MemoryError::ParseError(e.to_string()))?,
            base_address,
            attached: false,
            mem_file: fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(format!("/proc/{pid}/mem"))?,
            debug_enabled, // NEW: Initialize debug_enabled
        };

        utils.attach()?;
        Ok(utils)
    }

    /// Create a new GameMemUtils instance from a process ID
    ///
    /// # Arguments
    /// * `pid` - The process ID to attach to
    /// * `debug_enabled` - Whether to enable debug output for internal operations.
    ///
    /// # Returns
    /// * `Result<Self, MemoryError>` - The GameMemUtils instance or an error
    pub fn from_pid(pid: u64, debug_enabled: bool) -> Result<Self, MemoryError> {
        // MODIFIED signature
        let mut utils = GameMemUtils {
            pid: pid_t::try_from(pid).map_err(|e| MemoryError::ParseError(e.to_string()))?,
            base_address: 0, // Base address will be set later or is not strictly needed for direct address reads
            attached: false,
            mem_file: fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(format!("/proc/{pid}/mem"))?,
            debug_enabled, // NEW: Initialize debug_enabled
        };
        utils.attach()?;
        Ok(utils)
    }

    /// Attach to the process via ptrace
    ///
    /// # Safety
    /// This function performs a `ptrace(PTRACE_ATTACH)` system call, which is inherently unsafe.
    /// It attempts to attach to the target process and then waits for it to stop.
    fn attach(&mut self) -> Result<(), MemoryError> {
        errno::set_errno(errno::Errno(0)); // Reset errno before the call
        let res = unsafe {
            ptrace(
                PTRACE_ATTACH,
                self.pid,
                ptr::null_mut::<c_void>(),
                ptr::null_mut::<c_void>(),
            )
        };

        if res != 0 {
            let current_errno = errno::errno();
            if self.debug_enabled {
                eprintln!(
                    "DEBUG: ptrace(PTRACE_ATTACH) failed for PID {}. errno: {} ({})",
                    self.pid, current_errno.0, current_errno
                );
            }
            return Err(MemoryError::PtraceError(format!(
                "Failed to attach to PID {}: {}",
                self.pid, current_errno
            )));
        }

        // Wait for the process to stop after attach
        let mut status = 0;
        errno::set_errno(errno::Errno(0)); // Reset errno before waitpid
        let wait_res = unsafe { libc::waitpid(self.pid, &mut status, 0) };

        if wait_res == -1 {
            let current_errno = errno::errno();
            if self.debug_enabled {
                eprintln!(
                    "DEBUG: waitpid failed for PID {} after attach. errno: {} ({})",
                    self.pid, current_errno.0, current_errno
                );
            }
            return Err(MemoryError::PtraceError(format!(
                "Failed to wait for PID {} after attach: {}",
                self.pid, current_errno
            )));
        }
        self.attached = true;
        Ok(())
    }

    /// Detach from the process via ptrace
    ///
    /// # Safety
    /// This function performs a `ptrace(PTRACE_DETACH)` system call, which is inherently unsafe.
    /// It detaches from the target process, allowing it to resume execution.
    pub fn detach(&mut self) -> Result<(), MemoryError> {
        if !self.attached {
            return Ok(());
        }

        errno::set_errno(errno::Errno(0)); // Reset errno before the call
        let res = unsafe {
            ptrace(
                PTRACE_DETACH,
                self.pid,
                ptr::null_mut::<c_void>(),
                ptr::null_mut::<c_void>(),
            )
        };

        if res != 0 {
            let current_errno = errno::errno();
            if self.debug_enabled {
                eprintln!(
                    "DEBUG: ptrace(PTRACE_DETACH) failed for PID {}. errno: {} ({})",
                    self.pid, current_errno.0, current_errno
                );
            }
            return Err(MemoryError::PtraceError(format!(
                "Failed to detach from PID {}: {}",
                self.pid, current_errno
            )));
        }
        self.attached = false;
        Ok(())
    }

    /// Get the process ID
    ///
    /// # Returns
    /// * `u64` - The process ID.
    pub fn pid(&self) -> u64 {
        self.pid as u64
    }

    /// Get the base address
    ///
    /// # Returns
    /// * `u64` - The base address.
    pub fn base_address(&self) -> u64 {
        self.base_address
    }

    /// Set the base address manually
    ///
    /// # Arguments
    /// * `address` - The new base address.
    pub fn set_base_address(&mut self, address: u64) {
        self.base_address = address;
    }

    /// Scan all readable and executable memory regions of the process for a byte pattern.
    /// This mimics a broader "Full scan scope" found in tools like Pince, especially
    /// useful when specific module mappings are incomplete (e.g., under Wine/Proton).
    ///
    /// # Arguments
    /// * `pattern` - The pattern string in hex with spaces, where wildcards are represented by "??" or "?". Example: "89 46 08 ?? C0"
    ///
    /// # Returns
    /// * `Result<Option<u64>, MemoryError>` - The absolute address of the first match if found, or None if not found, or an error.
    pub fn pattern_scan_all_process_memory(
        &mut self,
        pattern: &str,
    ) -> Result<Option<u64>, MemoryError> {
        let all_modules = self.find_loaded_modules()?; // Get ALL memory mappings from /proc/PID/maps

        // Filter for regions that are readable ('r') and executable ('x').
        // Patterns are almost exclusively found in these types of regions.
        let target_regions: Vec<(u64, u64, String)> = all_modules
            .iter()
            .filter(|(_, _, _, perms)| perms.contains('r') && perms.contains('x'))
            .map(|(name, base, end, _perms)| (*base, *end, name.clone())) // Keep name for debug printing
            .collect();

        if target_regions.is_empty() {
            if self.debug_enabled {
                eprintln!("DEBUG: No readable+executable regions found to scan in the process.");
            }
            return Ok(None);
        }

        let (pattern_bytes, mask) = Self::parse_pattern(pattern)?;

        // Iterate through each filtered region and perform the scan
        for (base, end, name) in target_regions {
            let size = (end - base) as usize;

            if size == 0 {
                if self.debug_enabled {
                    eprintln!("DEBUG: Skipping empty region {base:#x}-{end:#x} (name: {name})",);
                }
                continue;
            }

            if self.debug_enabled {
                eprintln!(
                    "DEBUG: Scanning all-mem region {base:#x}-{end:#x} (size: {size} bytes, name: {name})",
                );
            }

            // Attempt to read the bytes for the current region
            let buffer_result = self.read_bytes(base, size);

            match buffer_result {
                Ok(buffer) => {
                    // If reading succeeded, try to find the pattern in this buffer
                    if let Some(offset) = Self::find_pattern(&buffer, &pattern_bytes, &mask) {
                        let found_address = base + offset as u64;
                        if self.debug_enabled {
                            eprintln!(
                                "DEBUG: Pattern found at: {found_address:#x} in region {base:#x}-{end:#x} (name: {name})",
                            );
                        }
                        return Ok(Some(found_address)); // Pattern found, return the absolute address
                    }
                }
                Err(e) => {
                    // Log the error but continue to the next region.
                    // Some memory regions might genuinely be unreadable for various reasons.
                    if self.debug_enabled {
                        eprintln!(
                            "DEBUG: Failed to read all-mem region {base:#x}-{end:#x} (name: {name}): {e}",
                        );
                    }
                }
            }
        }
        Ok(None)
    }

    /// Find all loaded modules' addresses, start and end
    ///
    /// This function parses the `/proc/{pid}/maps` file to retrieve information
    /// about all memory mappings of the target process. Each entry includes
    /// the memory range, permissions, and the associated file path if applicable.
    ///
    /// # Returns
    /// * `Result<Vec<(String, u64, u64, String)>, MemoryError>` - A vector of tuples,
    ///   where each tuple contains (pathname, base address, end address, permissions string),
    ///   or a `MemoryError` if the process or its maps file cannot be accessed.
    pub fn find_loaded_modules(&self) -> Result<Vec<(String, u64, u64, String)>, MemoryError> {
        let maps_path = format!("/proc/{}/maps", self.pid);
        let file = fs::File::open(maps_path)?;
        let reader = BufReader::new(file);
        let mut modules = Vec::new();

        for line in reader.lines() {
            let line = line?;

            let parts: Vec<&str> = line.split_whitespace().collect();

            if parts.len() < 5 {
                // Need at least address, perms, offset, device, inode
                continue;
            }

            let range = parts[0];
            let permissions = parts[1];

            let pathname_start_idx = if parts.len() >= 6 && parts[5].starts_with('/') {
                5
            } else {
                // If it's not a file-backed mapping, pathname will be empty or a label like [stack]
                parts.len()
            };
            let pathname = parts[pathname_start_idx..].join(" ");

            let mut addr_parts = range.split('-');
            let (Some(start_str), Some(end_str)) = (addr_parts.next(), addr_parts.next()) else {
                continue;
            };

            let start = u64::from_str_radix(start_str, 16)?;
            let end = u64::from_str_radix(end_str, 16)?;

            modules.push((pathname, start, end, permissions.to_string())); // Store permissions too
        }

        Ok(modules)
    }

    /// Filter loaded modules by some pattern
    ///
    /// This function takes a slice of loaded modules (as returned by `find_loaded_modules`)
    /// and filters them based on a provided regular expression pattern applied to their
    /// pathname.
    ///
    /// # Arguments
    /// * `modules` - Slice of loaded modules, where each module is a tuple of (pathname, base address, end address, permissions string).
    /// * `pattern` - A regular expression string to match against the module pathnames.
    ///
    /// # Returns
    /// * `Result<Vec<(String, u64, u64, String)>, regex::Error>` - A vector of modules
    ///   whose pathnames satisfy the given regex pattern, or a `regex::Error` if the
    ///   pattern is invalid.
    pub fn filter_modules_by_regex(
        &self,
        modules: &[(String, u64, u64, String)], // Updated type
        pattern: &str,
    ) -> Result<Vec<(String, u64, u64, String)>, regex::Error> {
        let re = Regex::new(pattern)?;
        Ok(modules
            .iter()
            .filter(|(path, _, _, _)| re.is_match(path))
            .cloned()
            .collect())
    }

    /// Find the base address of a specific module
    ///
    /// This function searches for a module by its name within the target process's
    /// memory mappings and returns its base address.
    ///
    /// # Arguments
    /// * `module_name` - The name of the module to find (e.g., "libc.so.6").
    ///
    /// # Returns
    /// * `Result<u64, MemoryError>` - The base address of the module if found,
    ///   or a `MemoryError` if the module is not found or cannot be accessed.
    pub fn find_module_base(&self, module_name: &str) -> Result<u64, MemoryError> {
        Self::find_base_address(self.pid as u64, module_name)
    }

    /// Scan the memory of a specified module for a byte pattern with wildcards.
    ///
    /// This function attempts to find the first memory mapping associated with the
    /// given `module_name` and then scans that region for the specified byte pattern.
    /// Note that for processes running under Wine/Proton, a module might be mapped
    /// across multiple non-contiguous regions, and this function will only scan the first one found.
    /// For a more comprehensive scan, consider `pattern_scan_all_process_memory`.
    ///
    /// # Arguments
    /// * `module_name` - The exact name of the module to scan (e.g., "hota.dll").
    /// * `pattern` - The pattern string in hex with spaces, where wildcards are represented by "??" or "?". Example: "89 46 08 ?? C0"
    ///
    /// # Returns
    /// * `Result<Option<u64>, MemoryError>` - The absolute address of the first match if found,
    ///   or `None` if not found, or a `MemoryError` if the module is not found or memory
    ///   cannot be read.
    pub fn pattern_scan_module(
        &mut self,
        module_name: &str,
        pattern: &str,
    ) -> Result<Option<u64>, MemoryError> {
        let modules = self.find_loaded_modules()?; // Returns Vec<(String, u64, u64, String)>

        // This filters for the first region matching the module name.
        let target_module_regions: Vec<(u64, u64)> = modules
            .iter()
            .filter(|(name, _, _, _)| name.contains(module_name))
            .map(|(_, base, end, _)| (*base, *end))
            .collect();

        if target_module_regions.is_empty() {
            return Err(MemoryError::ModuleNotFound(module_name.to_string()));
        }

        let (pattern_bytes, mask) = Self::parse_pattern(pattern)?;

        for (base, end) in target_module_regions {
            let size = (end - base) as usize;

            if size == 0 {
                if self.debug_enabled {
                    eprintln!("DEBUG: Skipping empty region {base:#x}-{end:#x} for {module_name}",);
                }
                continue;
            }

            if self.debug_enabled {
                eprintln!(
                    "DEBUG: Scanning region {base:#x}-{end:#x} (size: {size} bytes) for {module_name}",
                );
            }

            let buffer_result = self.read_bytes(base, size);

            match buffer_result {
                Ok(buffer) => {
                    if let Some(offset) = Self::find_pattern(&buffer, &pattern_bytes, &mask) {
                        return Ok(Some(base + offset as u64));
                    }
                }
                Err(e) => {
                    if self.debug_enabled {
                        eprintln!(
                            "DEBUG: Failed to read module region {base:#x}-{end:#x} for {module_name}: {e}",
                        );
                    }
                }
            }
        }

        Ok(None)
    }

    /// Parse a pattern string with wildcards into a byte vector and mask.
    ///
    /// This internal helper function converts a human-readable pattern string
    /// (e.g., "AB ?? CD") into a byte vector and a boolean mask. The mask indicates
    /// which bytes are significant (true) and which are wildcards (false).
    ///
    /// # Arguments
    /// * `pattern` - The pattern string in hex with spaces, where wildcards are represented by "??" or "?".
    ///
    /// # Returns
    /// * `Result<(Vec<u8>, Vec<bool>), MemoryError>` - A tuple containing the parsed bytes
    ///   and the corresponding mask, or a `MemoryError::PatternParseError` if the pattern is invalid.
    fn parse_pattern(pattern: &str) -> Result<(Vec<u8>, Vec<bool>), MemoryError> {
        let mut bytes = Vec::new();
        let mut mask = Vec::new();

        for token in pattern.split_whitespace() {
            match token {
                "?" | "??" => {
                    bytes.push(0);
                    mask.push(false);
                }
                _ => {
                    let byte = u8::from_str_radix(token, 16).map_err(|_| {
                        MemoryError::PatternParseError(format!("Invalid byte token '{token}'"))
                    })?;
                    bytes.push(byte);
                    mask.push(true);
                }
            }
        }
        if bytes.is_empty() {
            return Err(MemoryError::PatternParseError(
                "Pattern cannot be empty".to_string(),
            ));
        }
        Ok((bytes, mask))
    }

    /// Find the pattern with mask inside the buffer.
    ///
    /// This internal helper function efficiently searches for a byte pattern within a given buffer,
    /// respecting wildcard bytes defined by the mask. It uses `memchr` for a fast initial scan
    /// for the first non-wildcard byte, then performs a full comparison.
    ///
    /// # Arguments
    /// * `buffer` - The slice of bytes to search within.
    /// * `pattern` - The byte pattern to search for.
    /// * `mask` - A boolean mask indicating which bytes in the pattern are significant (`true`)
    ///   and which are wildcards (`false`).
    ///
    /// # Returns
    /// * `Option<usize>` - The starting offset of the first match in the buffer if found,
    ///   or `None` if the pattern is not found.
    fn find_pattern(buffer: &[u8], pattern: &[u8], mask: &[bool]) -> Option<usize> {
        if pattern.is_empty() {
            return None; // Or 0 if an empty pattern should match at start
        }

        // Find the index of the first non-wildcard byte in the pattern
        let first_masked_byte_idx = mask.iter().position(|&m| m)?; // Returns None if all are wildcards
        let first_significant_byte = pattern[first_masked_byte_idx];

        let mut current_search_start_offset = 0;

        // Use memchr to quickly find occurrences of the first non-wildcard byte
        while let Some(mut pos) = memchr(
            first_significant_byte,
            &buffer[current_search_start_offset..],
        ) {
            pos += current_search_start_offset; // Adjust `pos` to be an absolute offset in the original buffer

            // Calculate the potential starting position of the full pattern based on where
            // the `first_significant_byte` was found.
            // `checked_sub` prevents underflow if `pos < first_masked_byte_idx`.
            let potential_pattern_start = pos.checked_sub(first_masked_byte_idx)?;

            // If the potential pattern start plus its full length exceeds the buffer, we can stop.
            if potential_pattern_start + pattern.len() > buffer.len() {
                break; // No more full matches possible
            }

            // Now, perform a full pattern check from this potential start position
            let mut full_match = true;
            for i in 0..pattern.len() {
                // Only compare bytes where the mask indicates a specific value
                if mask[i] && buffer[potential_pattern_start + i] != pattern[i] {
                    full_match = false;
                    break;
                }
            }

            if full_match {
                return Some(potential_pattern_start); // Found a full match!
            }

            // If no full match, advance the search starting point past the current `pos`
            // to find the next potential `first_significant_byte`
            current_search_start_offset = pos + 1;
        }

        None // Pattern not found in the entire buffer
    }

    /// Read a value at a specific absolute address using `/proc/pid/mem`.
    ///
    /// This function reads `mem::size_of::<T>()` bytes from the specified absolute
    /// memory address in the target process and attempts to interpret them as type `T`.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to read from.
    ///
    /// # Type Parameters
    /// * `T` - The type of the value to read. Must implement `Copy`.
    ///
    /// # Returns
    /// * `Result<T, MemoryError>` - The read value, or a `MemoryError` if the address
    ///   is invalid or memory cannot be read.
    ///
    /// # Safety
    /// This function uses `ptr::read_unaligned` which is unsafe. It is assumed that
    /// the memory at `address` contains a valid representation of `T`.
    pub fn read_at<T>(&self, address: u64) -> Result<T, MemoryError>
    where
        T: Copy,
    {
        let size = mem::size_of::<T>();
        if size == 0 {
            return Err(MemoryError::InvalidAddress);
        }
        let mut buffer = vec![0u8; size];

        self.read_bytes_into(address, &mut buffer)?;

        // Safety: The buffer is guaranteed to be the correct size of T and has been filled
        // with bytes from the process's memory. `ptr::read_unaligned` is used because the
        // address may not be aligned to T's requirements, which is common in memory scanning.
        Ok(unsafe { ptr::read_unaligned(buffer.as_ptr() as *const T) })
    }

    /// Read a value at an offset from the base address.
    ///
    /// This function reads `mem::size_of::<T>()` bytes from an address calculated as
    /// `self.base_address + offset` in the target process and attempts to interpret them as type `T`.
    ///
    /// # Arguments
    /// * `offset` - The offset from the base address to read from.
    ///
    /// # Type Parameters
    /// * `T` - The type of the value to read. Must implement `Copy`.
    ///
    /// # Returns
    /// * `Result<T, MemoryError>` - The read value, or a `MemoryError` if the address
    ///   is invalid or memory cannot be read.
    pub fn read<T>(&self, offset: u64) -> Result<T, MemoryError>
    where
        T: Copy,
    {
        self.read_at(self.base_address + offset)
    }

    /// Read a value at a hexadecimal offset from the base address.
    ///
    /// This function parses a hexadecimal string representing an offset,
    /// then reads `mem::size_of::<T>()` bytes from `self.base_address + parsed_offset`
    /// in the target process and attempts to interpret them as type `T`.
    ///
    /// # Arguments
    /// * `hex_offset` - The hexadecimal string representing the offset (e.g., "1A4F").
    ///
    /// # Type Parameters
    /// * `T` - The type of the value to read. Must implement `Copy`.
    ///
    /// # Returns
    /// * `Result<T, MemoryError>` - The read value, or a `MemoryError` if the offset
    ///   string is invalid, the address is invalid, or memory cannot be read.
    pub fn read_hex<T>(&self, hex_offset: &str) -> Result<T, MemoryError>
    where
        T: Copy,
    {
        let offset = u64::from_str_radix(hex_offset, 16)?;
        self.read(offset)
    }

    /// Write a value at a specific absolute address using `/proc/pid/mem`.
    ///
    /// This function writes `mem::size_of::<T>()` bytes from the provided `value`
    /// to the specified absolute memory address in the target process.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to write to.
    /// * `value` - The value to write.
    ///
    /// # Type Parameters
    /// * `T` - The type of the value to write. Must implement `Copy`.
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - `Ok(())` on success, or a `MemoryError` if
    ///   memory cannot be written to (e.g., due to permissions).
    ///
    /// # Safety
    /// This function directly writes to process memory. Incorrect usage can corrupt
    /// the target process's state, leading to crashes or undefined behavior.
    pub fn write_at<T>(&self, address: u64, value: T) -> Result<(), MemoryError>
    where
        T: Copy,
    {
        let size = mem::size_of::<T>();
        // Safety: `value` is a valid T. The pointer is valid for `size` bytes.
        // The slice's lifetime is confined to this function, ensuring `value` outlives it.
        let buffer = unsafe { std::slice::from_raw_parts((&value) as *const T as *const u8, size) };
        self.write_bytes(address, buffer)
    }

    /// Write a value at an offset from the base address.
    ///
    /// This function writes `mem::size_of::<T>()` bytes from the provided `value`
    /// to an address calculated as `self.base_address + offset` in the target process.
    ///
    /// # Arguments
    /// * `offset` - The offset from the base address to write to.
    /// * `value` - The value to write.
    ///
    /// # Type Parameters
    /// * `T` - The type of the value to write. Must implement `Copy`.
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - `Ok(())` on success, or a `MemoryError` if
    ///   memory cannot be written to.
    ///
    /// # Safety
    /// This function directly writes to process memory. Incorrect usage can corrupt
    /// the target process's state, leading to crashes or undefined behavior.
    pub fn write<T>(&self, offset: u64, value: T) -> Result<(), MemoryError>
    where
        T: Copy,
    {
        self.write_at(self.base_address + offset, value)
    }

    /// Write a value at a hexadecimal offset from the base address.
    ///
    /// This function parses a hexadecimal string representing an offset,
    /// then writes `mem::size_of::<T>()` bytes from the provided `value`
    /// to `self.base_address + parsed_offset` in the target process.
    ///
    /// # Arguments
    /// * `hex_offset` - The hexadecimal string representing the offset (e.g., "1A4F").
    /// * `value` - The value to write.
    ///
    /// # Type Parameters
    /// * `T` - The type of the value to write. Must implement `Copy`.
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - `Ok(())` on success, or a `MemoryError` if
    ///   the offset string is invalid or memory cannot be written to.
    ///
    /// # Safety
    /// This function directly writes to process memory. Incorrect usage can corrupt
    /// the target process's state, leading to crashes or undefined behavior.
    pub fn write_hex<T>(&self, hex_offset: &str, value: T) -> Result<(), MemoryError>
    where
        T: Copy,
    {
        let offset = u64::from_str_radix(hex_offset, 16)?;
        self.write(offset, value)
    }

    /// Read a little-endian u32 value at a specific address.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to read from.
    ///
    /// # Returns
    /// * `Result<u32, MemoryError>` - The read `u32` value, or a `MemoryError` if
    ///   memory cannot be read.
    pub fn read_u32_le(&self, address: u64) -> Result<u32, MemoryError> {
        let mut bytes = [0u8; 4];
        self.read_bytes_into(address, &mut bytes)?;
        Ok(u32::from_le_bytes(bytes))
    }

    /// Read a little-endian u64 value at a specific address.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to read from.
    ///
    /// # Returns
    /// * `Result<u64, MemoryError>` - The read `u64` value, or a `MemoryError` if
    ///   memory cannot be read.
    pub fn read_u64_le(&self, address: u64) -> Result<u64, MemoryError> {
        let mut bytes = [0u8; 8];
        self.read_bytes_into(address, &mut bytes)?;
        Ok(u64::from_le_bytes(bytes))
    }

    /// Write a little-endian u32 value at a specific address.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to write to.
    /// * `value` - The `u32` value to write.
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - `Ok(())` on success, or a `MemoryError` if
    ///   memory cannot be written to.
    pub fn write_u32_le(&self, address: u64, value: u32) -> Result<(), MemoryError> {
        self.write_bytes(address, &value.to_le_bytes())
    }

    /// Write a little-endian u64 value at a specific address.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to write to.
    /// * `value` - The `u64` value to write.
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - `Ok(())` on success, or a `MemoryError` if
    ///   memory cannot be written to.
    pub fn write_u64_le(&self, address: u64, value: u64) -> Result<(), MemoryError> {
        self.write_bytes(address, &value.to_le_bytes())
    }

    /// Read raw bytes from a specific address using `/proc/pid/mem`.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to read from.
    /// * `size` - The number of bytes to read.
    ///
    /// # Returns
    /// * `Result<Vec<u8>, MemoryError>` - A vector containing the read bytes,
    ///   or a `MemoryError` if memory cannot be read.
    pub fn read_bytes(&self, address: u64, size: usize) -> Result<Vec<u8>, MemoryError> {
        let mut buffer = vec![0u8; size];
        self.read_bytes_into(address, &mut buffer)?;
        Ok(buffer)
    }

    /// Internal helper: read bytes into a mutable slice using `/proc/pid/mem`.
    ///
    /// This function performs the actual low-level memory read operation by seeking
    /// to the specified address in the `/proc/pid/mem` file and reading bytes into
    /// the provided buffer.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to read from.
    /// * `buffer` - A mutable slice to store the read bytes. The length of the slice
    ///   determines how many bytes will be read.
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - `Ok(())` on success, or a `MemoryError::IoError`
    ///   if the read operation fails.
    fn read_bytes_into(&self, address: u64, buffer: &mut [u8]) -> Result<(), MemoryError> {
        let mut mem_file = &self.mem_file; // Get a mutable reference to the file

        // Safety: We are seeking to an address in the process's memory space.
        // The address comes from /proc/maps, so it should be valid within the process's context.
        // We handle potential IO errors.
        mem_file.seek(io::SeekFrom::Start(address))?;
        mem_file.read_exact(buffer)?; // Read exactly `buffer.len()` bytes

        Ok(())
    }

    /// Write raw bytes to a specific address using `/proc/pid/mem`.
    ///
    /// This function performs the actual low-level memory write operation by seeking
    /// to the specified address in the `/proc/pid/mem` file and writing the provided bytes.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address to write to.
    /// * `data` - The slice of bytes to write.
    ///
    /// # Returns
    /// * `Result<(), MemoryError>` - `Ok(())` on success, or a `MemoryError::IoError`
    ///   if the write operation fails (e.g., due to permissions).
    ///
    /// # Safety
    /// This function directly writes to process memory. Incorrect usage can corrupt
    /// the target process's state, leading to crashes or undefined behavior.
    pub fn write_bytes(&self, address: u64, data: &[u8]) -> Result<(), MemoryError> {
        let mut mem_file = &self.mem_file; // Get a mutable reference to the file

        // Safety: We are seeking to an address in the process's memory space.
        // The address comes from /proc/maps, so it should be valid within the process's context.
        // We handle potential IO errors.
        mem_file.seek(io::SeekFrom::Start(address))?;
        mem_file.write_all(data)?; // Write all bytes from `data`

        Ok(())
    }

    /// Read a null-terminated string from a specific address.
    ///
    /// This function reads bytes from the specified address until a null terminator (0x00)
    /// is encountered or `max_length` bytes have been read. It then attempts to convert
    /// the bytes into a UTF-8 string.
    ///
    /// # Arguments
    /// * `address` - The absolute memory address where the string starts.
    /// * `max_length` - The maximum number of bytes to read to prevent reading past
    ///   the intended string boundary.
    ///
    /// # Returns
    /// * `Result<String, MemoryError>` - The read string, or a `MemoryError` if
    ///   memory cannot be read or the bytes are not valid UTF-8.
    pub fn read_string(&self, address: u64, max_length: usize) -> Result<String, MemoryError> {
        let bytes = self.read_bytes(address, max_length)?;
        let null_pos = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
        String::from_utf8(bytes[..null_pos].to_vec())
            .map_err(|e| MemoryError::ParseError(e.to_string()))
    }

    /// Find process ID by its name by searching `/proc`.
    ///
    /// This function iterates through `/proc` entries to find a process
    /// whose `/proc/{pid}/comm` file content matches the provided `name`.
    ///
    /// # Arguments
    /// * `name` - The executable name of the process (e.g., "firefox", "my_game").
    ///
    /// # Returns
    /// * `Result<u64, MemoryError>` - The PID of the found process, or a
    ///   `MemoryError::ProcessNotFound` if no such process is running.
    fn find_process_id(name: &str) -> Result<u64, MemoryError> {
        fs::read_dir("/proc")?
            .filter_map(Result::ok)
            .filter_map(|entry| entry.file_name().into_string().ok())
            .filter_map(|dir_name| dir_name.parse::<u64>().ok())
            .find(|&pid| {
                if let Ok(comm) = fs::read_to_string(format!("/proc/{pid}/comm")) {
                    return comm.trim() == name;
                }
                false
            })
            .ok_or_else(|| MemoryError::ProcessNotFound(name.to_string()))
    }

    /// Find the base address of a module by parsing `/proc/{pid}/maps`.
    ///
    /// This function scans the `/proc/{pid}/maps` file for the first memory mapping
    /// that contains the given `name` in its path, and returns its starting address.
    /// This is typically used to find the base address of the main executable or a specific DLL/shared library.
    ///
    /// # Arguments
    /// * `pid` - The process ID.
    /// * `name` - The name of the module (e.g., "my_game_executable", "libc.so.6").
    ///
    /// # Returns
    /// * `Result<u64, MemoryError>` - The base address of the module, or a
    ///   `MemoryError::BaseAddressNotFound` if the module is not found.
    fn find_base_address(pid: u64, name: &str) -> Result<u64, MemoryError> {
        let maps_path = format!("/proc/{pid}/maps");
        let maps_file = fs::File::open(maps_path)?;

        for line_result in BufReader::new(maps_file).lines() {
            let line = line_result?;
            if !line.contains(name) {
                continue;
            }

            if let Some(range) = line.split_whitespace().next() {
                if let Some(addr_str) = range.split('-').next() {
                    if let Ok(addr) = u64::from_str_radix(addr_str, 16) {
                        return Ok(addr);
                    }
                }
            }
        }
        Err(MemoryError::BaseAddressNotFound(name.to_string()))
    }
}

impl Drop for GameMemUtils {
    /// Implements the `Drop` trait for `GameMemUtils`.
    ///
    /// When a `GameMemUtils` instance goes out of scope, this method is called.
    /// It ensures that if the tool was attached to a process via `ptrace`, it
    /// detaches cleanly, preventing the traced process from remaining stopped.
    fn drop(&mut self) {
        if self.attached {
            let _ = self.detach(); // We ignore the result here as panicking in drop is discouraged.
        }
        // `self.mem_file` (std::fs::File) automatically closes its file descriptor when dropped.
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
    #[test]
    fn test_parse_pattern() {
        let (bytes, mask) = GameMemUtils::parse_pattern("AB ?? CD 12 ? EF").unwrap();
        assert_eq!(bytes, vec![0xAB, 0, 0xCD, 0x12, 0, 0xEF]);
        assert_eq!(mask, vec![true, false, true, true, false, true]);
    }

    #[test]
    fn test_find_pattern() {
        let buffer = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77];
        let (pattern, mask) = GameMemUtils::parse_pattern("33 ?? 55").unwrap();
        assert_eq!(
            GameMemUtils::find_pattern(&buffer, &pattern, &mask),
            Some(2)
        );

        let (pattern, mask) = GameMemUtils::parse_pattern("11 22 33").unwrap();
        assert_eq!(
            GameMemUtils::find_pattern(&buffer, &pattern, &mask),
            Some(0)
        );

        let (pattern, mask) = GameMemUtils::parse_pattern("99").unwrap();
        assert_eq!(GameMemUtils::find_pattern(&buffer, &pattern, &mask), None);

        // Test with pattern having wildcard at the beginning
        let (pattern, mask) = GameMemUtils::parse_pattern("?? 22 33").unwrap();
        assert_eq!(
            GameMemUtils::find_pattern(&buffer, &pattern, &mask),
            Some(0)
        );

        // Test with pattern having wildcard at the end
        let (pattern, mask) = GameMemUtils::parse_pattern("55 66 ??").unwrap();
        assert_eq!(
            GameMemUtils::find_pattern(&buffer, &pattern, &mask),
            Some(4)
        );

        // Test with pattern having only wildcards (should not find anything)
        let (pattern, mask) = GameMemUtils::parse_pattern("?? ?? ??").unwrap();
        assert_eq!(GameMemUtils::find_pattern(&buffer, &pattern, &mask), None);
    }
}
