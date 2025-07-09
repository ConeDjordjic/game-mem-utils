# Game Memory Utils

A Rust library for reading and writing process memory on Linux, designed for easy trainer creation!

## Features

- **Process Memory Access**: Read and write to any process memory using `/proc/pid/mem`
- **Pattern Scanning**: Advanced byte pattern matching with wildcard support
- **Module Management**: Find and work with loaded modules/libraries
- **Safe Memory Operations**: Type-safe memory operations with error handling
- **Ptrace Integration**: Automatic process attachment and detachment
- **Debug Support**: Optional debug output for troubleshooting

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
game_mem_utils = "0.2.0"
```

Or use `cargo add`:

```bash
cargo add game_mem_utils
```

## Quick Start

```rust
use game_mem_utils::{GameMemUtils, hex};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Attach to a process by name
    let mut mem = GameMemUtils::new("my_game", false)?;

    // Read a u32 value at absolute address
    let gold: u32 = mem.read_at(hex!("8320b84"))?;
    println!("Current gold: {gold}");

    // Write a new value
    mem.write_at(hex!("8320b84"), 999999u32)?;

    // Pattern scanning
    if let Some(addr) = mem.pattern_scan_all_process_memory("48 89 ?? ?? ?? C3")? {
        println!("Pattern found at: 0x{:x}", addr);
    }

    Ok(())
}
```

## Usage Examples

### Process Attachment

```rust
// Attach by process name
let mut mem = GameMemUtils::new("game_process", false)?;

// Attach by PID
let mut mem = GameMemUtils::from_pid(1234, false)?;

// Enable debug output
let mut mem = GameMemUtils::new("game_process", true)?;
```

### Reading Memory

```rust
// Read at absolute address
let value: u32 = mem.read_at(0x12345678)?;

// Read at offset from base address
let value: u32 = mem.read(0x1000)?;

// Read using hex string offset
let value: u32 = mem.read_hex("1000")?;

// Read raw bytes
let bytes = mem.read_bytes(0x12345678, 16)?;

// Read null-terminated string
let text = mem.read_string(0x12345678, 64)?;

// Read specific integer types
let val_u32 = mem.read_u32_le(0x12345678)?;
let val_u64 = mem.read_u64_le(0x12345678)?;
```

### Writing Memory

```rust
// Write at absolute address
mem.write_at(0x12345678, 42u32)?;

// Write at offset from base address
mem.write(0x1000, 100i32)?;

// Write using hex string offset
mem.write_hex("1000", 200u32)?;

// Write raw bytes
mem.write_bytes(0x12345678, &[0x41, 0x42, 0x43])?;

// Write specific integer types
mem.write_u32_le(0x12345678, 12345)?;
mem.write_u64_le(0x12345678, 9876543210)?;
```

### Pattern Scanning

```rust
// Scan all readable+executable memory regions
if let Some(addr) = mem.pattern_scan_all_process_memory("48 89 ?? ?? ?? C3")? {
    println!("Pattern found at: 0x{:x}", addr);
}

// Scan specific module
if let Some(addr) = mem.pattern_scan_module("game.exe", "89 46 08 ?? C0")? {
    println!("Pattern found in module at: 0x{:x}", addr);
}

// Pattern syntax: hex bytes with ?? for wildcards
// Examples:
// "48 89 E5"           - exact bytes
// "48 ?? E5"           - wildcard in middle
// "?? 89 ?? ?? ?? C3"  - multiple wildcards
```

### Module Management

```rust
// Get process and base address info
let pid = mem.pid();
let base_addr = mem.base_address();

// Find module base address
let module_base = mem.find_module_base("libgame.so")?;

// List all loaded modules
let modules = mem.find_loaded_modules()?;
for (name, base, end, permissions) in modules {
    println!("{}: 0x{:x}-0x{:x} ({})", name, base, end, permissions);
}

// Filter modules by regex
let filtered = mem.filter_modules_by_regex(&modules, r".*\.so$")?;
```

### Using the hex! Macro

```rust
use game_mem_utils::hex;

// Convert hex strings to u64 at compile time
let address = hex!("8320b84");  // 0x8320b84
let value: u32 = mem.read_at(address)?;
```

## Error Handling

The library uses a comprehensive error system:

```rust
use game_mem_utils::MemoryError;

match mem.read_at::<u32>(0x12345678) {
    Ok(value) => println!("Read value: {}", value),
    Err(MemoryError::ProcessNotFound(name)) => {
        eprintln!("Process '{}' not found", name);
    }
    Err(MemoryError::InsufficientPermissions) => {
        eprintln!("Need sudo or appropriate permissions");
    }
    Err(MemoryError::InvalidAddress) => {
        eprintln!("Invalid memory address");
    }
    Err(e) => eprintln!("Other error: {}", e),
}
```

## Debug Mode

Enable debug output to troubleshoot memory operations:

```rust
let mut mem = GameMemUtils::new("my_game", true)?; // Enable debug

// Debug output will show:
// - Memory region scanning details
// - Pattern matching progress
// - Ptrace operation results
// - Module loading information
```

## Requirements

- **Linux**: This library is Linux-specific and uses `/proc/pid/mem` and `ptrace`
- **Permissions**: May require `sudo` or appropriate capabilities to attach to processes
- **Target Process**: The target process should be running and accessible

## Supported Platforms

- Linux (x86_64, ARM64, and other architectures supported by Rust)
- Wine/Proton games

## Safety Notes

- This library directly manipulates process memory, which can cause crashes if used incorrectly
- Always validate addresses and data before writing
- The target process will be temporarily stopped during attachment
- Automatic cleanup ensures processes are properly detached

## License

Licensed under the MIT license. See [LICENSE](LICENSE) for details.

## Changelog

### 0.2.0

- Added comprehensive pattern scanning with wildcard support
- Added debug mode for troubleshooting
- Enhanced error handling and reporting
- Added support for regex-based module filtering
- Process attachment via ptrace

### 0.1.2

- Initial release with basic memory read/write operations
- Module base address detection
