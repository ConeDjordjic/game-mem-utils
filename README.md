# GameMemUtils

A Rust library for reading and writing process memory on Linux.

## Usage

Add to your `Cargo.toml` or use `cargo add game_mem_utils`:

```toml
[dependencies]
game_mem_utils = "0.1.0"
```

Example:

```rust
use game_mem_utils::{GameMemUtils, hex};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut mem = GameMemUtils::new("process_name")?;

    // Read a u32 value
    let gold: u32 = mem.read_at(hex!("8320b84"))?;
    println!("Current gold: {gold}");

    // Write a new value
    mem.write_at(hex!("8320b84"), 999999u32)?;

    Ok(())
}
```

## API

### Create instance

```rust
let mut mem = GameMemUtils::new("process_name")?;
let mut mem = GameMemUtils::from_pid(1234)?;
```

### Read memory

```rust
let value: u32 = mem.read_at(0x12345678)?;          // absolute address
let value: u32 = mem.read(0x1000)?;                 // offset from base
let value: u32 = mem.read_hex("1000")?;             // hex string offset
let bytes = mem.read_bytes(0x12345678, 16)?;        // raw bytes
let text = mem.read_string(0x12345678, 64)?;        // null-terminated string
```

### Write memory

```rust
mem.write_at(0x12345678, 42u32)?;                   // absolute address
mem.write(0x1000, 100i32)?;                         // offset from base
mem.write_hex("1000", 200u32)?;                     // hex string offset
mem.write_bytes(0x12345678, &[0x41, 0x42, 0x43])?;  // raw bytes
```

### Utilities

```rust
let pid = mem.pid();
let base_addr = mem.base_address();
let module_base = mem.find_module_base("module.so")?;
```

## Requirements

- Linux
- Appropriate permissions (may need `sudo`)

## License

Licensed under the MIT license.
