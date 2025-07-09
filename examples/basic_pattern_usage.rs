use game_mem_utils::GameMemUtils;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize GameMemUtils by process name.
    let mut mem_utils = GameMemUtils::new("game.exe", true)?; // `true` enables debug output
    println!("Successfully attached to PID: {}", mem_utils.pid());

    // Define the byte pattern to search for.
    // This pattern represents: MOV [ECX], EAX; MOV EAX, [address]; MOV [ESI+8], EAX
    // The "A1 ?? ?? ?? ??" part is a MOV EAX, [imm32] instruction where
    // A1 is the opcode and the following 4 bytes are a 32-bit memory address.
    let gold_access_pattern = "89 01 A1 ?? ?? ?? ?? 89 46 08";
    println!("\nSearching for pattern: \"{gold_access_pattern}\"...");

    // Perform the pattern scan across all accessible memory.
    let pattern_found_address = mem_utils.pattern_scan_all_process_memory(gold_access_pattern)?;

    if let Some(pattern_addr) = pattern_found_address {
        println!("Pattern found at instruction: {pattern_addr:#x}");

        // Extract the address from the MOV EAX, [imm32] instruction.
        // In the pattern "89 01 A1 ?? ?? ?? ?? 89 46 08":
        // - Bytes 0-1: "89 01" (MOV [ECX], EAX)
        // - Byte 2: "A1" (MOV EAX, [imm32] opcode)
        // - Bytes 3-6: The 32-bit immediate address (what we want)
        // - Bytes 7-9: "89 46 08" (MOV [ESI+8], EAX)
        let address_offset_in_pattern = 3; // Offset to the 32-bit address within the pattern
        let pointer_location_in_memory = pattern_addr + address_offset_in_pattern;

        // Read the 32-bit address from the instruction
        let target_address_u32: u32 = mem_utils.read_u32_le(pointer_location_in_memory)?;
        println!(
            "Address embedded in instruction at {pointer_location_in_memory:#x}: {target_address_u32:#x}"
        );

        // Cast to u64 for consistency with library functions
        let target_address: u64 = u64::from(target_address_u32);
        println!("Target address: {target_address:#x}");

        // The target address might point to:
        // 1. The actual variable (if gold_offset = 0)
        // 2. A structure containing the variable at some offset
        // 3. A pointer to another structure (requires additional dereferencing)

        // This offset should be determined through reverse engineering tools
        // like Cheat Engine, x64dbg, or similar memory analysis tools.
        let gold_offset: u64 = 0x0; // Replace with actual offset (e.g., 0x12C)
        let actual_gold_address: u64 = target_address + gold_offset;
        println!("Calculated gold variable address: {actual_gold_address:#x}");

        // Attempt to read the gold value
        match mem_utils.read_u32_le(actual_gold_address) {
            Ok(current_gold) => {
                println!("Current gold value: {current_gold}");

                // Example: Modify the gold value
                mem_utils.write_u32_le(actual_gold_address, 9999)?;
                println!("Gold value updated to: 9999");
            }
            Err(e) => {
                eprintln!("Error reading gold value at {actual_gold_address:#x}: {e}");
                eprintln!("This may indicate:");
                eprintln!("  - Incorrect offset calculation");
                eprintln!("  - Memory protection preventing access");
                eprintln!("  - The address points to a pointer requiring dereferencing");
            }
        }
    } else {
        println!("Pattern not found in process memory.");
        println!("Consider:");
        println!("  - Verifying the pattern is correct");
        println!("  - Checking if the game version matches the pattern");
        println!("  - Ensuring the game is in the expected state");
    }

    Ok(())
}
