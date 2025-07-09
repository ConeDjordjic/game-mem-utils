use game_mem_utils::{GameMemUtils, hex};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create a new GameMemUtils instance by process name and no debug
    let mem = GameMemUtils::new("h3hota HD.exe", false)?;

    // Read current gold value at an absolute address
    let gold: u32 = mem.read_at(hex!("8320b84"))?;
    println!("Current gold: {gold}");

    // Write new gold value
    mem.write_at(hex!("8320b84"), 400000u32)?;

    // Verify the change
    let new_gold: u32 = mem.read_at(hex!("8320b84"))?;
    println!("New gold: {new_gold}");

    // Example of reading with offset from base address
    let health: u32 = mem.read(0x1000)?;
    println!("Health: {health}");

    // Example of reading with hex offset
    let mana: u32 = mem.read_hex("2000")?;
    println!("Mana: {mana}");

    // Example of reading raw bytes
    let bytes = mem.read_bytes(hex!("8320b84"), 4)?;
    println!("Raw bytes: {bytes:?}");

    // Example of reading a string
    let player_name = mem.read_string(hex!("8320c00"), 32)?;
    println!("Player name: {player_name}");

    Ok(())
}
