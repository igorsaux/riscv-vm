use std::path::PathBuf;

use clap::Parser;

#[derive(Debug, Parser)]
struct App {
    /// Path to a RISC-V binary file.
    pub bin: PathBuf
}

fn main() {
    let app = App::parse();

    println!("Hello, world!");
}
