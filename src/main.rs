use baseconverter::Config;
use colored::Colorize;
use std::env;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    let config = Config::new(&args).unwrap_or_else(|err| {
        eprintln!("{}", format!("\nError parsing arguments: {}\n", err).red());
        process::exit(1);
    });

    if let Err(e) = baseconverter::run(config) {
        eprintln!("{}", format!("\nError: {}\n", e).red());
        process::exit(1);
    };
}
