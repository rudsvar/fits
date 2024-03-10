use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    fits::init_logging();

    let usage = format!(
        "usage: {} <command> <path>",
        std::env::args().next().unwrap()
    );
    let command = std::env::args().nth(1).ok_or(usage.clone())?;
    let path = std::env::args().nth(2).ok_or(usage)?;
    let input = std::fs::read_to_string(path)?;
    match command.as_str() {
        "parse" => {
            let program = fits::parse(&input)?;
            println!("{:#?}", program);
        }
        "tc" => {
            let program = fits::parse(&input)?;
            fits::typecheck(&program)?;
            println!("Ok");
        }
        "run" => {
            fits::run(&input)?;
        }
        "fmt" => {
            let program = fits::parse(&input)?;
            print!("{}", program);
        }
        _ => eprintln!("No such command"),
    }

    Ok(())
}
