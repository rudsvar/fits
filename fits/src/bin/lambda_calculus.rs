use ariadne::{Color, Config, Label, Report, ReportKind, Source};
use tracing::debug;
use tracing_subscriber::EnvFilter;

fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();
    let filename = std::env::args().nth(1).expect("missing filename");
    let content = std::fs::read_to_string(filename).expect("failed to read file");
    let ast = fits::lambda_calculus::parse(&content);
    match ast {
        Err(errs) => {
            errs.into_iter().for_each(|e| {
                Report::build(ReportKind::Error, (), e.span().start)
                    .with_config(Config::default().with_compact(true))
                    .with_message(e.to_string())
                    .with_label(
                        Label::new(e.span())
                            .with_message(e.to_string())
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(Source::from(&content))
                    .unwrap()
            });
        }
        Ok(ast) => {
            debug!("AST: {:?}", ast);
            println!("{}", fits::lambda_calculus::beta_reduce(ast));
        }
    }
}
