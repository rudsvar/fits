use std::fmt::Display;

use chumsky::{
    error::Simple,
    primitive::{choice, end, just},
    recursive::recursive,
    text::{ident, whitespace, TextParser},
    Parser,
};
use tracing::debug;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Unit,
    Int(i32),
    Sum(Vec<Expr>),
    Var(String),
    Abs(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Unit => write!(f, "()"),
            Expr::Int(i) => write!(f, "{}", i),
            Expr::Sum(addends) => {
                write!(
                    f,
                    "+ {}",
                    addends
                        .iter()
                        .map(|a| a.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            Expr::Var(v) => write!(f, "{}", v),
            Expr::Abs(v, e) => write!(f, "(\\{}. {})", v, e),
            Expr::App(abs, e) => write!(f, "({} {})", abs, e),
        }
    }
}

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    recursive(|p| {
        let unit = just("()").to(Expr::Unit);
        let int = just("-").or_not().then_with(|sign| {
            chumsky::text::int(10).map(move |s: String| {
                let n: i32 = s.parse().unwrap();
                match sign {
                    Some("-") => Expr::Int(-n),
                    None => Expr::Int(n),
                    _ => unreachable!(),
                }
            })
        });
        let var = ident().map(Expr::Var);
        let abs = just("\\")
            .padded()
            .ignore_then(ident().padded())
            .then_ignore(just(".").padded())
            .then(p.clone())
            .map(|(v, e)| Expr::Abs(v, Box::new(e)));
        let atom = recursive(|atom| {
            let sum = just("+")
                .padded()
                .ignore_then(atom.clone().padded().repeated())
                .map(Expr::Sum);
            choice((
                unit,
                int,
                sum,
                var,
                abs,
                p.delimited_by(just("("), just(")")),
            ))
            .padded()
        });

        atom.clone()
            .then(whitespace().ignore_then(atom).repeated())
            .foldl(|f, a| Expr::App(Box::new(f), Box::new(a)))
    })
    .then_ignore(end())
}

pub fn parse(s: &str) -> Result<Expr, Vec<Simple<char>>> {
    parser().parse(s)
}

pub fn format(s: &str) -> Result<String, Vec<Simple<char>>> {
    parse(s).map(|e| e.to_string())
}

pub fn substitute(m: Expr, x: &str, n: Expr) -> Expr {
    match m {
        Expr::Var(x2) if x == x2 => n.clone(),
        Expr::Abs(x2, b) if x != x2 => Expr::Abs(x2, Box::new(substitute(*b, x, n))),
        Expr::App(f, body) => Expr::App(
            Box::new(substitute(*f, x, n.clone())),
            Box::new(substitute(*body, x, n)),
        ),
        e => e,
    }
}

pub fn beta_reduce_with(e: Expr, depth: usize) -> Expr {
    let indent = " ".repeat(2 * depth);
    debug!("{indent}reduce_with({e:?}) {{");
    let e = match e {
        Expr::Var(v) => panic!("{indent} Unbound variable {v:?}"),
        abs @ Expr::Abs(_, _) => abs,
        Expr::App(f, x) => {
            if let Expr::Abs(v, b) = beta_reduce_with(*f.clone(), depth + 1) {
                beta_reduce_with(substitute(*b, &v, *x), depth + 1)
            } else {
                panic!("{indent}{f} must be an abstraction");
            }
        }
        Expr::Unit => Expr::Unit,
        Expr::Int(i) => Expr::Int(i),
        Expr::Sum(addends) => {
            let mut sum = 0;
            for addend in addends {
                if let Expr::Int(i) = addend {
                    sum += i;
                } else {
                    panic!("{indent}{addend} must be an integer");
                }
            }
            Expr::Int(sum)
        }
    };
    debug!("{indent}}} => {e:?}");
    e
}

pub fn beta_reduce(e: Expr) -> Expr {
    beta_reduce_with(e, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_value() {
        assert_eq!(Expr::Unit, parse("()").unwrap());
        assert_eq!(Expr::Int(123), parse("123").unwrap());
        assert_eq!(Expr::Int(-123), parse("-123").unwrap());
    }

    #[test]
    fn parse_var() {
        assert_eq!(Expr::Var("x".to_string()), parse(" x ").unwrap());
    }

    #[test]
    fn parse_abs() {
        assert_eq!(
            Expr::Abs("x".to_string(), Box::new(Expr::Var("x".to_string()))),
            parse(" \\ x . x ").unwrap()
        );
    }

    #[test]
    fn parse_app() {
        assert_eq!(
            Expr::App(
                Box::new(Expr::Var("f".to_string())),
                Box::new(Expr::Var("x".to_string()))
            ),
            parse("f x").unwrap()
        );
    }

    #[test]
    fn parse_app_abs_var() {
        assert_eq!(
            Expr::App(
                Box::new(Expr::Abs(
                    "x".to_string(),
                    Box::new(Expr::Var("x".to_string()))
                )),
                Box::new(Expr::Var("x".to_string()))
            ),
            parse("(\\x. x) x").unwrap()
        );
    }

    #[test]
    fn reduce1() {
        assert_eq!(
            Expr::Unit,
            beta_reduce(Expr::App(
                Box::new(Expr::Abs(
                    "x".to_string(),
                    Box::new(Expr::Var("x".to_string()))
                )),
                Box::new(Expr::Unit)
            ))
        );
    }

    #[test]
    fn parse_reduce_1() {
        assert_eq!("()", beta_reduce(parse("()").unwrap()).to_string());
    }

    #[test]
    fn parse_reduce_2() {
        assert_eq!("()", beta_reduce(parse("(\\x. x) ()").unwrap()).to_string());
    }

    #[test]
    fn parse_reduce_3() {
        assert_eq!(
            "(\\x. (\\y. x))",
            beta_reduce(parse("(\\x. \\y . x)").unwrap()).to_string()
        );
    }

    #[test]
    fn parse_reduce_4() {
        assert_eq!(
            "(\\y. ())",
            beta_reduce(parse("(\\x. \\y . x) ()").unwrap()).to_string()
        );
    }

    #[test]
    fn parse_reduce_nested() {
        assert_eq!(
            "()",
            beta_reduce(parse("(\\y . y) ()").unwrap()).to_string()
        );
    }

    #[test]
    fn parse_reduce_nested_2() {
        assert_eq!(
            "()",
            beta_reduce(parse("(\\x . \\y . x) () ()").unwrap()).to_string()
        );
    }

    #[test]
    fn parse_if_true_false() {
        parse("(\\if. \\true. \\false. if true false true) (\\b. b) (\\x. \\y. x) (\\x. \\y. y)")
            .unwrap();
    }

    #[test]
    fn parse_reduce_if_true_false() {
        beta_reduce(
            parse(
                "(\\if. \\true. \\false. if true false true) (\\b. b) (\\x. \\y. x) (\\x. \\y. y)",
            )
            .unwrap(),
        );
    }

    #[test]
    fn parse_reduce_5() {
        assert_eq!(
            "(\\x. (\\y. y))",
            beta_reduce(parse(
                "(\\if. \\true. \\false. if true false true) (\\b. b) (\\x. \\y. x) (\\x. \\y. y)"
            ).unwrap())
            .to_string()
        );
    }

    #[test]
    fn sum() {
        assert_eq!(Expr::Int(6), beta_reduce(parse("+ 1 2 3").unwrap()));
        assert_eq!(Expr::Int(0), beta_reduce(parse("+ 1 2 (-3)").unwrap()));
    }
}
