use nom::{
    branch::alt,
    bytes::complete::{is_not, tag},
    character::complete::{alpha1, alphanumeric0, char, digit1, satisfy},
    combinator::{eof, map, map_res, opt, recognize},
    error::context,
    multi::{many0, separated_list0},
    sequence::{delimited, pair, preceded, separated_pair},
    IResult,
};

use crate::{
    expr::{Expr, Function},
    record::Record,
    statement::Stmt,
    Program,
};

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub struct ParseError(String);

impl<'a> From<nom::Err<nom::error::Error<&'a str>>> for ParseError {
    fn from(value: nom::Err<nom::error::Error<&'a str>>) -> Self {
        ParseError(value.to_string())
    }
}

pub type ParseResult<'a, T> = IResult<&'a str, T>;

pub fn unit(input: &str) -> ParseResult<()> {
    map(pair(symbol("("), symbol(")")), |_| ())(input)
}

pub fn bool(input: &str) -> ParseResult<bool> {
    let t = map(symbol("true"), |_| true);
    let f = map(symbol("false"), |_| false);
    alt((t, f))(input)
}

pub fn int(input: &str) -> ParseResult<i128> {
    let (input, sign) = opt(alt((symbol("+"), symbol("-"))))(input)?;
    let (input, i) = lexeme(map_res(recognize(digit1), str::parse::<i128>))(input)?;
    let i: i128 = if let Some("-") = sign.as_deref() {
        -i
    } else {
        i
    };
    Ok((input, i))
}

pub fn keyword<'a>(keyword: &str) -> impl Fn(&'a str) -> IResult<&'a str, String> + '_ {
    move |input| {
        let (input, s) = tag(keyword)(input)?;
        Ok((input, s.to_string()))
    }
}

pub fn string(input: &str) -> IResult<&str, String> {
    let (input, s) = delimited(char('"'), recognize(many0(is_not("\""))), char('"'))(input)?;
    Ok((input, s.to_string()))
}

pub fn lexeme<'a, T>(
    mut p: impl FnMut(&'a str) -> IResult<&'a str, T>,
) -> impl FnMut(&'a str) -> IResult<&'a str, T> {
    move |input| {
        let (input, _) = many0(satisfy(|c| c.is_whitespace()))(input)?;
        p(input)
    }
}

pub fn identifier(input: &str) -> IResult<&str, String> {
    let (input, identifier) = lexeme(recognize(pair(alpha1, alphanumeric0)))(input)?;
    Ok((input, identifier.to_string()))
}

pub fn key_value<'a, T>(
    value_parser: impl FnMut(&'a str) -> ParseResult<'a, T>,
) -> impl FnMut(&'a str) -> IResult<&'a str, (String, T)> {
    let mut key_value = separated_pair(identifier, symbol(":"), lexeme(value_parser));
    move |input| {
        let (input, (key, value)) = key_value(input)?;
        Ok((input, (key.to_string(), value)))
    }
}

pub fn symbol<'a>(symbol: &'a str) -> impl FnMut(&'a str) -> ParseResult<'a, String> {
    move |input| {
        let (input, s) = lexeme(tag(symbol))(input)?;
        Ok((input, s.to_string()))
    }
}

pub fn record<'a, T>(
    value_parser: impl FnMut(&'a str) -> ParseResult<'a, T>,
) -> impl FnMut(&'a str) -> IResult<&'a str, Record<T>> {
    let mut parse_record = delimited(
        symbol("{"),
        separated_list0(symbol(","), key_value(value_parser)),
        symbol("}"),
    );
    move |input| {
        let (input, kvs) = parse_record(input)?;
        let record = Record {
            fields: kvs.into_iter().collect(),
        };
        Ok((input, record))
    }
}

pub fn r#if(input: &str) -> ParseResult<(Expr, Expr, Expr)> {
    let (input, _) = symbol("if")(input)?;
    let (input, b) = expr(input)?;
    let (input, _) = symbol("then")(input)?;
    let (input, e1) = expr(input)?;
    let (input, _) = symbol("else")(input)?;
    let (input, e2) = expr(input)?;
    Ok((input, (b, e1, e2)))
}

/// Parses a factor, a unit of expression.
pub fn factor(input: &str) -> ParseResult<Expr> {
    let (input, e) = alt((
        map(unit, |_| Expr::Unit),
        map(bool, Expr::Bool),
        map(int, Expr::Int),
        map(string, Expr::String),
        map(r#if, |(b, e1, e2)| {
            Expr::If(Box::new(b), Box::new(e1), Box::new(e2))
        }),
        map(identifier, Expr::Var),
        map(record(expr), Expr::Record),
        delimited(symbol("("), context("(expr)", expr), symbol(")")),
    ))(input)?;

    // Parse function call
    let (input, lparen) = opt(symbol("("))(input)?;
    match (e, lparen) {
        (Expr::Var(f), Some(_)) => {
            let (input, args) = separated_list0(symbol(","), expr)(input)?;
            let (input, _) = symbol(")")(input)?;
            Ok((input, Expr::Call(f, args)))
        }
        (e, _) => Ok((input, e)),
    }
}

/// Parses a term, composed of factors.
pub fn term2(input: &str) -> ParseResult<Expr> {
    let (mut big_input, mut e1) = lexeme(factor)(input)?;
    loop {
        let (input, op) = opt(lexeme(alt((
            symbol("."),
            symbol("*"),
            symbol("<"),
            symbol("%"),
        ))))(big_input)?;
        if let Some(op) = op {
            match op.as_str() {
                "." => {
                    let (input, field_name) = identifier(input)?;
                    big_input = input;
                    e1 = Expr::FieldAccess(Box::new(e1), field_name);
                }
                "*" => {
                    let (input, e2) = factor(input)?;
                    big_input = input;
                    e1 = Expr::Mul(Box::new(e1), Box::new(e2));
                }
                "<" => {
                    let (input, e2) = factor(input)?;
                    big_input = input;
                    e1 = Expr::Lt(Box::new(e1), Box::new(e2));
                }
                "%" => {
                    let (input, e2) = factor(input)?;
                    big_input = input;
                    e1 = Expr::Mod(Box::new(e1), Box::new(e2));
                }
                _ => unimplemented!(),
            }
        } else {
            break;
        }
    }
    Ok((big_input, e1))
}

/// Parses a term, composed of factors.
pub fn term(input: &str) -> ParseResult<Expr> {
    let (mut big_input, mut e1) = lexeme(term2)(input)?;
    loop {
        let (input, op) = opt(lexeme(alt((symbol("+"), symbol("-"), symbol("==")))))(big_input)?;
        if let Some(op) = op {
            match op.as_str() {
                "+" => {
                    let (input, e2) = term2(input)?;
                    big_input = input;
                    e1 = Expr::Add(Box::new(e1), Box::new(e2));
                }
                "-" => {
                    let (input, e2) = term2(input)?;
                    big_input = input;
                    e1 = Expr::Sub(Box::new(e1), Box::new(e2));
                }
                "==" => {
                    let (input, e2) = term2(input)?;
                    big_input = input;
                    e1 = Expr::Eq(Box::new(e1), Box::new(e2));
                }
                _ => unimplemented!(),
            }
        } else {
            break;
        }
    }
    Ok((big_input, e1))
}

/// Parses an expression, composed of terms.
pub fn expr(input: &str) -> ParseResult<Expr> {
    let (mut big_input, mut e1) = lexeme(term)(input)?;
    loop {
        let (input, op) = opt(lexeme(alt((symbol("&&"),))))(big_input)?;
        if let Some(op) = op {
            match op.as_str() {
                "&&" => {
                    let (input, e2) = expr(input)?;
                    big_input = input;
                    e1 = Expr::And(Box::new(e1), Box::new(e2));
                }
                _ => unimplemented!(),
            }
        } else {
            break;
        }
    }
    Ok((big_input, e1))
}

pub fn variable_definition(input: &str) -> ParseResult<Stmt> {
    let (input, _) = symbol("let")(input)?;
    let (input, name) = identifier(input)?;
    let (input, ty) = opt(preceded(symbol(":"), identifier))(input)?;
    let (input, _) = symbol("=")(input)?;
    let (input, e) = expr(input)?;
    Ok((input, Stmt::VarDef(name, ty, e)))
}

pub fn type_definition(input: &str) -> ParseResult<Stmt> {
    let (input, _) = symbol("type")(input)?;
    let (input, name) = identifier(input)?;
    let (input, _) = symbol("=")(input)?;
    let (input, r) = record(identifier)(input)?;
    Ok((input, Stmt::TypeDef(name, r)))
}

pub fn function_definition(input: &str) -> ParseResult<Stmt> {
    let (input, _) = symbol("fn")(input)?;
    let (input, name) = identifier(input)?;
    let (input, params) = delimited(
        symbol("("),
        separated_list0(
            symbol(","),
            separated_pair(identifier, symbol(":"), identifier),
        ),
        symbol(")"),
    )(input)?;
    let (input, _) = symbol(":")(input)?;
    let (input, return_ty) = identifier(input)?;
    let (input, _) = symbol("=")(input)?;
    let (input, body) = expr(input)?;
    Ok((
        input,
        Stmt::FunDef(Function {
            name,
            params,
            body: Box::new(body),
            return_ty,
        }),
    ))
}

pub fn println(input: &str) -> ParseResult<Stmt> {
    let (input, _) = symbol("println")(input)?;
    let (input, e) = expr(input)?;
    Ok((input, Stmt::PrintLn(e)))
}

pub fn block(input: &str) -> ParseResult<Stmt> {
    let (input, stmts) = delimited(symbol("{"), many0(stmt), symbol("}"))(input)?;
    Ok((input, Stmt::Block(stmts)))
}

pub fn stmt(input: &str) -> ParseResult<Stmt> {
    let (input, stmt) = alt((
        variable_definition,
        type_definition,
        function_definition,
        println,
    ))(input)?;
    let (input, _) = symbol(";")(input)?;
    Ok((input, stmt))
}

pub fn stmts(input: &str) -> ParseResult<Vec<Stmt>> {
    many0(alt((stmt, block)))(input)
}

pub fn program(input: &str) -> ParseResult<'_, Program> {
    let (input, program) = map(stmts, |stmts| Program { stmts })(input)?;
    let (input, _) = lexeme(eof)(input)?;
    Ok((input, program))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Expr;

    #[test]
    fn parse_unit() {
        assert_eq!(Ok(("", ())), unit("()"));
        assert_eq!(Ok(("", ())), unit(" ()"));
        assert_eq!(Ok(("", ())), unit("( )"));
    }

    #[test]
    fn parse_bool() {
        assert_eq!(Ok(("", true)), bool("true"));
        assert_eq!(Ok(("", false)), bool("false"));
    }

    #[test]
    fn parse_int() {
        assert_eq!(Ok(("", 123)), int("123"));
        assert_eq!(Ok(("", -123)), int("-123"));
    }

    #[test]
    fn parse_string() {
        assert_eq!(Ok(("", "".to_string())), string("\"\""));
        assert_eq!(Ok(("", "abc".to_string())), string("\"abc\""));
    }

    #[test]
    fn parse_key_value() {
        let input = r#"  abc: "def""#;
        let expected = ("abc".to_string(), "def".to_string());
        assert_eq!(Ok(("", expected)), key_value(string)(input));
    }

    #[test]
    fn parse_record() {
        let input = r#"
            {
                abc: "def" ,
                e123 : "456" }"#;
        let expected = Record {
            fields: vec![
                ("abc".to_string(), "def".to_string()),
                ("e123".to_string(), "456".to_string()),
            ]
            .into_iter()
            .collect(),
        };
        assert_eq!(Ok(("", expected)), record(string)(input));
    }

    #[test]
    fn parse_lexeme() {
        assert_eq!(Ok(("   ", 'x')), lexeme(char('x'))("  \n x   "))
    }

    #[test]
    fn parse_expr_unit() {
        assert_eq!(Ok(("", Expr::Unit)), expr("()"));
        assert_eq!(Ok(("", Expr::Unit)), expr(" ()"));
        assert_eq!(Ok(("", Expr::Unit)), expr("( )"));
        assert_eq!(Ok((" ", Expr::Unit)), expr("() "));
    }

    #[test]
    fn parse_expr_bool() {
        assert_eq!(Ok(("", Expr::Bool(true))), expr("true"));
        assert_eq!(Ok(("", Expr::Bool(false))), expr("false"));
    }

    #[test]
    fn parse_expr_int() {
        assert_eq!(Ok(("", Expr::Int(812))), expr("812"));
    }

    #[test]
    fn parse_expr_string() {
        assert_eq!(
            Ok(("", Expr::String("Hello!\nThere".to_string()))),
            expr("\"Hello!\nThere\"")
        );
    }

    #[test]
    fn parse_expr_var() {
        assert_eq!(Ok(("", Expr::Var("foo".to_string()))), expr("foo"));
    }

    #[test]
    fn parse_expr_record() {
        assert_eq!(
            Ok((
                "",
                Expr::Record(Record {
                    fields: vec![("key".to_string(), Expr::Int(38))]
                        .into_iter()
                        .collect()
                })
            )),
            expr(
                r#"
                {
                    key: 38
                }"#
            )
        );
    }

    #[test]
    fn parse_expr_parens() {
        assert_eq!(Ok(("", Expr::Bool(true))), expr("(true)"));
        assert_eq!(Ok(("", Expr::Bool(false))), expr("(false)"));
        assert_eq!(Ok(("", Expr::Int(28))), expr("(28)"));
        assert_eq!(Ok(("", Expr::String("s".to_string()))), expr("(\"s\")"));
        assert_eq!(Ok(("", Expr::Var("s".to_string()))), expr("((((s))))"));
    }

    #[test]
    fn parse_expr_function_call() {
        assert_eq!(
            Ok(("", Expr::Call("f".to_string(), vec![Expr::Int(3)]))),
            expr("f ( 3 )")
        );
        assert_eq!(
            Ok(("", Expr::Call("f".to_string(), vec![Expr::Int(3)]))),
            expr("f(3)")
        );
    }

    #[test]
    fn parse_expr_field_access() {
        assert_eq!(
            Ok((
                "",
                Expr::FieldAccess(Box::new(Expr::Var("foo".to_string())), "bar".to_string())
            )),
            expr("foo.bar")
        );
        assert_eq!(
            Ok((
                "",
                Expr::FieldAccess(
                    Box::new(Expr::FieldAccess(
                        Box::new(Expr::Var("foo".to_string())),
                        "bar".to_string()
                    )),
                    "baz".to_string()
                )
            )),
            expr("foo.bar.baz")
        );
        assert_eq!(
            Ok((
                "",
                Expr::FieldAccess(
                    Box::new(Expr::Call(
                        "foo".to_string(),
                        vec![Expr::String("arg".to_string())]
                    )),
                    "bar".to_string()
                ),
            )),
            expr("foo(\"arg\").bar")
        );
    }

    #[test]
    fn parse_if() {
        assert_eq!(
            Ok(("", (Expr::Int(0), Expr::Int(0), Expr::Int(0)))),
            r#if("if 0 then 0 else 0")
        );
    }

    #[test]
    fn parse_expr_mul() {
        assert_eq!(
            Ok((
                "",
                Expr::Mul(Box::new(Expr::Int(3)), Box::new(Expr::Int(5)))
            )),
            expr("3 * 5")
        )
    }

    #[test]
    fn parse_expr_add() {
        assert_eq!(
            Ok((
                "",
                Expr::Add(Box::new(Expr::Int(3)), Box::new(Expr::Int(5)))
            )),
            expr("3 + 5")
        )
    }

    #[test]
    fn parse_expr_add_mul() {
        assert_eq!(
            Ok((
                "",
                Expr::Add(
                    Box::new(Expr::Int(3)),
                    Box::new(Expr::Mul(Box::new(Expr::Int(5)), Box::new(Expr::Int(7))))
                )
            )),
            expr("3 + 5 * 7")
        )
    }

    #[test]
    fn parse_expr_mul_add() {
        assert_eq!(
            Ok((
                "",
                Expr::Add(
                    Box::new(Expr::Mul(Box::new(Expr::Int(3)), Box::new(Expr::Int(5)))),
                    Box::new(Expr::Int(7))
                )
            )),
            expr("3 * 5 + 7")
        );
    }

    #[test]
    fn parse_variable_definition() {
        assert_eq!(
            Ok((
                "",
                Stmt::VarDef("a".to_string(), Some("b".to_string()), Expr::Unit)
            )),
            variable_definition("let a: b = ()")
        );
    }

    #[test]
    fn parse_type_definition() {
        assert_eq!(
            Ok((
                "",
                Stmt::TypeDef(
                    "A".to_string(),
                    Record {
                        fields: vec![
                            ("a".to_string(), "b".to_string()),
                            ("c".to_string(), "d".to_string())
                        ]
                        .into_iter()
                        .collect()
                    }
                )
            )),
            type_definition("type A = { a : b , c : d }")
        );
    }

    #[test]
    fn parse_function_definition() {
        assert_eq!(
            Ok((
                "",
                Stmt::FunDef(Function {
                    name: "f".to_string(),
                    params: vec![
                        ("a".to_string(), "A".to_string()),
                        ("b".to_string(), "B".to_string())
                    ],
                    return_ty: "C".to_string(),
                    body: Box::new(Expr::Add(
                        Box::new(Expr::Var("a".to_string())),
                        Box::new(Expr::Var("b".to_string()))
                    ))
                })
            )),
            function_definition(" fn f ( a : A , b : B ) : C = a + b")
        );
    }

    #[test]
    fn parse_stmt() {
        assert_eq!(
            Ok((
                "",
                Stmt::FunDef(Function {
                    name: "f".to_string(),
                    params: vec![
                        ("a".to_string(), "A".to_string()),
                        ("b".to_string(), "B".to_string()),
                        ("c".to_string(), "C".to_string())
                    ],
                    return_ty: "D".to_string(),
                    body: Box::new(Expr::If(
                        Box::new(Expr::Var("a".to_string())),
                        Box::new(Expr::Var("b".to_string())),
                        Box::new(Expr::Var("c".to_string()))
                    ))
                })
            )),
            stmt(" fn f ( a : A , b : B, c: C) : D = if a then b else c;")
        );
    }

    #[test]
    fn parse_mod_eq() {
        assert_eq!(
            Ok((
                "",
                Expr::Eq(
                    Box::new(Expr::Mod(
                        Box::new(Expr::Var("n".to_string())),
                        Box::new(Expr::Int(2))
                    )),
                    Box::new(Expr::Int(0))
                )
            )),
            expr("n % 2 == 0")
        );
    }

    #[test]
    fn parse_mod_eq_and() {
        assert_eq!(
            Ok((
                "",
                Expr::And(
                    Box::new(Expr::Eq(
                        Box::new(Expr::Mod(
                            Box::new(Expr::Var("n".to_string())),
                            Box::new(Expr::Int(3))
                        )),
                        Box::new(Expr::Int(0))
                    )),
                    Box::new(Expr::Eq(
                        Box::new(Expr::Mod(
                            Box::new(Expr::Var("n".to_string())),
                            Box::new(Expr::Int(5))
                        )),
                        Box::new(Expr::Int(0))
                    ))
                )
            )),
            expr("n % 3 == 0 && n % 5 == 0")
        );
    }

    #[test]
    fn parse_empty_block() {
        assert_eq!(
            Ok((
                "",
                Program {
                    stmts: vec![Stmt::Block(vec![])]
                }
            )),
            program("{}")
        );
    }

    #[test]
    fn parse_block_with_definitions() {
        assert_eq!(
            Ok((
                "",
                Program {
                    stmts: vec![
                        Stmt::VarDef("a".to_string(), None, Expr::Int(0)),
                        Stmt::Block(vec![Stmt::VarDef(
                            "b".to_string(),
                            None,
                            Expr::Var("a".to_string())
                        )])
                    ]
                }
            )),
            program(
                r#"
                let a = 0;
                {
                    let b = a;
                }
            "#
            )
        );
    }
}
