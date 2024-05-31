use chumsky::{
    error::Simple,
    primitive::just,
    text::{ident, TextParser},
    Parser,
};

pub fn list_of_strings() -> impl Parser<char, Vec<String>, Error = Simple<char>> {
    chumsky::text::ident()
        .padded()
        .separated_by(just(','))
        .delimited_by(just('('), just(')'))
        .padded()
}

pub fn record() -> impl Parser<char, Vec<(String, String)>, Error = Simple<char>> {
    ident()
        .padded()
        .then_ignore(just(":"))
        .then(ident().padded())
        .separated_by(just(','))
        .delimited_by(just('{'), just('}'))
        .padded()
}

pub fn let_expr(
) -> impl Parser<char, ((String, Option<String>), Vec<(String, String)>), Error = Simple<char>> {
    just("let")
        .ignore_then(ident().padded())
        .then(just(":").ignore_then(ident().padded()).or_not())
        .then_ignore(just("="))
        .then(record())
        .padded()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_list_of_strings() {
        let i = " ( a, b ,d)";
        assert_eq!(
            Ok(vec!["a".to_string(), "b".to_string(), "d".to_string()]),
            list_of_strings().parse(i)
        );
    }

    #[test]
    fn parse_record() {
        let i = "{ a : b , c : d }";
        assert_eq!(
            Ok(vec![
                ("a".to_string(), "b".to_string()),
                ("c".to_string(), "d".to_string())
            ]),
            record().parse(i)
        );
    }

    #[test]
    fn parse_let_expr() {
        let i = " let x: A = { a: b }";
        assert_eq!(
            Ok((
                ("x".to_string(), Some("A".to_string())),
                vec![("a".to_string(), "b".to_string())]
            )),
            let_expr().parse(i)
        );
        let i = " let x = { a: b }";
        assert_eq!(
            Ok((
                ("x".to_string(), None),
                vec![("a".to_string(), "b".to_string())]
            )),
            let_expr().parse(i)
        );
        let i = " let x: = { a: b }";
        assert!(let_expr().parse(i).is_err());
    }
}
