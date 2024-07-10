use nom::character::complete::alphanumeric1;
use nom::sequence::{delimited, pair, preceded, terminated};
use nom::{
    branch::alt,
    bytes::complete::{tag, tag_no_case},
    character::complete::{alpha1, alphanumeric0, char, digit1, space0},
    combinator::opt,
    error::{context, VerboseError},
    multi::{many0, many1},
    number,
    sequence::tuple,
    IResult,
};

/// Int[ x_ ^ a_., x_Symbol ] := xxx /; a > 1

type Res<T, U> = IResult<T, U, VerboseError<T>>;
fn int(input: &str) -> Res<&str, &str> {
    context("Int", tag("Int"))(input)
}
fn sym(input: &str) -> Res<&str, String> {
    terminated(
        pair(alpha1, alphanumeric0),
        tuple((many0(char('_')), alphanumeric0)),
    )(input)
    .map(|(x, y)| (x, format!("?{}{}", y.0, y.1))) // ignore x1_XX , just return x1
}
fn number(input: &str) -> Res<&str, String> {
    digit1(input).map(|(x, y)| (x, y.to_owned()))
}
fn parse_plus(input: &str) -> Res<&str, String> {
    tuple((sym, space0, char('+'), space0, sym))(input)
        .map(|(x, y)| (x, format!("(+ {} {})", y.0, y.4)))
}
fn parse_sub(input: &str) -> Res<&str, String> {
    tuple((sym, space0, char('-'), space0, sym))(input)
        .map(|(x, y)| (x, format!("(- {} {})", y.0, y.4)))
}
fn parse_mult(input: &str) -> Res<&str, String> {
    tuple((sym, space0, char('*'), space0, sym))(input)
        .map(|(x, y)| (x, format!("(* {} {})", y.0, y.4)))
}
fn parse_div(input: &str) -> Res<&str, String> {
    tuple((sym, space0, char('/'), space0, sym))(input)
        .map(|(x, y)| (x, format!("(/ {} {})", y.0, y.4)))
}
fn parse_pow(input: &str) -> Res<&str, String> {
    tuple((sym, space0, char('^'), space0, sym))(input)
        .map(|(x, y)| (x, format!("(^ {} {})", y.0, y.4)))
}
fn parse_expr(input: &str) -> Res<&str, String> {
    tuple((
        preceded(space0, int),           // Int 0
        preceded(space0, char('[')),     // [ 1
        preceded(space0, parse_pow),     // left 2
        preceded(space0, char(',')),     //3
        preceded(space0, sym),           // , x 4
        preceded(space0, char(']')),     // ] 5
        preceded(space0, tag(":=")),     // := 6
        preceded(space0, parse_pow),     // right  7
        preceded(space0, tag("/;")),     // /; 8
        preceded(space0, alphanumeric1), // cond 9
    ))(input)
    .map(|(x, y)| {
        (
            x,
            format!(r#"rw!("(i {}, {})" => "{}" if {})"#, y.2, y.4, y.7, y.9),
        )
    })
}
/// from
/// ```mathematica
/// FreeQ[{a,b,c,d,e}, x]
/// ```
/// to
/// ```rs
/// freeq(&["?a", "?b", ...], "?x")
/// ```
fn parse_freeq(input: &str) -> Res<&str, String> {
    tuple((
        tag("FreeQ[{"),
        many1(terminated(sym, opt(char(',')))),
        char('}'),
        delimited(space0, char(','), space0),
        delimited(space0, sym, space0),
        delimited(space0, char(']'), space0),
    ))(input)
    .map(|(x, y)| (x, format!(r#"freeq(&{:?}, "{}" )"#, y.1, y.4)))
}
#[cfg(test)]
mod parse {

    use super::*;
    #[test]
    fn test_frame() {
        dbg!(parse_expr("Int[x_^ m_,x_Symbol] := m^x  /; xxxx "));
    }
    #[test]
    fn parse_sym() {
        dbg!(sym("x_Symbol"));
        dbg!(sym("x1_Symbol"));
        dbg!(sym("xm1_Symbol"));
        dbg!(sym("x1m_Symbol"));
    }
    #[test]
    fn parse_num() {
        dbg!(number("123"));
    }
    #[test]
    fn test_parse_plus() {
        dbg!(parse_plus("a+b"));
        dbg!(parse_sub("a-b"));
        dbg!(parse_mult("a*b"));
        dbg!(parse_div("a/b"));
        dbg!(parse_pow("a^b"));
    }
    #[test]
    fn test_freeq() {
        dbg!(parse_freeq("FreeQ[{a,b,c,d,e}, x]"));
    }
}
