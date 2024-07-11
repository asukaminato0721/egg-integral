use nom::character::complete::{alphanumeric1, one_of, space1};
use nom::combinator::map;
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
fn Int(input: &str) -> Res<&str, String> {
    context("Int", tag("Int"))(input).map(|(x, y)| (x, y.into()))
}
fn sym(input: &str) -> Res<&str, String> {
    terminated(
        pair(alpha1, alphanumeric0),
        // here allow x_.Symbol, but since this won't happen, so nvm.
        pair(many0(pair(char('_'), opt(char('.')))), alphanumeric0),
    )(input)
    .map(|(x, y)| (x, format!("?{}{}", y.0, y.1))) // ignore x1_XX , just return x1
}
fn sym_or_int(input: &str) -> Res<&str, String> {
    alt((number, sym))(input).map(|(x, y)| (x, format!("{y}")))
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
    tuple((sym_or_int, space0, char('^'), space0, sym_or_int))(input)
        .map(|(x, y)| (x, format!("(^ {} {})", y.0, y.4)))
}
fn parse_full(input: &str) -> Res<&str, String> {
    tuple((
        preceded(space0, Int),           // Int 0
        preceded(space0, char('[')),     // [ 1
        preceded(space0, parse_pow),     // left 2
        preceded(space0, char(',')),     // 3
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
/// NeQ[x*2]
/// pred1("?x", |x| x * 2 < 0)
fn parse_neq(input: &str) -> Res<&str, String> {
    let expr = delimited(tag("NeQ["), parse_mult, tuple((space0, char(']'), space0)))(input);
    expr
}

#[cfg(test)]
mod parse {

    use super::*;
    #[test]
    fn test_frame() {
        dbg!(parse_full("Int[x_. ^ 5  ,x_Symbol] := m^x  /; xxxx "));
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
    #[test]
    fn test_item() {
        dbg!(sym_or_int("a1"));
    }
}
