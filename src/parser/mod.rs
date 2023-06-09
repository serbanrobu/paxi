mod string;

use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, char, multispace0, u64, u8},
    combinator::{eof, map, recognize, value},
    error::Error,
    multi::many0,
    sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
    Finish, IResult,
};

use crate::{Checkable, Inferable, Name};

use string::parse_string;

use self::string::parse_char;

fn parse_identifier(input: &str) -> IResult<&str, String> {
    map(
        recognize(pair(
            alt((alpha1, tag("_"))),
            many0(alt((alphanumeric1, tag("_"), tag("\'")))),
        )),
        str::to_owned,
    )(input)
}

pub fn parse_checkable(input: &str) -> IResult<&str, Checkable> {
    alt((
        parens(ws(parse_checkable)),
        alt((
            value(Checkable::Char, tag("Char")),
            value(Checkable::Nil, tag("nil")),
            value(Checkable::Sole, tag("sole")),
            value(Checkable::String, tag("String")),
            value(Checkable::Trivial, tag("Trivial")),
            value(Checkable::Usize, tag("Usize")),
        )),
        map(u64, |u| Checkable::UsizeLit(u as usize)),
        map(parse_char, Checkable::CharLit),
        map(parse_string, Checkable::StringLit),
        map(
            preceded(
                pair(tag("cons"), multispace0),
                parens(separated_pair(
                    ws(parse_checkable),
                    char(','),
                    ws(parse_checkable),
                )),
            ),
            |(e_1, e_2)| Checkable::Cons(Box::new(e_1), Box::new(e_2)),
        ),
        map(
            preceded(pair(tag("Fin"), multispace0), parens(ws(parse_checkable))),
            |e| Checkable::Fin(Box::new(e)),
        ),
        map(
            preceded(
                pair(tag("lam"), multispace0),
                parens(pair(
                    terminated(ws(parse_identifier), char(',')),
                    ws(parse_checkable),
                )),
            ),
            |(x, e)| Checkable::Lam(Box::new(e)),
        ),
        map(
            preceded(
                pair(tag("let"), multispace0),
                parens(tuple((
                    terminated(ws(parse_identifier), char(',')),
                    terminated(ws(parse_checkable), char(',')),
                    ws(parse_checkable),
                ))),
            ),
            |(x, e_1, e_2)| Checkable::Let(x, Box::new(e_1), Box::new(e_2)),
        ),
        map(
            preceded(pair(tag("List"), multispace0), parens(ws(parse_checkable))),
            |e| Checkable::List(Box::new(e)),
        ),
        map(
            preceded(pair(char('U'), multispace0), parens(ws(u8))),
            Checkable::U,
        ),
        map(
            preceded(
                pair(tag("Vec"), multispace0),
                parens(separated_pair(
                    ws(parse_checkable),
                    char(','),
                    ws(parse_checkable),
                )),
            ),
            |(e_1, e_2)| Checkable::Vec(Box::new(e_1), Box::new(e_2)),
        ),
        map(parse_inferable, Checkable::Inferable),
    ))(input)
}

pub fn parse_inferable(input: &str) -> IResult<&str, Inferable> {
    alt((
        map(
            preceded(
                pair(tag("the"), multispace0),
                parens(separated_pair(
                    ws(parse_checkable),
                    char(','),
                    ws(parse_checkable),
                )),
            ),
            |(e_1, e_2)| Inferable::Ann(Box::new(e_1), Box::new(e_2)),
        ),
        map(parse_identifier, |x| Inferable::Free(Name::Global(x))),
    ))(input)
}

fn parens<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(char('('), inner, char(')'))
}

fn _brackets<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(char('['), inner, char(']'))
}

fn ws<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(multispace0, inner, multispace0)
}

impl FromStr for Checkable {
    type Err = Error<String>;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let (_remaining, checkable) = terminated(parse_checkable, eof)(s.trim())
            .finish()
            .map_err(|e| Error::new(e.input.to_owned(), e.code))?;

        Ok(checkable)
    }
}
