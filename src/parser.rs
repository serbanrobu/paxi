use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, char, multispace0, multispace1},
    combinator::{map, recognize},
    multi::{fold_many0, many0, separated_list1},
    sequence::{delimited, pair, preceded},
    IResult,
};

use crate::{Checkable, Identifier, Inferable};

fn parse_identifier(input: &str) -> IResult<&str, Identifier> {
    map(
        recognize(pair(
            alt((alpha1, tag("_"))),
            many0(alt((alphanumeric1, tag("_"), tag("\'")))),
        )),
        |s: &str| s.to_owned(),
    )(input)
}

fn parse_atom(input: &str) -> IResult<&str, Inferable> {
    alt((
        parens(ws(parse_inferable)),
        map(parse_identifier, Inferable::Variable),
    ))(input)
}

fn parse_inferable(input: &str) -> IResult<&str, Inferable> {
    let (input, atom) = parse_atom(input)?;

    fold_many0(
        parens(separated_list1(char(','), ws(parse_checkable))),
        move || atom.clone(),
        |fun, args| {
            args.into_iter()
                .fold(fun, |fun, arg| Inferable::Application {
                    function: fun.into(),
                    argument: arg.into(),
                })
        },
    )(input)
}

pub fn parse_checkable(input: &str) -> IResult<&str, Checkable> {
    alt((
        parens(ws(parse_checkable)),
        map(
            pair(
                preceded(pair(char('λ'), multispace1), parse_identifier),
                preceded(pair(char('.'), multispace0), parse_checkable),
            ),
            |(identifier, body)| Checkable::Lambda {
                identifier,
                body: body.into(),
            },
        ),
        map(parse_inferable, Checkable::Inferable),
    ))(input)
}

pub fn parens<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(char('('), inner, char(')'))
}

pub fn ws<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: Fn(&'a str) -> IResult<&'a str, O>,
{
    delimited(multispace0, inner, multispace0)
}
