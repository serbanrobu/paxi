use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, char, multispace0, multispace1, u8},
    combinator::{map, recognize},
    multi::{fold_many0, many0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair},
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

fn parse_inferable_atom(input: &str) -> IResult<&str, Inferable> {
    alt((
        map(parse_identifier, Inferable::Variable),
        parens(ws(parse_inferable)),
    ))(input)
}

fn parse_application(input: &str) -> IResult<&str, Inferable> {
    let (input, atom) = parse_inferable_atom(input)?;

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

fn parse_inferable_lifting(input: &str) -> IResult<&str, Inferable> {
    alt((
        map(preceded(char('↑'), parse_inferable_lifting), |a| {
            Inferable::Lift(a.into())
        }),
        parse_application,
    ))(input)
}

fn parse_inferable(input: &str) -> IResult<&str, Inferable> {
    parse_inferable_lifting(input)
}

fn parse_checkable_atom(input: &str) -> IResult<&str, Checkable> {
    alt((
        map(preceded(char('U'), parens(ws(u8))), |i| {
            Checkable::Universe(i)
        }),
        map(parse_inferable, Checkable::Inferable),
        parens(ws(parse_checkable)),
    ))(input)
}

fn parse_checkable_lifting(input: &str) -> IResult<&str, Checkable> {
    alt((
        map(preceded(char('↑'), parse_checkable_lifting), |a| {
            Checkable::Lift(a.into())
        }),
        parse_checkable_atom,
    ))(input)
}

fn parse_function(input: &str) -> IResult<&str, Checkable> {
    map(
        separated_list1(ws(tag("→ ")), parse_checkable_lifting),
        |list: Vec<_>| {
            list.into_iter()
                .rev()
                .reduce(|b, a| Checkable::Function(a.into(), b.into()))
                .unwrap()
        },
    )(input)
}

fn parse_abstraction(input: &str) -> IResult<&str, Checkable> {
    alt((
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
        map(
            pair(
                preceded(
                    pair(char('Π'), multispace1),
                    parens(separated_pair(
                        ws(parse_identifier),
                        char(':'),
                        ws(parse_checkable),
                    )),
                ),
                preceded(pair(char('.'), multispace0), parse_checkable),
            ),
            |((x, a), body)| Checkable::Pi(x, a.into(), body.into()),
        ),
        parse_function,
    ))(input)
}

pub fn parse_checkable(input: &str) -> IResult<&str, Checkable> {
    parse_abstraction(input)
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
