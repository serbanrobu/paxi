use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, char, multispace0, multispace1, u64},
    combinator::{map, recognize, value},
    multi::{fold_many0, many0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, tuple},
    IResult,
};

use crate::{checkable::Checkable, inferable::Inferable, Identifier};

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
        parens(ws(parse_inferable)),
        map(
            preceded(
                pair(tag("indNat"), multispace0),
                parens(tuple((
                    ws(parse_identifier),
                    preceded(char('.'), ws(parse_checkable)),
                    preceded(char(','), ws(parse_checkable)),
                    preceded(char(','), ws(parse_identifier)),
                    preceded(char('.'), ws(parse_identifier)),
                    preceded(char('.'), ws(parse_checkable)),
                    preceded(char(','), ws(parse_checkable)),
                ))),
            ),
            |(x, motive, base, y, z, step, target)| Inferable::NaturalInduction {
                x,
                motive: motive.into(),
                base: base.into(),
                y,
                z,
                step: step.into(),
                target: target.into(),
            },
        ),
        map(parse_identifier, Inferable::Variable),
    ))(input)
}

fn parse_application(input: &str) -> IResult<&str, Inferable> {
    let (input, atom) = parse_inferable_atom(input)?;

    fold_many0(
        parens(separated_list1(char(','), ws(parse_checkable))),
        move || atom.clone(),
        |operator, operands| {
            operands
                .into_iter()
                .fold(operator, |operator, operand| Inferable::Application {
                    operator: operator.into(),
                    operand: operand.into(),
                })
        },
    )(input)
}

pub fn parse_inferable(input: &str) -> IResult<&str, Inferable> {
    parse_application(input)
}

fn parse_checkable_atom(input: &str) -> IResult<&str, Checkable> {
    alt((
        map(u64, |n| {
            (0..n).fold(Checkable::Zero, |n, _| Checkable::Successor(n.into()))
        }),
        value(Checkable::Natural, tag("Nat")),
        map(
            preceded(pair(tag("succ"), multispace0), parens(ws(parse_checkable))),
            |n| Checkable::Successor(n.into()),
        ),
        map(
            preceded(pair(char('U'), multispace0), parens(ws(parse_checkable))),
            |i| Checkable::Universe(i.into()),
        ),
        value(Checkable::Zero, tag("zero")),
        map(parse_inferable, Checkable::Inferable),
        parens(ws(parse_checkable)),
    ))(input)
}

fn parse_function(input: &str) -> IResult<&str, Checkable> {
    map(
        separated_list1(ws(tag("→ ")), parse_checkable_atom),
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
