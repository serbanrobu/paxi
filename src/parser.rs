use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, char, multispace0, multispace1, u64, u8},
    combinator::{map, recognize, value},
    multi::{fold_many0, many0, many_m_n, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
    IResult,
};

use crate::{checkable::Checkable, inferable::Inferable, Binding, Identifier};

fn parse_identifier(input: &str) -> IResult<&str, Identifier> {
    map(
        recognize(pair(
            alt((alpha1, tag("_"))),
            many0(alt((alphanumeric1, tag("_"), tag("\'")))),
        )),
        |s: &str| s.to_owned(),
    )(input)
}

fn parse_binding<const N: usize>(input: &str) -> IResult<&str, Binding<N>> {
    map(
        pair(
            many_m_n(N, N, terminated(parse_identifier, ws(char('.')))),
            parse_checkable,
        ),
        |(xs, t)| Binding(xs.try_into().unwrap(), t),
    )(input)
}

fn parse_inferable_atom(input: &str) -> IResult<&str, Inferable> {
    alt((
        parens(ws(parse_inferable)),
        map(
            preceded(
                pair(tag("indNat"), multispace0),
                parens(tuple((
                    ws(parse_binding::<1>),
                    preceded(char(','), ws(parse_checkable)),
                    preceded(char(','), ws(parse_binding::<2>)),
                    preceded(char(','), ws(parse_checkable)),
                ))),
            ),
            |(motive, base, step, target)| Inferable::NaturalInduction {
                motive: box motive,
                base: box base,
                step: box step,
                target: box target,
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
                    operator: box operator,
                    operand: box operand,
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
            (0..n).fold(Checkable::Zero, |n, _| Checkable::Successor(box n))
        }),
        value(Checkable::Natural, tag("Nat")),
        map(
            preceded(pair(tag("succ"), multispace0), parens(ws(parse_checkable))),
            |n| Checkable::Successor(box n),
        ),
        map(
            preceded(pair(char('U'), multispace0), parens(ws(u8))),
            Checkable::Universe,
        ),
        value(Checkable::Zero, tag("zero")),
        map(parse_inferable, Checkable::Inferable),
        parens(ws(parse_checkable)),
    ))(input)
}

fn parse_abstraction(input: &str) -> IResult<&str, Checkable> {
    alt((
        map(
            preceded(pair(char('λ'), multispace1), parse_binding),
            |binding| Checkable::Lambda(box binding),
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
            |((x, a), body)| Checkable::Pi(box a, box Binding([x], body)),
        ),
        parse_checkable_atom,
    ))(input)
}

fn parse_function(input: &str) -> IResult<&str, Checkable> {
    map(
        separated_list1(ws(tag("→ ")), parse_abstraction),
        |list: Vec<_>| {
            list.into_iter()
                .rev()
                .reduce(|b, a| Checkable::Function(box a, box b))
                .unwrap()
        },
    )(input)
}

pub fn parse_checkable(input: &str) -> IResult<&str, Checkable> {
    parse_function(input)
}

pub fn parens<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(char('('), inner, char(')'))
}

pub fn ws<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(multispace0, inner, multispace0)
}
