use std::str::FromStr;

use color_eyre::{eyre::eyre, Report, Result};
use im_rc::{HashMap, HashSet};
use nom::{combinator::eof, error::Error, sequence::terminated, Finish};

use crate::{
    inferable::Inferable,
    parser,
    value::{Closure, Neutral, Value},
    Binding, Context, Environment, Identifier, Level, Type,
};

#[derive(Clone, Debug)]
pub enum Checkable {
    Function(Box<Checkable>, Box<Checkable>),
    Inferable(Inferable),
    Lambda {
        identifier: Identifier,
        body: Box<Checkable>,
    },
    Natural,
    Pi(Box<Checkable>, Box<Binding<Checkable>>),
    Successor(Box<Checkable>),
    Universe(Level),
    Zero,
}

impl Checkable {
    pub fn reduce(&self, context: &HashSet<Identifier>, environment: &Environment) -> Checkable {
        self.evaluate(environment).quote(context)
    }

    pub fn convert(
        &self,
        other: &Self,
        context: &HashSet<Identifier>,
        environment: &Environment,
    ) -> bool {
        self.evaluate(environment)
            .convert(&other.evaluate(environment), context)
    }

    pub fn alpha_eq(&self, other: &Self) -> bool {
        self.alpha_eq_(other, 0, &HashMap::new(), &HashMap::new())
    }

    pub fn alpha_eq_(
        &self,
        other: &Self,
        index: usize,
        context: &HashMap<Identifier, usize>,
        context_: &HashMap<Identifier, usize>,
    ) -> bool {
        match (self, other) {
            (Self::Function(a, b), Self::Function(a_, b_)) => {
                a.alpha_eq_(a_, index, context, context_)
                    && b.alpha_eq_(b_, index, context, context_)
            }
            (Self::Inferable(inferable), Self::Inferable(inferable_)) => {
                inferable.alpha_eq(inferable_, index, context, context_)
            }
            (
                Self::Lambda {
                    identifier: x,
                    body,
                },
                Self::Lambda {
                    identifier: y,
                    body: body_,
                },
            ) => {
                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), index);

                let mut ctx_ = context_.to_owned();
                ctx_.insert(y.to_owned(), index);

                body.alpha_eq_(body_, index + 1, &ctx, &ctx_)
            }
            (Self::Natural, Self::Natural) => true,
            (Self::Pi(a, box b), Self::Pi(a_, box b_)) => {
                a.alpha_eq_(a_, index, context, context_) && {
                    let Binding(x, body) = b;
                    let mut ctx = context.to_owned();
                    ctx.insert(x.to_owned(), index);

                    let Binding(x_, body_) = b_;
                    let mut ctx_ = context_.to_owned();
                    ctx_.insert(x_.to_owned(), index);

                    body.alpha_eq_(body_, index + 1, &ctx, &ctx_)
                }
            }
            (Self::Successor(n), Self::Successor(n_)) => n.alpha_eq_(n_, index, context, context_),
            (Self::Universe(i), Self::Universe(j)) => i == j,
            (Self::Zero, Self::Zero) => true,
            _ => false,
        }
    }

    pub fn check(
        &self,
        i: Level,
        t: &Type,
        context: &Context,
        environment: &Environment,
    ) -> Result<()> {
        match (self, t) {
            (Self::Function(a, b), Type::Universe(_i)) => {
                a.check(i, t, context, environment)?;
                b.check(i, t, context, environment)
            }
            (Self::Inferable(inferable), _) => {
                let t_ = inferable.infer(i, context, environment)?;
                let ctx = context.iter().map(|(x, _)| x.to_owned()).collect();

                // Coercion
                if let (&Type::Universe(j), &Type::Universe(j_)) = (&t_, t) {
                    if j > j_ {
                        return Err(eyre!("type mismatch"));
                    }

                    return Ok(());
                }

                if !t_.convert(t, &ctx) {
                    return Err(eyre!("type mismatch"));
                }

                Ok(())
            }
            (
                Self::Lambda {
                    identifier: x,
                    body,
                },
                Type::Function(box a, b),
            ) => {
                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), a.to_owned());
                body.check(i, b, &ctx, environment)
            }
            (
                Self::Lambda {
                    identifier: x,
                    body,
                },
                Type::Pi(box a, closure),
            ) => {
                let b = closure.apply(Value::Neutral(Neutral::Variable(x.to_owned())));

                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), a.to_owned());

                body.check(i, &b, &ctx, environment)
            }
            (Self::Natural, Type::Universe(_i)) => Ok(()),
            (Self::Pi(a, box b), Type::Universe(_i)) => {
                a.check(i, t, context, environment)?;

                let Binding(x, body) = b;
                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), a.evaluate(environment));

                body.check(i, t, &ctx, environment)
            }
            (Self::Successor(n), Type::Natural) => n.check(i, t, context, environment),
            (&Self::Universe(j), &Type::Universe(k)) if j < k => Ok(()),
            (Self::Zero, Type::Natural) => Ok(()),
            _ => Err(eyre!("type mismatch")),
        }
    }

    pub fn evaluate(&self, environment: &Environment) -> Value {
        match self {
            Self::Function(a, b) => {
                Value::Function(box a.evaluate(environment), box b.evaluate(environment))
            }
            Self::Inferable(inferable) => inferable.evaluate(environment),
            Self::Lambda {
                identifier: x,
                box body,
            } => Value::Lambda(Closure {
                environment: environment.to_owned(),
                identifier: x.to_owned(),
                body: body.to_owned(),
            }),
            Self::Natural => Value::Natural,
            Self::Pi(a, box Binding(x, body)) => Value::Pi(
                box a.evaluate(environment),
                Closure {
                    environment: environment.to_owned(),
                    identifier: x.to_owned(),
                    body: body.to_owned(),
                },
            ),
            Self::Successor(n) => Value::Successor(box n.evaluate(environment)),
            &Self::Universe(i) => Value::Universe(i),
            Self::Zero => Value::Zero,
        }
    }
}

impl FromStr for Checkable {
    type Err = Report;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let (_remaining, checkable) = terminated(parser::parse_checkable, eof)(s)
            .finish()
            .map_err(|e| Error::new(e.input.to_owned(), e.code))?;

        Ok(checkable)
    }
}
