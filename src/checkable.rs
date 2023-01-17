use std::str::FromStr;

use color_eyre::{eyre::eyre, Report, Result};
use im_rc::HashMap;
use nom::{combinator::eof, error::Error, sequence::terminated, Finish};

use crate::{
    inferable::Inferable,
    parser,
    value::{Closure, Neutral, Value},
    Context, Environment, Identifier, Type,
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
    Pi(Identifier, Box<Checkable>, Box<Checkable>),
    Successor(Box<Checkable>),
    Universe(Box<Checkable>),
    Zero,
}

impl Checkable {
    pub fn reduce(&self, environment: &Environment) -> Checkable {
        let ctx = environment.keys().collect();
        self.evaluate(environment).quote(&ctx)
    }

    pub fn convert(&self, other: &Self, environment: &Environment) -> bool {
        let ctx = environment.keys().collect();

        self.evaluate(environment)
            .convert(&other.evaluate(environment), &ctx)
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
            (Self::Pi(x, a, body), Self::Pi(y, a_, body_)) => {
                a.alpha_eq_(a_, index, context, context_) && {
                    let mut ctx = context.to_owned();
                    ctx.insert(x.to_owned(), index);

                    let mut ctx_ = context_.to_owned();
                    ctx_.insert(y.to_owned(), index);

                    body.alpha_eq_(body_, index + 1, &ctx, &ctx_)
                }
            }
            (Self::Successor(n), Self::Successor(n_)) => n.alpha_eq_(n_, index, context, context_),
            (Self::Universe(i), Self::Universe(j)) => i.alpha_eq_(j, index, context, context_),
            (Self::Zero, Self::Zero) => true,
            _ => false,
        }
    }

    pub fn check(
        &self,
        level: &Value,
        t: &Type,
        context: &Context,
        environment: &Environment,
    ) -> Result<()> {
        match (self, t) {
            (Self::Function(a, b), Type::Universe(_i)) => {
                a.check(level, t, context, environment)?;
                b.check(level, t, context, environment)
            }
            (Self::Inferable(inferable), _) => {
                let t_ = inferable.infer(level, context, environment)?;
                let ctx = context.iter().map(|(x, _)| x.to_owned()).collect();

                // Coercion
                if let (Type::Universe(i), Type::Universe(j)) = (&t_, t) {
                    if j.lt(i, &ctx) {
                        return Err(eyre!("type mismatch"));
                    }

                    return Ok(());
                }

                if !t_.convert(&t, &ctx) {
                    return Err(eyre!("type mismatch"));
                }

                Ok(())
            }
            (
                Self::Lambda {
                    identifier: x,
                    body,
                },
                Type::Function(a, b),
            ) => {
                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), a.as_ref().to_owned());
                body.check(level, b, &ctx, environment)
            }
            (
                Self::Lambda {
                    identifier: x,
                    body,
                },
                Type::Pi(a, closure),
            ) => {
                let b = closure.apply(Value::Neutral(Neutral::Variable(x.to_owned())));

                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), a.as_ref().to_owned());

                body.check(level, &b, &ctx, environment)
            }
            (Self::Natural, Type::Universe(_i)) => Ok(()),
            (Self::Pi(x, a, body), Type::Universe(_i)) => {
                a.check(level, t, context, environment)?;

                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), a.evaluate(environment));

                body.check(level, t, &ctx, environment)
            }
            (Self::Successor(n), Type::Natural) => n.check(level, t, context, environment),
            (Self::Universe(i), Type::Universe(j)) => {
                i.check(level, &Type::Natural, context, environment)?;
                let i = i.evaluate(environment);
                let ctx = context.iter().map(|(x, _)| x.to_owned()).collect();

                if j.lte(&i, &ctx) {
                    return Err(eyre!("type mismatch"));
                }

                Ok(())
            }
            (Self::Zero, Type::Natural) => Ok(()),
            _ => Err(eyre!("type mismatch")),
        }
    }

    pub fn evaluate(&self, environment: &Environment) -> Value {
        match self {
            Self::Function(a, b) => Value::Function(
                a.evaluate(environment).into(),
                b.evaluate(environment).into(),
            ),
            Self::Inferable(inferable) => inferable.evaluate(environment),
            Self::Lambda {
                identifier: x,
                body,
            } => Value::Lambda(Closure {
                environment: environment.to_owned(),
                identifier: x.to_owned(),
                body: body.as_ref().to_owned(),
            }),
            Self::Natural => Value::Natural,
            Self::Pi(x, a, body) => Value::Pi(
                a.evaluate(environment).into(),
                Closure {
                    environment: environment.to_owned(),
                    identifier: x.to_owned(),
                    body: body.as_ref().to_owned(),
                },
            ),
            Self::Successor(n) => Value::Successor(n.evaluate(environment).into()),
            Self::Universe(i) => Value::Universe(i.evaluate(environment).into()),
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
