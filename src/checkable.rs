use std::str::FromStr;

use color_eyre::{eyre::eyre, Report, Result};
use im_rc::HashMap;
use nom::{combinator::eof, error::Error, sequence::terminated, Finish};

use crate::{
    inferable::Inferable,
    parser,
    value::{Closure, Neutral, Value},
    Context, Environment, Identifier, Level, Lift, Type,
};

#[derive(Clone, Debug)]
pub enum Checkable {
    Function(Box<Checkable>, Box<Checkable>),
    Inferable(Inferable),
    Lambda {
        identifier: Identifier,
        body: Box<Checkable>,
    },
    Lift(Box<Checkable>),
    Pi(Identifier, Box<Checkable>, Box<Checkable>),
    Universe(Level),
}

impl Checkable {
    fn reduce(&self, environment: &Environment) -> Checkable {
        self.reduce_(environment, 0)
    }

    fn reduce_(&self, environment: &Environment, lift: Lift) -> Checkable {
        let ctx = environment.keys().collect();
        self.evaluate_(environment, lift).quote(&ctx)
    }

    pub fn convert(&self, other: &Self, environment: &Environment) -> bool {
        self.convert_(other, environment, 0)
    }

    fn convert_(&self, other: &Self, environment: &Environment, lift: Lift) -> bool {
        let ctx = environment.keys().collect();

        self.evaluate_(environment, lift)
            .convert(&other.evaluate_(environment, lift), &ctx)
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
            (Self::Lift(checkable), Self::Lift(checkable_)) => {
                checkable.alpha_eq_(checkable_, index, context, context_)
            }
            (Self::Pi(x, a, body), Self::Pi(y, a_, body_)) => {
                a.alpha_eq_(a_, index, context, context_) && {
                    let mut ctx = context.to_owned();
                    ctx.insert(x.to_owned(), index);

                    let mut ctx_ = context_.to_owned();
                    ctx_.insert(y.to_owned(), index);

                    body.alpha_eq_(body_, index + 1, &ctx, &ctx_)
                }
            }
            (Self::Universe(i), Self::Universe(j)) => i == j,
            _ => false,
        }
    }

    pub fn check(&self, t: &Type, context: &Context) -> Result<()> {
        match (self, t) {
            (Self::Function(a, b), Type::Universe(_i)) => {
                a.check(t, context)?;
                b.check(t, context)
            }
            (Self::Inferable(inferable), _) => {
                let t_ = inferable.infer(context)?;
                let ctx = context.iter().map(|(x, _)| x.to_owned()).collect();

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
                ctx.insert(x.to_owned(), (a.as_ref().to_owned(), None));
                body.check(b, &ctx)
            }
            (
                Self::Lambda {
                    identifier: x,
                    body,
                },
                Type::Pi(a, closure),
            ) => {
                let b = closure.apply(Value::Neutral(Neutral::Variable(0, x.to_owned())));

                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), (a.as_ref().to_owned(), None));

                body.check(&b, &ctx)
            }
            (Self::Lift(checkable), &Type::Universe(i @ 1..)) => {
                checkable.check(&Type::Universe(i - 1), context)
            }
            (Self::Pi(x, a, body), Type::Universe(_i)) => {
                a.check(t, context)?;

                let mut ctx = context.to_owned();
                ctx.insert(x.to_owned(), (a.evaluate(&HashMap::new()), None));

                body.check(t, &ctx)
            }
            (&Self::Universe(i), &Type::Universe(j)) if i < j => Ok(()),
            _ => Err(eyre!("type mismatch")),
        }
    }

    pub fn evaluate(&self, environment: &Environment) -> Value {
        self.evaluate_(environment, 0)
    }

    pub fn evaluate_(&self, environment: &Environment, lift: Lift) -> Value {
        match self {
            Self::Function(a, b) => Value::Function(
                a.evaluate_(environment, lift).into(),
                b.evaluate_(environment, lift).into(),
            ),
            Self::Inferable(inferable) => inferable.evaluate(environment, lift),
            Self::Lambda {
                identifier: x,
                body,
            } => Value::Lambda(Closure {
                environment: environment.to_owned(),
                lift,
                identifier: x.to_owned(),
                body: body.as_ref().to_owned(),
            }),
            Self::Lift(checkable) => checkable.evaluate_(environment, lift + 1),
            Self::Pi(x, a, body) => Value::Pi(
                a.evaluate_(environment, lift).into(),
                Closure {
                    environment: environment.to_owned(),
                    lift,
                    identifier: x.to_owned(),
                    body: body.as_ref().to_owned(),
                },
            ),
            &Self::Universe(i) => Value::Universe(i),
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
