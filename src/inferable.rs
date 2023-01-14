use std::str::FromStr;

use color_eyre::{
    eyre::{eyre, ContextCompat},
    Report, Result,
};
use im_rc::HashMap;
use nom::{combinator::eof, error::Error, sequence::terminated, Finish};

use crate::{
    checkable::Checkable,
    parser,
    value::{Closure, Neutral, Value},
    Context, Environment, Identifier, Level, Lift, Type,
};

#[derive(Clone, Debug)]
pub enum Inferable {
    Application {
        operator: Box<Inferable>,
        operand: Box<Checkable>,
    },
    Lift(Box<Inferable>),
    Term(Box<Inferable>, Box<Checkable>),
    Type(Level, Box<Checkable>),
    Variable(Identifier),
}

impl Inferable {
    pub fn alpha_eq(
        &self,
        other: &Self,
        index: usize,
        context: &HashMap<Identifier, usize>,
        context_: &HashMap<Identifier, usize>,
    ) -> bool {
        match (self, other) {
            (
                Self::Application {
                    operator: f,
                    operand: a,
                },
                Self::Application {
                    operator: f_,
                    operand: a_,
                },
            ) => {
                f.alpha_eq(f_, index, context, context_)
                    && a.alpha_eq_(a_, index, context, context_)
            }
            (Self::Lift(a), Self::Lift(a_)) => a.alpha_eq(a_, index, context, context_),
            (Self::Term(t, a), Self::Term(t_, a_)) => {
                t.alpha_eq(t_, index, context, context_)
                    && a.alpha_eq_(a_, index, context, context_)
            }
            (Self::Type(i, t), Self::Type(j, t_)) => {
                i == j && t.alpha_eq_(t_, index, context, context_)
            }
            (Self::Variable(x), Self::Variable(y)) => match (context.get(x), context_.get(y)) {
                (None, None) => x == y,
                (Some(&i), Some(&j)) => i == j,
                _ => false,
            },
            _ => false,
        }
    }

    pub fn infer(&self, context: &Context, environment: &Environment) -> Result<Type> {
        match self {
            Self::Application { operator, operand } => {
                let t = operator.infer(context, environment)?;

                let Type::Function(ref a, b) = t else {
                    return Err(eyre!("illegal application"));
                };

                operand.check(a, context, environment)?;

                Ok(*b)
            }
            Self::Lift(inferable) => {
                let t = inferable.infer(context, environment)?;

                let Type::Universe(i) = t else {
                    return Err(eyre!("illegal lifting"));
                };

                Ok(Type::Universe(i + 1))
            }
            Self::Term(t, a) => {
                let u = t.infer(context, environment)?;

                let Type::Universe(_i) = u else {
                    return Err(eyre!("illegal term"));
                };

                let t_ = t.evaluate(environment);

                a.check(&t_, context, environment)?;

                Ok(t_)
            }
            Self::Type(i, t) => {
                let u = Type::Universe(*i);
                t.check(&u, context, environment)?;
                Ok(u)
            }
            Self::Variable(x) => context.get(x).cloned().wrap_err("unknown identifier"),
        }
    }

    pub fn evaluate(&self, environment: &Environment) -> Value {
        self.evaluate_(environment, 0)
    }

    pub fn evaluate_(&self, environment: &Environment, lift: Lift) -> Value {
        match self {
            Self::Application { operator, operand } => {
                match operator.evaluate_(environment, lift) {
                    Value::Lambda(Closure {
                        environment: mut env,
                        lift,
                        identifier: x,
                        body,
                    }) => {
                        env.insert(x, operand.evaluate_(environment, lift));
                        body.evaluate_(&env, lift)
                    }
                    Value::Neutral(neutral) => Value::Neutral(Neutral::Application {
                        operator: neutral.into(),
                        operand: operand.evaluate_(environment, lift).into(),
                    }),
                    _ => unreachable!(),
                }
            }
            Self::Lift(inferable) => inferable.evaluate_(environment, lift + 1),
            Self::Term(_t, a) => a.evaluate_(environment, lift),
            Self::Type(_i, t) => t.evaluate_(environment, lift),
            Self::Variable(x) => environment
                .get(x)
                .cloned()
                .unwrap_or_else(|| Value::Neutral(Neutral::Variable(lift, x.to_owned()))),
        }
    }
}

impl FromStr for Inferable {
    type Err = Report;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let (_remaining, inferable) = terminated(parser::parse_inferable, eof)(s)
            .finish()
            .map_err(|e| Error::new(e.input.to_owned(), e.code))?;

        Ok(inferable)
    }
}
