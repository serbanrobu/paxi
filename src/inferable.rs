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
    Context, Environment, Identifier, Type,
};

#[derive(Clone, Debug)]
pub enum Inferable {
    Application {
        operator: Box<Inferable>,
        operand: Box<Checkable>,
    },
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
            Self::Variable(x) => context.get(x).cloned().wrap_err("unknown identifier"),
        }
    }

    pub fn evaluate(&self, environment: &Environment) -> Value {
        match self {
            Self::Application { operator, operand } => match operator.evaluate(environment) {
                Value::Lambda(Closure {
                    environment: mut env,
                    identifier: x,
                    body,
                }) => {
                    env.insert(x, operand.evaluate(environment));
                    body.evaluate(&env)
                }
                Value::Neutral(neutral) => Value::Neutral(Neutral::Application {
                    operator: neutral.into(),
                    operand: operand.evaluate(environment).into(),
                }),
                _ => unreachable!(),
            },
            Self::Variable(x) => environment
                .get(x)
                .cloned()
                .unwrap_or_else(|| Value::Neutral(Neutral::Variable(x.to_owned()))),
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
