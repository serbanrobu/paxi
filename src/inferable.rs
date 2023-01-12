use color_eyre::{
    eyre::{eyre, ContextCompat},
    Result,
};
use im_rc::HashMap;

use crate::{
    checkable::Checkable,
    value::{Closure, Neutral, Value},
    Context, Environment, Identifier, Lift, Type,
};

#[derive(Clone, Debug)]
pub enum Inferable {
    Application {
        operator: Box<Inferable>,
        operand: Box<Checkable>,
    },
    Lift(Box<Inferable>),
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
            Self::Variable(x) => context.get(x).cloned().wrap_err("unknown identifier"),
        }
    }

    pub fn evaluate(&self, environment: &Environment, lift: Lift) -> Value {
        match self {
            Self::Application { operator, operand } => match operator.evaluate(environment, lift) {
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
            },
            Self::Lift(inferable) => inferable.evaluate(environment, lift + 1),
            Self::Variable(x) => environment
                .get(x)
                .cloned()
                .unwrap_or_else(|| Value::Neutral(Neutral::Variable(lift, x.to_owned()))),
        }
    }
}
