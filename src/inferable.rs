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
    Context, Environment, Identifier, Level, Type,
};

#[derive(Clone, Debug)]
pub enum Inferable {
    Application {
        operator: Box<Inferable>,
        operand: Box<Checkable>,
    },
    NaturalInduction {
        x: Identifier,
        motive: Box<Checkable>,
        base: Box<Checkable>,
        y: Identifier,
        z: Identifier,
        step: Box<Checkable>,
        target: Box<Checkable>,
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
            (
                Self::NaturalInduction {
                    x,
                    motive,
                    base,
                    y,
                    z,
                    step,
                    target,
                },
                Self::NaturalInduction {
                    x: x_,
                    motive: motive_,
                    base: base_,
                    y: y_,
                    z: z_,
                    step: step_,
                    target: target_,
                },
            ) => {
                let mut step_ctx = context.to_owned();
                step_ctx.insert(y.to_owned(), index);
                step_ctx.insert(z.to_owned(), index + 1);

                let mut step_ctx_ = context.to_owned();
                step_ctx_.insert(y_.to_owned(), index);
                step_ctx_.insert(z_.to_owned(), index + 1);

                motive.alpha_eq_(
                    motive_,
                    index + 1,
                    &context.update(x.to_owned(), index),
                    &context_.update(x_.to_owned(), index),
                ) && base.alpha_eq_(base_, index, context, context_)
                    && step.alpha_eq_(step_, index + 2, &step_ctx, &step_ctx_)
                    && target.alpha_eq_(target_, index, context, context_)
            }
            (Self::Variable(x), Self::Variable(y)) => match (context.get(x), context_.get(y)) {
                (None, None) => x == y,
                (Some(&i), Some(&j)) => i == j,
                _ => false,
            },
            _ => false,
        }
    }

    pub fn infer(&self, i: Level, context: &Context, environment: &Environment) -> Result<Type> {
        match self {
            Self::Application { operator, operand } => {
                let t = operator.infer(i, context, environment)?;

                match t {
                    Type::Function(ref a, b) => {
                        operand.check(i, a, context, environment)?;
                        Ok(*b)
                    }
                    Type::Pi(ref a, body) => {
                        operand.check(i, a, context, environment)?;
                        Ok(body.apply(operand.evaluate(environment)))
                    }
                    _ => Err(eyre!("illegal application")),
                }
            }
            Self::NaturalInduction {
                x,
                motive,
                base,
                y,
                z,
                step,
                target,
            } => {
                motive.check(
                    i,
                    &Type::Universe(i),
                    &context.update(x.to_owned(), Type::Natural),
                    environment,
                )?;

                base.check(
                    i,
                    &motive.evaluate(&environment.update(x.to_owned(), Value::Zero)),
                    context,
                    environment,
                )?;

                let mut step_ctx = context.to_owned();
                step_ctx.insert(y.to_owned(), Type::Natural);
                step_ctx.insert(z.to_owned(), motive.evaluate(environment));

                step.check(
                    i,
                    &motive.evaluate(&environment.update(
                        x.to_owned(),
                        Value::Successor(Value::Neutral(Neutral::Variable(y.to_owned())).into()),
                    )),
                    &step_ctx,
                    environment,
                )?;

                target.check(i, &Type::Natural, context, environment)?;

                Ok(
                    motive
                        .evaluate(&environment.update(x.to_owned(), target.evaluate(environment))),
                )
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
            Self::NaturalInduction {
                x,
                motive,
                base,
                y,
                z,
                step,
                target,
            } => natural_induction(
                x,
                motive,
                base,
                y,
                z,
                step,
                target.evaluate(environment),
                environment,
            ),
            Self::Variable(x) => environment
                .get(x)
                .cloned()
                .unwrap_or_else(|| Value::Neutral(Neutral::Variable(x.to_owned()))),
        }
    }
}

fn natural_induction(
    x: &Identifier,
    motive: &Checkable,
    base: &Checkable,
    y: &Identifier,
    z: &Identifier,
    step: &Checkable,
    target: Value,
    environment: &Environment,
) -> Value {
    match target {
        Value::Zero => base.evaluate(environment),
        Value::Successor(n) => {
            let mut env = environment.to_owned();
            env.insert(y.to_owned(), n.as_ref().to_owned());

            env.insert(
                z.to_owned(),
                natural_induction(x, motive, base, y, z, step, *n, environment),
            );

            step.evaluate(&env)
        }
        Value::Neutral(neutral) => Value::Neutral(Neutral::NaturalInduction {
            x: x.to_owned(),
            motive: motive.evaluate(environment).into(),
            base: base.evaluate(environment).into(),
            y: y.to_owned(),
            z: z.to_owned(),
            step: step.evaluate(environment).into(),
            target: neutral.into(),
        }),
        _ => unreachable!(),
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
