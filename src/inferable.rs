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
    Binding, Context, Environment, Identifier, Level, Type,
};

#[derive(Clone, Debug)]
pub enum Inferable {
    Application {
        operator: Box<Inferable>,
        operand: Box<Checkable>,
    },
    NaturalInduction {
        motive: Box<Binding<Checkable>>,
        base: Box<Checkable>,
        step: Box<Binding<Binding<Checkable>>>,
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
                    motive: box Binding(x, motive_),
                    base,
                    step: box Binding(y, Binding(z, step_)),
                    target,
                },
                Self::NaturalInduction {
                    motive: box Binding(x_, motive__),
                    base: base_,
                    step: box Binding(y_, Binding(z_, step__)),
                    target: target_,
                },
            ) => {
                let mut step_ctx = context.to_owned();
                step_ctx.insert(y.to_owned(), index);
                step_ctx.insert(z.to_owned(), index + 1);

                let mut step_ctx_ = context.to_owned();
                step_ctx_.insert(y_.to_owned(), index);
                step_ctx_.insert(z_.to_owned(), index + 1);

                motive_.alpha_eq_(
                    motive__,
                    index + 1,
                    &context.update(x.to_owned(), index),
                    &context_.update(x_.to_owned(), index),
                ) && base.alpha_eq_(base_, index, context, context_)
                    && step_.alpha_eq_(step__, index + 2, &step_ctx, &step_ctx_)
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
                motive: box Binding(x, motive_),
                base,
                step: box Binding(y, Binding(z, step_)),
                target,
            } => {
                motive_.check(
                    i,
                    &Type::Universe(i),
                    &context.update(x.to_owned(), Type::Natural),
                    environment,
                )?;

                base.check(
                    i,
                    &motive_.evaluate(&environment.update(x.to_owned(), Value::Zero)),
                    context,
                    environment,
                )?;

                let mut step_ctx = context.to_owned();
                step_ctx.insert(y.to_owned(), Type::Natural);
                step_ctx.insert(z.to_owned(), motive_.evaluate(environment));

                step_.check(
                    i,
                    &motive_.evaluate(&environment.update(
                        x.to_owned(),
                        Value::Successor(box Value::Neutral(Neutral::Variable(y.to_owned()))),
                    )),
                    &step_ctx,
                    environment,
                )?;

                target.check(i, &Type::Natural, context, environment)?;

                Ok(motive_
                    .evaluate(&environment.update(x.to_owned(), target.evaluate(environment))))
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
                    operator: box neutral,
                    operand: box operand.evaluate(environment),
                }),
                _ => unreachable!(),
            },
            Self::NaturalInduction {
                motive,
                base,
                step,
                target,
            } => natural_induction(
                motive,
                base,
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
    motive: &Binding<Checkable>,
    base: &Checkable,
    step: &Binding<Binding<Checkable>>,
    target: Value,
    environment: &Environment,
) -> Value {
    match target {
        Value::Zero => base.evaluate(environment),
        Value::Successor(box n) => {
            let Binding(y, Binding(z, step_)) = step;
            let mut env = environment.to_owned();
            env.insert(y.to_owned(), n.clone());

            env.insert(
                z.to_owned(),
                natural_induction(motive, base, step, n, environment),
            );

            step_.evaluate(&env)
        }
        Value::Neutral(neutral) => {
            let Binding(x, motive_) = motive;
            let Binding(y, Binding(z, step_)) = step;

            Value::Neutral(Neutral::NaturalInduction {
                motive: box Binding(x.to_owned(), motive_.evaluate(environment)),
                base: box base.evaluate(environment),
                step: box Binding(
                    y.to_owned(),
                    Binding(z.to_owned(), step_.evaluate(environment)),
                ),
                target: box neutral,
            })
        }
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
