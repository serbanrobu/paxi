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
        target: Box<Inferable>,
        motive: Box<Binding<1>>,
        zero: Box<Checkable>,
        successor: Box<Binding<2>>,
    },
    SigmaInduction {
        target: Box<Inferable>,
        motive: Box<Binding<1>>,
        pair: Box<Binding<2>>,
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
                    target,
                    motive: box Binding([x], motive_),
                    zero: base,
                    successor: box Binding([y, z], succ_),
                },
                Self::NaturalInduction {
                    target: target_,
                    motive: box Binding([x_], motive__),
                    zero: base_,
                    successor: box Binding([y_, z_], succ__),
                },
            ) => {
                let mut step_ctx = context.to_owned();
                step_ctx.insert(y.to_owned(), index);
                step_ctx.insert(z.to_owned(), index + 1);

                let mut step_ctx_ = context.to_owned();
                step_ctx_.insert(y_.to_owned(), index);
                step_ctx_.insert(z_.to_owned(), index + 1);

                target.alpha_eq(target_, index, context, context_)
                    && motive_.alpha_eq_(
                        motive__,
                        index + 1,
                        &context.update(x.to_owned(), index),
                        &context_.update(x_.to_owned(), index),
                    )
                    && base.alpha_eq_(base_, index, context, context_)
                    && succ_.alpha_eq_(succ__, index + 2, &step_ctx, &step_ctx_)
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
                        Ok(body.evaluate([operand.evaluate(environment)]))
                    }
                    _ => Err(eyre!("illegal application")),
                }
            }
            Self::NaturalInduction {
                motive: box Binding([x], motive_),
                zero: base,
                successor: box Binding([y, z], step_),
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

                let Type::Natural = target.infer(i, context, environment)? else {
                    return Err(eyre!("not a natural"));
                };

                Ok(motive_
                    .evaluate(&environment.update(x.to_owned(), target.evaluate(environment))))
            }
            Self::SigmaInduction {
                target: p,
                motive: box Binding([z], c),
                pair: box Binding([x, y], g),
            } => {
                let p_type = p.infer(i, context, environment)?;

                let Type::Sigma(box a, b) = p_type.clone() else {
                    return Err(eyre!("illegal sigma induction"));
                };

                c.check(
                    i,
                    &Type::Universe(i),
                    &context.update(z.to_owned(), p_type),
                    environment,
                )?;

                g.check(
                    i,
                    &c.evaluate(&environment.update(
                        z.to_owned(),
                        Value::Pair(
                            box Value::Neutral(Neutral::Variable(x.to_owned())),
                            box Value::Neutral(Neutral::Variable(y.to_owned())),
                        ),
                    )),
                    &{
                        let mut ctx = context.to_owned();
                        ctx.insert(x.to_owned(), a);

                        ctx.insert(
                            y.to_owned(),
                            b.evaluate([Value::Neutral(Neutral::Variable(x.to_owned()))]),
                        );

                        ctx
                    },
                    environment,
                )?;

                Ok(c.evaluate(&environment.update(z.to_owned(), p.evaluate(environment))))
            }
            Self::Variable(x) => context.get(x).cloned().wrap_err("unknown identifier"),
        }
    }

    pub fn evaluate(&self, environment: &Environment) -> Value {
        match self {
            Self::Application { operator, operand } => match operator.evaluate(environment) {
                Value::Lambda(Closure {
                    environment: mut env,
                    binding: Binding([x], body),
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
                target,
                box motive,
                zero,
                box successor,
            } => natural_induction(
                target.evaluate(environment),
                Closure {
                    environment: environment.to_owned(),
                    binding: motive.to_owned(),
                },
                zero.evaluate(environment),
                Closure {
                    environment: environment.to_owned(),
                    binding: successor.to_owned(),
                },
            ),
            Self::SigmaInduction {
                target,
                box motive,
                box pair,
            } => sigma_induction(
                target.evaluate(environment),
                Closure {
                    environment: environment.to_owned(),
                    binding: motive.to_owned(),
                },
                Closure {
                    environment: environment.to_owned(),
                    binding: pair.to_owned(),
                },
            ),
            Self::Variable(x) => environment
                .get(x)
                .cloned()
                .unwrap_or_else(|| Value::Neutral(Neutral::Variable(x.to_owned()))),
        }
    }
}

fn sigma_induction(target: Value, motive: Closure<1>, pair: Closure<2>) -> Value {
    match target {
        Value::Pair(box a, box b) => pair.evaluate([a, b]),
        Value::Neutral(neutral) => Value::Neutral(Neutral::SigmaInduction {
            motive,
            pair,
            target: box neutral,
        }),
        _ => unreachable!(),
    }
}

fn natural_induction(
    target: Value,
    motive: Closure<1>,
    zero: Value,
    successor: Closure<2>,
) -> Value {
    match target {
        Value::Zero => zero,
        Value::Successor(box n) => successor
            .clone()
            .evaluate([n.clone(), natural_induction(n, motive, zero, successor)]),
        Value::Neutral(neutral) => Value::Neutral(Neutral::NaturalInduction {
            target: box neutral,
            motive,
            zero: box zero,
            successor,
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
