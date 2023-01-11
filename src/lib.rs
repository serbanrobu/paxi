use std::{collections::HashSet, str::FromStr};

use color_eyre::{
    eyre::{eyre, ContextCompat},
    Report, Result,
};
use nom::{combinator::eof, error::Error, sequence::terminated, Finish};

mod parser;

type Level = u8;

#[derive(Clone, PartialEq)]
enum Type {
    Universe(Level),
    Function(Box<Type>, Box<Type>),
}

type Identifier = String;

type Context = Vec<(Identifier, Type)>;

#[derive(Clone, Debug)]
pub enum Inferable {
    Application {
        function: Box<Inferable>,
        argument: Box<Checkable>,
    },
    Variable(Identifier),
}

impl Inferable {
    fn infer(&self, context: &Context) -> Result<Type> {
        match self {
            Self::Application { function, argument } => match function.infer(context)? {
                Type::Function(ref a, b) => {
                    argument.check(a, context)?;
                    Ok(*b)
                }
                _ => Err(eyre!("illegal application")),
            },
            Self::Variable(x) => context
                .iter()
                .rev()
                .find_map(|(y, t)| {
                    if x == y {
                        return Some(t.to_owned());
                    }

                    None
                })
                .wrap_err("unknown identifier"),
        }
    }

    fn evaluate(&self, environment: &Environment) -> Value {
        match self {
            Self::Application { function, argument } => match function.evaluate(environment) {
                Value::Closure(Closure {
                    environment: mut env,
                    identifier: x,
                    body,
                }) => {
                    env.push((x, argument.evaluate(environment)));
                    body.evaluate(&env)
                }
                Value::Neutral(neutral) => Value::Neutral(Neutral::Application {
                    function: neutral.into(),
                    argument: argument.evaluate(environment).into(),
                }),
            },
            Self::Variable(x) => environment
                .iter()
                .rev()
                .find_map(|(y, v)| {
                    if x == y {
                        return Some(v.to_owned());
                    }

                    None
                })
                .unwrap_or_else(|| Value::Neutral(Neutral::Variable(x.to_owned()))),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Checkable {
    Inferable(Inferable),
    Lambda {
        identifier: Identifier,
        body: Box<Checkable>,
    },
}

impl Checkable {
    fn check(&self, t: &Type, context: &Context) -> Result<()> {
        match (self, t) {
            (Self::Inferable(inferable), _) => {
                let t_ = inferable.infer(context)?;

                if *t != t_ {
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
                ctx.push((x.to_owned(), a.as_ref().to_owned()));
                body.check(b, &ctx)
            }
            _ => Err(eyre!("type mismatch")),
        }
    }

    fn evaluate(&self, environment: &Environment) -> Value {
        match self {
            Self::Inferable(inferable) => inferable.evaluate(environment),
            Self::Lambda {
                identifier: x,
                body,
            } => Value::Closure(Closure {
                environment: environment.to_owned(),
                identifier: x.to_owned(),
                body: body.as_ref().to_owned(),
            }),
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

#[derive(Clone)]
enum Neutral {
    Application {
        function: Box<Neutral>,
        argument: Box<Value>,
    },
    Variable(Identifier),
}

impl Neutral {
    fn quote(&self, context: &HashSet<Identifier>) -> Inferable {
        match self {
            Self::Application { function, argument } => Inferable::Application {
                function: function.quote(context).into(),
                argument: argument.quote(context).into(),
            },
            Self::Variable(x) => Inferable::Variable(x.to_owned()),
        }
    }
}

#[derive(Clone)]
enum Value {
    Closure(Closure),
    Neutral(Neutral),
}

impl Value {
    fn quote(&self, context: &HashSet<Identifier>) -> Checkable {
        match self {
            Self::Closure(closure) => closure.quote(context),
            Self::Neutral(neutral) => Checkable::Inferable(neutral.quote(context)),
        }
    }
}

type Environment = Vec<(Identifier, Value)>;

#[derive(Clone)]
struct Closure {
    environment: Environment,
    identifier: Identifier,
    body: Checkable,
}

fn freshen(identifier: &Identifier, context: &HashSet<Identifier>) -> Identifier {
    let mut x = identifier.to_owned();

    if context.contains(&x) {
        x.push('\'');
        return freshen(&x, context);
    }

    x
}

impl Closure {
    fn apply(&self, argument: Value) -> Value {
        let mut env = self.environment.to_owned();
        env.push((self.identifier.to_owned(), argument));
        self.body.to_owned().evaluate(&env)
    }

    fn quote(&self, context: &HashSet<Identifier>) -> Checkable {
        let x = freshen(&self.identifier, context);
        let body = self.apply(Value::Neutral(Neutral::Variable(x.clone())));
        let mut ctx = context.to_owned();
        ctx.insert(x.clone());

        Checkable::Lambda {
            identifier: x,
            body: body.quote(&ctx).into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_id() -> Result<()> {
        let id: Checkable = "λ x. x".parse()?;

        id.check(
            &Type::Function(Type::Universe(0).into(), Type::Universe(0).into()),
            &vec![],
        )?;

        dbg!(&id);

        Ok(())
    }
}
