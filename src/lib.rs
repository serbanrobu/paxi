use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
};

use color_eyre::{
    eyre::{eyre, ContextCompat},
    Report, Result,
};
use nom::{combinator::eof, error::Error, sequence::terminated, Finish};

mod parser;

type Level = u8;

type Lift = u8;

type Identifier = String;

type Type = Value;

type Context = Vec<(Identifier, Type)>;

#[derive(Clone, Debug)]
pub enum Inferable {
    Application {
        function: Box<Inferable>,
        argument: Box<Checkable>,
    },
    Lift(Box<Inferable>),
    Variable(Identifier),
}

impl Inferable {
    fn alpha_eq(
        &self,
        other: &Self,
        index: usize,
        context: &HashMap<Identifier, usize>,
        context_: &HashMap<Identifier, usize>,
    ) -> bool {
        match (self, other) {
            (
                Self::Application {
                    function: f,
                    argument: a,
                },
                Self::Application {
                    function: f_,
                    argument: a_,
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

    fn infer(&self, context: &Context) -> Result<Type> {
        match self {
            Self::Application { function, argument } => {
                let t = function.infer(context)?;

                let Type::Function(ref a, b) = t else {
                    return Err(eyre!("illegal application"));
                };

                argument.check(a, context)?;

                Ok(*b)
            }
            Self::Lift(inferable) => {
                let t = inferable.infer(context)?;

                let Type::Universe(i) = t else {
                    return Err(eyre!("illegal lifting"));
                };

                Ok(Type::Universe(i + 1))
            }
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

    fn evaluate(&self, environment: &Environment, lift: Lift) -> Value {
        match self {
            Self::Application { function, argument } => {
                match function.evaluate(environment, lift) {
                    Value::Lambda(Closure {
                        environment: mut env,
                        lift,
                        identifier: x,
                        body,
                    }) => {
                        env.push((x, argument.evaluate(environment, lift)));
                        body.evaluate(&env, lift)
                    }
                    Value::Neutral(neutral) => Value::Neutral(Neutral::Application {
                        function: neutral.into(),
                        argument: argument.evaluate(environment, lift).into(),
                    }),
                    _ => unreachable!(),
                }
            }
            Self::Lift(inferable) => inferable.evaluate(environment, lift + 1),
            Self::Variable(x) => environment
                .iter()
                .rev()
                .find_map(|(y, v)| {
                    if x == y {
                        return Some(v.to_owned());
                    }

                    None
                })
                .unwrap_or_else(|| Value::Neutral(Neutral::Variable(lift, x.to_owned()))),
        }
    }
}

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
    fn reduce(&self, environment: &Environment, lift: Lift) -> Checkable {
        let ctx: HashSet<Identifier> = environment.iter().map(|(x, _)| x).cloned().collect();

        self.evaluate(environment, lift).quote(&ctx)
    }

    fn convert(&self, other: &Self, environment: &Environment, lift: Lift) -> bool {
        let ctx: HashSet<Identifier> = environment.iter().map(|(x, _)| x).cloned().collect();

        self.evaluate(environment, lift)
            .convert(&other.evaluate(environment, lift), &ctx)
    }

    fn alpha_eq(&self, other: &Self) -> bool {
        self.alpha_eq_(other, 0, &HashMap::new(), &HashMap::new())
    }

    fn alpha_eq_(
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

    fn check(&self, t: &Type, context: &Context) -> Result<()> {
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
                ctx.push((x.to_owned(), a.as_ref().to_owned()));
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
                ctx.push((x.to_owned(), a.as_ref().to_owned()));

                body.check(&b, &ctx)
            }
            (Self::Lift(checkable), &Type::Universe(i @ 1..)) => {
                checkable.check(&Type::Universe(i - 1), context)
            }
            (Self::Pi(x, a, body), Type::Universe(_i)) => {
                a.check(t, context)?;

                let mut ctx = context.to_owned();
                ctx.push((x.to_owned(), a.evaluate(&vec![], 0)));

                body.check(t, &ctx)
            }
            (&Self::Universe(i), &Type::Universe(j)) if i < j => Ok(()),
            _ => Err(eyre!("type mismatch")),
        }
    }

    fn evaluate(&self, environment: &Environment, lift: Lift) -> Value {
        match self {
            Self::Function(a, b) => Value::Function(
                a.evaluate(environment, lift).into(),
                b.evaluate(environment, lift).into(),
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
            Self::Lift(checkable) => checkable.evaluate(environment, lift + 1),
            Self::Pi(x, a, body) => Value::Pi(
                a.evaluate(environment, lift).into(),
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

#[derive(Clone, Debug)]
enum Neutral {
    Application {
        function: Box<Neutral>,
        argument: Box<Value>,
    },
    Variable(Lift, Identifier),
}

impl Neutral {
    fn quote(&self, context: &HashSet<Identifier>) -> Inferable {
        match self {
            Self::Application { function, argument } => Inferable::Application {
                function: function.quote(context).into(),
                argument: argument.quote(context).into(),
            },
            Self::Variable(lift, x) => (0..*lift)
                .fold(Inferable::Variable(x.to_owned()), |a, _| {
                    Inferable::Lift(a.into())
                }),
        }
    }
}

#[derive(Clone, Debug)]
enum Value {
    Lambda(Closure),
    Function(Box<Value>, Box<Value>),
    Neutral(Neutral),
    Pi(Box<Value>, Closure),
    Universe(Level),
}

impl Value {
    fn convert(&self, other: &Self, context: &HashSet<Identifier>) -> bool {
        self.quote(context).alpha_eq(&other.quote(context))
    }

    fn quote(&self, context: &HashSet<Identifier>) -> Checkable {
        match self {
            Self::Lambda(closure) => {
                let (x, body) = closure.quote(context);

                if let Checkable::Inferable(Inferable::Application { function, argument }) = &body {
                    if let Checkable::Inferable(Inferable::Variable(y)) = argument.as_ref() {
                        if x == *y {
                            return Checkable::Inferable(function.as_ref().to_owned());
                        }
                    }
                }

                Checkable::Lambda {
                    identifier: x,
                    body: body.into(),
                }
            }
            Self::Function(a, b) => {
                Checkable::Function(a.quote(context).into(), b.quote(context).into())
            }
            Self::Neutral(neutral) => Checkable::Inferable(neutral.quote(context)),
            Self::Pi(a, closure) => {
                let (identifier, body) = closure.quote(context);
                Checkable::Pi(identifier, a.quote(context).into(), body.into())
            }
            &Self::Universe(i) => Checkable::Universe(i),
        }
    }
}

type Environment = Vec<(Identifier, Value)>;

#[derive(Clone, Debug)]
struct Closure {
    environment: Environment,
    lift: Lift,
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
        self.body.to_owned().evaluate(&env, self.lift)
    }

    fn quote(&self, context: &HashSet<Identifier>) -> (Identifier, Checkable) {
        let x = freshen(&self.identifier, context);
        let body = self.apply(Value::Neutral(Neutral::Variable(0, x.clone())));
        let mut ctx = context.to_owned();
        ctx.insert(x.clone());

        (x, body.quote(&ctx))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check() -> Result<()> {
        let mut env = vec![];

        let mut ctx = vec![];

        ctx.push((
            "Void".to_owned(),
            "U(0)".parse::<Checkable>()?.evaluate(&env, 0),
        ));

        ctx.push((
            "Not".to_owned(),
            "U(0) →  U(0)".parse::<Checkable>()?.evaluate(&env, 0),
        ));

        env.push((
            "Not".to_owned(),
            "λ A. A →  Void".parse::<Checkable>()?.evaluate(&env, 0),
        ));

        let samples = [
            ("λ _A. λ a. a", "Π (A : U(0)). ↑(A →  A)", 1),
            (
                "λ _A. λ _B. λ a. λ _b. a",
                "Π (A : U(0)). Π (B : U(0)). ↑(A →  B →  A)",
                1,
            ),
            ("U(1) →  U(2)", "U(3)", 4),
            ("U(0)", "U(100)", 101),
            (
                "λ _P. λ _Q. λ pq. λ nq. λ p. nq(pq(p))",
                "Π (P : U(0)). Π (Q : U(0)). ↑((P →  Q) →  Not(Q) →  Not(P))",
                1,
            ),
        ];

        for (a, t, i) in samples {
            let t: Checkable = t.parse()?;
            let a: Checkable = a.parse()?;

            t.check(&Type::Universe(i), &ctx)?;
            a.check(&t.evaluate(&env, 0), &ctx)?;
        }

        Ok(())
    }

    #[test]
    fn alpha_eq() -> Result<()> {
        let samples = [("λ x. f(x)", "λ y. f(y)")];

        for (a, b) in samples {
            let a: Checkable = a.parse()?;
            let b: Checkable = b.parse()?;

            assert!(a.alpha_eq(&b));
        }

        Ok(())
    }

    #[test]
    fn convert() -> Result<()> {
        let mut env: Environment = vec![];

        let id: Checkable = "λ x. x".parse()?;
        env.push(("id".to_owned(), id.evaluate(&env, 0)));

        let samples = [
            ("λ x. id(x)", "λ y. y"),
            ("λ x. f(x)", "f"),
            ("↑A(B)", "(↑A)(↑B)"),
            ("(A →  B) →  (C →  D)", "(A →  B) →  C →  D"),
        ];

        for (a, b) in samples {
            let a: Checkable = a.parse()?;
            let b: Checkable = b.parse()?;

            assert!(a.convert(&b, &env, 0));
        }

        Ok(())
    }
}
