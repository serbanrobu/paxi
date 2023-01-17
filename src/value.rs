use im_rc::HashSet;

use crate::{checkable::Checkable, inferable::Inferable, Environment, Identifier};

#[derive(Clone, Debug)]
pub enum Neutral {
    Application {
        operator: Box<Neutral>,
        operand: Box<Value>,
    },
    NaturalInduction {
        x: Identifier,
        motive: Box<Value>,
        base: Box<Value>,
        y: Identifier,
        z: Identifier,
        step: Box<Value>,
        target: Box<Neutral>,
    },
    Variable(Identifier),
}

impl Neutral {
    fn quote(&self, context: &HashSet<Identifier>) -> Inferable {
        match self {
            Self::Application { operator, operand } => Inferable::Application {
                operator: operator.quote(context).into(),
                operand: operand.quote(context).into(),
            },
            Self::NaturalInduction {
                x,
                motive,
                base,
                y,
                z,
                step,
                target,
            } => Inferable::NaturalInduction {
                x: x.to_owned(),
                motive: motive.quote(context).into(),
                base: base.quote(context).into(),
                y: y.to_owned(),
                z: z.to_owned(),
                step: step.quote(context).into(),
                target: Checkable::Inferable(target.quote(context)).into(),
            },
            Self::Variable(x) => Inferable::Variable(x.to_owned()),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Lambda(Closure),
    Function(Box<Value>, Box<Value>),
    Natural,
    Neutral(Neutral),
    Pi(Box<Value>, Closure),
    Successor(Box<Value>),
    Universe(Box<Value>),
    Zero,
}

impl Value {
    pub fn apply(&self, operand: Value) -> Value {
        match self {
            Self::Lambda(closure) => closure.apply(operand),
            Self::Neutral(neutral) => Value::Neutral(Neutral::Application {
                operator: neutral.to_owned().into(),
                operand: operand.into(),
            }),
            _ => unreachable!(),
        }
    }

    pub fn convert(&self, other: &Self, context: &HashSet<Identifier>) -> bool {
        self.quote(context).alpha_eq(&other.quote(context))
    }

    pub fn lt(&self, other: &Value, context: &HashSet<Identifier>) -> bool {
        let Value::Successor(other) = other else {
            return false;
        };

        self.lte(other, context)
    }

    pub fn lte(&self, other: &Value, context: &HashSet<Identifier>) -> bool {
        match (self, other) {
            (Value::Zero, Value::Successor(_b)) => true,
            (Value::Successor(a), Value::Successor(b)) => a.lte(b, context),
            (a, b) => a.convert(b, context),
        }
    }

    pub fn quote(&self, context: &HashSet<Identifier>) -> Checkable {
        match self {
            Self::Lambda(closure) => {
                let (x, body) = closure.quote(context);

                if let Checkable::Inferable(Inferable::Application { operator, operand }) = &body {
                    if let Checkable::Inferable(Inferable::Variable(y)) = operand.as_ref() {
                        if x == *y {
                            return Checkable::Inferable(operator.as_ref().to_owned());
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
            Self::Natural => Checkable::Natural,
            Self::Neutral(neutral) => Checkable::Inferable(neutral.quote(context)),
            Self::Pi(a, closure) => {
                let (identifier, body) = closure.quote(context);
                Checkable::Pi(identifier, a.quote(context).into(), body.into())
            }
            Self::Successor(n) => Checkable::Successor(n.quote(context).into()),
            Self::Universe(i) => Checkable::Universe(i.quote(context).into()),
            Self::Zero => Checkable::Zero,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Closure {
    pub environment: Environment,
    pub identifier: Identifier,
    pub body: Checkable,
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
    pub fn apply(&self, operand: Value) -> Value {
        let mut env = self.environment.to_owned();
        env.insert(self.identifier.to_owned(), operand);
        self.body.to_owned().evaluate(&env)
    }

    fn quote(&self, context: &HashSet<Identifier>) -> (Identifier, Checkable) {
        let x = freshen(&self.identifier, context);
        let body = self.apply(Value::Neutral(Neutral::Variable(x.clone())));
        let mut ctx = context.to_owned();
        ctx.insert(x.clone());

        (x, body.quote(&ctx))
    }
}
