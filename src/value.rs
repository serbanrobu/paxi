use im_rc::HashSet;

use crate::{checkable::Checkable, inferable::Inferable, Environment, Identifier, Level, Lift};

#[derive(Clone, Debug)]
pub enum Neutral {
    Application {
        operator: Box<Neutral>,
        operand: Box<Value>,
    },
    Variable(Lift, Identifier),
}

impl Neutral {
    fn quote(&self, context: &HashSet<Identifier>) -> Inferable {
        match self {
            Self::Application { operator, operand } => Inferable::Application {
                operator: operator.quote(context).into(),
                operand: operand.quote(context).into(),
            },
            Self::Variable(lift, x) => (0..*lift)
                .fold(Inferable::Variable(x.to_owned()), |a, _| {
                    Inferable::Lift(a.into())
                }),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Lambda(Closure),
    Function(Box<Value>, Box<Value>),
    Neutral(Neutral),
    Pi(Box<Value>, Closure),
    Universe(Level),
}

impl Value {
    pub fn convert(&self, other: &Self, context: &HashSet<Identifier>) -> bool {
        self.quote(context).alpha_eq(&other.quote(context))
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
            Self::Neutral(neutral) => Checkable::Inferable(neutral.quote(context)),
            Self::Pi(a, closure) => {
                let (identifier, body) = closure.quote(context);
                Checkable::Pi(identifier, a.quote(context).into(), body.into())
            }
            &Self::Universe(i) => Checkable::Universe(i),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Closure {
    pub environment: Environment,
    pub lift: Lift,
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
        self.body.to_owned().evaluate_(&env, self.lift)
    }

    fn quote(&self, context: &HashSet<Identifier>) -> (Identifier, Checkable) {
        let x = freshen(&self.identifier, context);
        let body = self.apply(Value::Neutral(Neutral::Variable(0, x.clone())));
        let mut ctx = context.to_owned();
        ctx.insert(x.clone());

        (x, body.quote(&ctx))
    }
}
