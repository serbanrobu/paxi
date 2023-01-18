use im_rc::HashSet;

use crate::{checkable::Checkable, inferable::Inferable, Binding, Environment, Identifier, Level};

#[derive(Clone, Debug)]
pub enum Neutral {
    Application {
        operator: Box<Neutral>,
        operand: Box<Value>,
    },
    NaturalInduction {
        motive: Box<Binding<Value>>,
        base: Box<Value>,
        step: Box<Binding<Binding<Value>>>,
        target: Box<Neutral>,
    },
    Variable(Identifier),
}

impl Neutral {
    fn quote(&self, context: &HashSet<Identifier>) -> Inferable {
        match self {
            Self::Application { operator, operand } => Inferable::Application {
                operator: box operator.quote(context),
                operand: box operand.quote(context),
            },
            Self::NaturalInduction {
                motive: box Binding(x, motive_),
                base,
                step: box Binding(y, Binding(z, step_)),
                target,
            } => Inferable::NaturalInduction {
                motive: box Binding(x.to_owned(), motive_.quote(context)),
                base: box base.quote(context),
                step: box Binding(y.to_owned(), Binding(z.to_owned(), step_.quote(context))),
                target: box Checkable::Inferable(target.quote(context)),
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
    Universe(Level),
    Zero,
}

impl Value {
    pub fn apply(&self, operand: Value) -> Value {
        match self {
            Self::Lambda(closure) => closure.apply(operand),
            Self::Neutral(neutral) => Value::Neutral(Neutral::Application {
                operator: box neutral.to_owned(),
                operand: box operand,
            }),
            _ => unreachable!(),
        }
    }

    pub fn convert(&self, other: &Self, context: &HashSet<Identifier>) -> bool {
        self.quote(context).alpha_eq(&other.quote(context))
    }

    pub fn quote(&self, context: &HashSet<Identifier>) -> Checkable {
        match self {
            Self::Lambda(closure) => {
                let (x, body) = closure.quote(context);

                if let Checkable::Inferable(Inferable::Application {
                    box operator,
                    operand: box Checkable::Inferable(Inferable::Variable(y)),
                }) = &body && x == *y
                {
                    return Checkable::Inferable(operator.to_owned());
                }

                Checkable::Lambda {
                    identifier: x,
                    body: box body,
                }
            }
            Self::Function(a, b) => Checkable::Function(box a.quote(context), box b.quote(context)),
            Self::Natural => Checkable::Natural,
            Self::Neutral(neutral) => Checkable::Inferable(neutral.quote(context)),
            Self::Pi(a, closure) => {
                let (x, body) = closure.quote(context);
                Checkable::Pi(box a.quote(context), box Binding(x, body))
            }
            Self::Successor(n) => Checkable::Successor(box n.quote(context)),
            &Self::Universe(i) => Checkable::Universe(i),
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
