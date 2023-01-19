use im_rc::HashSet;

use crate::{checkable::Checkable, inferable::Inferable, Binding, Environment, Identifier, Level};

#[derive(Clone, Debug)]
pub enum Neutral {
    Application {
        operator: Box<Neutral>,
        operand: Box<Value>,
    },
    NaturalInduction {
        target: Box<Neutral>,
        motive: Closure<1>,
        zero: Box<Value>,
        successor: Closure<2>,
    },
    SigmaInduction {
        target: Box<Neutral>,
        motive: Closure<1>,
        pair: Closure<2>,
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
                motive,
                zero: base,
                successor: step,
                target,
            } => Inferable::NaturalInduction {
                motive: box motive.quote(context),
                zero: box base.quote(context),
                successor: box step.quote(context),
                target: box target.quote(context),
            },
            Self::SigmaInduction {
                motive,
                pair: make,
                target,
            } => Inferable::SigmaInduction {
                motive: box motive.quote(context),
                pair: box make.quote(context),
                target: box target.quote(context),
            },
            Self::Variable(x) => Inferable::Variable(x.to_owned()),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Lambda(Closure<1>),
    Function(Box<Value>, Box<Value>),
    Natural,
    Neutral(Neutral),
    Pair(Box<Value>, Box<Value>),
    Pi(Box<Value>, Closure<1>),
    Product(Box<Value>, Box<Value>),
    Sigma(Box<Value>, Closure<1>),
    Successor(Box<Value>),
    Universe(Level),
    Zero,
}

impl Value {
    pub fn apply(&self, operand: Value) -> Value {
        match self {
            Self::Lambda(closure) => closure.evaluate([operand]),
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
                let Binding([x], body) = closure.quote(context);

                if let Checkable::Inferable(Inferable::Application {
                    box operator,
                    operand: box Checkable::Inferable(Inferable::Variable(y)),
                }) = &body && x == *y
                {
                    return Checkable::Inferable(operator.to_owned());
                }

                Checkable::Lambda(box Binding([x], body))
            }
            Self::Function(a, b) => Checkable::Function(box a.quote(context), box b.quote(context)),
            Self::Natural => Checkable::Natural,
            Self::Neutral(neutral) => Checkable::Inferable(neutral.quote(context)),
            Self::Pair(a, b) => Checkable::Pair(box a.quote(context), box b.quote(context)),
            Self::Pi(a, closure) => Checkable::Pi(box a.quote(context), box closure.quote(context)),
            Self::Product(a, b) => Checkable::Product(box a.quote(context), box b.quote(context)),
            Self::Sigma(a, closure) => {
                Checkable::Sigma(box a.quote(context), box closure.quote(context))
            }
            Self::Successor(n) => Checkable::Successor(box n.quote(context)),
            &Self::Universe(i) => Checkable::Universe(i),
            Self::Zero => Checkable::Zero,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Closure<const N: usize> {
    pub environment: Environment,
    pub binding: Binding<N>,
}

fn freshen(identifier: &Identifier, context: &HashSet<Identifier>) -> Identifier {
    let mut x = identifier.to_owned();

    if context.contains(&x) {
        x.push('\'');
        return freshen(&x, context);
    }

    x
}

impl<const N: usize> Closure<N> {
    pub fn evaluate(&self, arguments: [Value; N]) -> Value {
        let Binding(xs, body) = &self.binding;
        let mut env = self.environment.to_owned();

        for i in 0..N {
            env.insert(xs[i].to_owned(), arguments[i].clone());
        }

        body.to_owned().evaluate(&env)
    }

    fn quote(&self, context: &HashSet<Identifier>) -> Binding<N> {
        let Binding(xs, _body) = &self.binding;
        let ys = xs.to_owned().map(|x| freshen(&x, context));

        let mut ctx = context.to_owned();
        ctx.extend(&ys);

        let body = self.evaluate(ys.clone().map(|y| Value::Neutral(Neutral::Variable(y))));
        Binding(ys, body.quote(&ctx))
    }
}
