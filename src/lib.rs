pub mod parser;

use std::{collections::HashMap, fmt};

use color_eyre::{
    eyre::{eyre, ContextCompat},
    Result,
};

pub type Level = u8;

pub type Type = Value;

pub type Context = HashMap<Name, Type>;

pub type Env = [Value];

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Name {
    Global(String),
    Local(usize),
    Quote(usize),
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Global(x) => x.fmt(f),
            _ => panic!(),
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum Inferable {
    Ann(Box<Checkable>, Box<Checkable>),
    App(Box<Inferable>, Box<Checkable>),
    Bound(usize),
    Free(Name),
}

impl Inferable {
    fn bound_free(i: usize, x: Name) -> Self {
        match x {
            Name::Quote(k) => Self::Bound(i - k - 1),
            _ => Self::Free(x),
        }
    }

    pub fn eval(&self, d: &Env) -> Value {
        match self {
            Self::Ann(e, _) => e.eval(d),
            Self::App(e_1, e_2) => e_1.eval(d).app(e_2.eval(d)),
            &Self::Bound(i) => d[d.len() - 1 - i].clone(),
            Self::Free(x) => Value::free(x.to_owned()),
        }
    }

    pub fn infer(&self, cx: &Context, i: usize) -> Result<Type> {
        match self {
            Self::Ann(e_1, e_2) => {
                e_1.check(&Type::U(Level::MAX), cx, i)?;
                let t = e_1.eval(&[]);
                e_2.check(&t, cx, i)?;
                Ok(t)
            }
            &Self::Bound(_i) => todo!(),
            Self::Free(x) => cx.get(x).cloned().wrap_err("unknown identifier"),
            Self::App(e_1, e_2) => {
                let t = e_1.infer(cx, i)?;

                let Type::Fun(t_1, t_2) = t else {
                    return Err(eyre!("illegal application"));
                };

                e_2.check(&t_1, cx, i)?;
                Ok(*t_2)
            }
        }
    }

    pub fn substitute(&self, r: &Self, i: usize) -> Self {
        match self {
            Self::Ann(e, t) => Self::Ann(Box::new(e.substitute(r, i)), t.to_owned()),
            &Self::Bound(j) => {
                if i == j {
                    r.to_owned()
                } else {
                    Self::Bound(j)
                }
            }
            Self::Free(_) => self.to_owned(),
            Self::App(e_1, e_2) => Self::App(
                Box::new(e_1.substitute(r, i)),
                Box::new(e_2.substitute(r, i)),
            ),
        }
    }
}

impl fmt::Display for Inferable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ann(e_1, e_2) => write!(f, "{e_1} : {e_2}"),
            &Self::Bound(i) => write!(f, "${i}"),
            Self::Free(x) => x.fmt(f),
            Self::App(e_1, e_2) => write!(f, "({e_1})({e_2})"),
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum Checkable {
    Char,
    CharLit(char),
    Cons(Box<Checkable>, Box<Checkable>),
    Fin(Box<Checkable>),
    Fun(Box<Checkable>, Box<Checkable>),
    Inferable(Inferable),
    Lam(Box<Checkable>),
    Let(String, Box<Checkable>, Box<Checkable>),
    List(Box<Checkable>),
    Nil,
    Sole,
    String,
    StringLit(String),
    Trivial,
    U(Level),
    Usize,
    UsizeLit(usize),
    Vec(Box<Checkable>, Box<Checkable>),
}

impl Checkable {
    pub fn check(&self, t: &Type, cx: &Context, i: usize) -> Result<()> {
        match (self, t) {
            (Self::Char, Type::U(_)) => Ok(()),
            (Self::CharLit(_), Type::Char) => Ok(()),
            (Self::Cons(e_1, e_2), Type::List(v)) => {
                e_1.check(v, cx, i)?;
                e_2.check(t, cx, i)
            }
            (Self::Cons(e_1, e_2), Type::Vec(v_1, v_2)) => {
                let &Value::UsizeLit(u) = v_1.as_ref() else {
                    return Err(eyre!("type mismatch"));
                };

                if u == 0 {
                    return Err(eyre!("type mismatch"));
                }

                e_1.check(v_2, cx, i)?;

                e_2.check(
                    &Type::Vec(Box::new(Value::UsizeLit(u - 1)), v_2.to_owned()),
                    cx,
                    i,
                )
            }
            (Self::Fin(e), Type::U(_)) => e.check(&Type::Usize, cx, i),
            (Self::Fun(e_1, e_2), Type::U(_)) => {
                e_1.check(t, cx, i)?;
                e_2.check(t, cx, i)
            }
            (Self::Inferable(inferable), _) => {
                let t_1 = inferable.infer(cx, i)?;

                if t_1.quote(0) != t.quote(0) {
                    return Err(eyre!("type mismatch"));
                }

                Ok(())
            }
            (Self::Lam(e), Type::Fun(v_1, v_2)) => {
                let mut cx_1 = cx.to_owned();
                cx_1.insert(Name::Local(i), v_1.as_ref().to_owned());

                e.substitute(&Inferable::Free(Name::Local(i)), 0)
                    .check(v_2, &cx_1, i + 1)
            }
            (Self::List(e), Type::U(_)) => e.check(t, cx, i),
            (Self::Nil, Type::List(_)) => Ok(()),
            (Self::Nil, Type::Vec(t, _)) => {
                let Value::UsizeLit(0) = t.as_ref() else {
                    return Err(eyre!("type mismatch"));
                };

                Ok(())
            }
            (Self::Sole, Type::Trivial) => Ok(()),
            (Self::String, Type::U(_)) => Ok(()),
            (Self::StringLit(_), Type::String) => Ok(()),
            (Self::Trivial, Type::U(_)) => Ok(()),
            (Self::U(i), Type::U(j)) if i < j => Ok(()),
            (Self::Usize, Type::U(_)) => Ok(()),
            (Self::UsizeLit(_), Type::Usize) => Ok(()),
            (Self::Vec(e_1, e_2), Type::U(_)) => {
                e_1.check(&Type::Usize, cx, i)?;
                e_2.check(t, cx, i)
            }
            _ => Err(eyre!("type mismatch")),
        }
    }

    pub fn eval(&self, d: &Env) -> Value {
        match self {
            Self::Char => Value::Char,
            &Self::CharLit(c) => Value::CharLit(c),
            Self::Cons(e_1, e_2) => Value::Cons(Box::new(e_1.eval(d)), Box::new(e_2.eval(d))),
            Self::Fin(e) => Value::Fin(Box::new(e.eval(d))),
            Self::Fun(e_1, e_2) => Value::Fun(Box::new(e_1.eval(d)), Box::new(e_2.eval(d))),
            Self::Inferable(i) => i.eval(d),
            Self::Lam(e) => Value::Lam(d.to_owned(), e.as_ref().to_owned()),
            Self::Let(x, e_1, e_2) => todo!(),
            Self::List(e) => Value::List(Box::new(e.eval(d))),
            Self::Nil => Value::Nil,
            Self::Sole => Value::Sole,
            Self::String => Value::String,
            Self::StringLit(s) => Value::StringLit(s.to_owned()),
            Self::Trivial => Value::Trivial,
            &Self::U(i) => Value::U(i),
            Self::Usize => Value::Usize,
            &Self::UsizeLit(u) => Value::UsizeLit(u),
            Self::Vec(e_1, e_2) => Value::Vec(Box::new(e_1.eval(d)), Box::new(e_2.eval(d))),
        }
    }

    fn substitute(&self, r: &Inferable, i: usize) -> Self {
        match self {
            Self::Char => Self::Char,
            &Self::CharLit(c) => Self::CharLit(c),
            Self::Cons(e_1, e_2) => Self::Cons(
                Box::new(e_1.substitute(r, i)),
                Box::new(e_2.substitute(r, i)),
            ),
            Self::Fin(e) => Self::Fin(Box::new(e.substitute(r, i))),
            Self::Fun(e_1, e_2) => Self::Fun(
                Box::new(e_1.substitute(r, i)),
                Box::new(e_2.substitute(r, i)),
            ),
            Self::Inferable(e) => Self::Inferable(e.substitute(r, i)),
            Self::Lam(e) => Self::Lam(Box::new(e.substitute(r, i + 1))),
            Self::Let(x, e_1, e_2) => Self::Let(
                x.to_owned(),
                Box::new(e_1.substitute(r, i)),
                Box::new(e_2.substitute(r, i)),
            ),
            Self::List(e) => Self::List(Box::new(e.substitute(r, i))),
            Self::Nil => Self::Nil,
            Self::Sole => Self::Sole,
            Self::String => Self::String,
            Self::StringLit(s) => Self::StringLit(s.to_owned()),
            Self::Trivial => Self::Trivial,
            &Self::U(i) => Self::U(i),
            Self::Usize => Self::Usize,
            &Self::UsizeLit(u) => Self::UsizeLit(u),
            Self::Vec(e_1, e_2) => Self::Vec(
                Box::new(e_1.substitute(r, i)),
                Box::new(e_2.substitute(r, i)),
            ),
        }
    }
}

impl fmt::Display for Checkable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Char => "Char".fmt(f),
            Self::CharLit(c) => write!(f, "{c:?}"),
            Self::Cons(e_1, e_2) => write!(f, "cons({e_1}, {e_2})"),
            Self::Fin(e) => write!(f, "Fin({e})"),
            Self::Fun(e_1, e_2) => write!(f, "Fun({e_1}, {e_2})"),
            Self::Inferable(inferable) => inferable.fmt(f),
            Self::Lam(e) => write!(f, "lam({e})"),
            Self::Let(x, e_1, e_2) => write!(f, "let({x}, {e_1}, {e_2})"),
            Self::List(e) => write!(f, "List({e})"),
            Self::Nil => "nil".fmt(f),
            Self::Sole => "sole".fmt(f),
            Self::String => "String".fmt(f),
            Self::StringLit(s) => write!(f, "{s:?}"),
            Self::Trivial => "Trivial".fmt(f),
            Self::U(i) => write!(f, "U({i})"),
            Self::Usize => "Usize".fmt(f),
            Self::UsizeLit(u) => write!(f, "{u:?}"),
            Self::Vec(e_1, e_2) => write!(f, "Vec({e_1}, {e_2})"),
        }
    }
}

impl Value {
    pub fn quote(&self, i: usize) -> Checkable {
        match self {
            Self::Cons(v_1, v_2) => Checkable::Cons(Box::new(v_1.quote(i)), Box::new(v_2.quote(i))),
            Self::Char => Checkable::Char,
            &Self::CharLit(c) => Checkable::CharLit(c),
            Self::Fin(v) => Checkable::Fin(Box::new(v.quote(i))),
            Self::Fun(v_1, v_2) => Checkable::Fun(Box::new(v_1.quote(i)), Box::new(v_2.quote(i))),
            Self::Lam(d, e) => {
                let mut d = d.to_owned();
                d.push(Self::free(Name::Quote(i)));
                Checkable::Lam(Box::new(e.eval(&d).quote(i + 1)))
            }
            Self::List(v) => Checkable::List(Box::new(v.quote(i))),
            Self::Neutral(n) => Checkable::Inferable(n.quote(i)),
            Self::Nil => Checkable::Nil,
            Self::Sole => Checkable::Sole,
            Self::String => Checkable::String,
            Self::StringLit(s) => Checkable::StringLit(s.to_owned()),
            Self::Trivial => Checkable::Trivial,
            &Self::U(i) => Checkable::U(i),
            Self::Usize => Checkable::Usize,
            &Self::UsizeLit(u) => Checkable::UsizeLit(u),
            Self::Vec(v_1, v_2) => Checkable::Vec(Box::new(v_1.quote(i)), Box::new(v_2.quote(i))),
        }
    }
}

#[derive(Clone)]
pub enum Neutral {
    App(Box<Neutral>, Box<Value>),
    Free(Name),
}

impl Neutral {
    fn quote(&self, i: usize) -> Inferable {
        match self {
            Self::App(n, v) => Inferable::App(Box::new(n.quote(i)), Box::new(v.quote(i))),
            Self::Free(n) => Inferable::bound_free(i, n.to_owned()),
        }
    }
}

#[derive(Clone)]
pub enum Value {
    Char,
    CharLit(char),
    Cons(Box<Value>, Box<Value>),
    Fin(Box<Value>),
    Fun(Box<Value>, Box<Value>),
    Lam(<Env as ToOwned>::Owned, Checkable),
    List(Box<Value>),
    Neutral(Neutral),
    Nil,
    Sole,
    String,
    StringLit(String),
    Trivial,
    U(Level),
    Usize,
    UsizeLit(usize),
    Vec(Box<Value>, Box<Value>),
}

impl Value {
    pub fn app(self, v: Self) -> Self {
        match self {
            Self::Lam(mut d, e) => {
                d.push(v);
                e.eval(&d)
            }
            Self::Neutral(n) => Self::Neutral(Neutral::App(Box::new(n), Box::new(v))),
            _ => unreachable!(),
        }
    }

    fn free(n: Name) -> Self {
        Self::Neutral(Neutral::Free(n))
    }
}
