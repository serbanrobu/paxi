#![feature(box_patterns, box_syntax, let_chains)]

pub mod checkable;
pub mod inferable;
pub mod parser;
pub mod value;

use im_rc::HashMap;
use value::Value;

pub type Level = u8;

pub type Identifier = String;

pub type Type = Value;

pub type Context = HashMap<Identifier, Type>;

pub type Environment = HashMap<Identifier, Value>;

#[derive(Debug, Clone)]
pub struct Binding<T>(Identifier, T);

impl<T> From<(Identifier, T)> for Binding<T> {
    fn from((x, t): (Identifier, T)) -> Self {
        Binding(x, t)
    }
}
