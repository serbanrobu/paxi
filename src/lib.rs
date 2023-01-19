#![feature(box_patterns, box_syntax, let_chains)]

pub mod checkable;
pub mod inferable;
pub mod parser;
pub mod value;

use checkable::Checkable;
use im_rc::HashMap;
use value::Value;

pub type Level = u8;

pub type Identifier = String;

pub type Type = Value;

pub type Context = HashMap<Identifier, Type>;

pub type Environment = HashMap<Identifier, Value>;

#[derive(Debug, Clone)]
pub struct Binding<const N: usize>([Identifier; N], Checkable);
