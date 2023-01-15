pub mod checkable;
pub mod inferable;
pub mod parser;
pub mod value;

use im_rc::HashMap;
use value::Value;

pub type Identifier = String;

pub type Type = Value;

pub type Context = HashMap<Identifier, Type>;

pub type Environment = HashMap<Identifier, Value>;
