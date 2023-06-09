use std::str::FromStr;

use color_eyre::Result;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, multispace1},
    combinator::{eof, map, opt, value},
    error::Error,
    sequence::{pair, preceded, terminated},
    Finish, IResult,
};
use pax::{
    parser::{parse_checkable, parse_inferable},
    Checkable, Context, Env, Inferable, Name, Type, Value,
};
use rustyline::{config::Configurer, error::ReadlineError, DefaultEditor};

fn main() -> Result<()> {
    let mut rl = DefaultEditor::new()?;
    rl.set_edit_mode(rustyline::EditMode::Vi);

    let mut ctx = Context::new();
    let mut env = vec![];

    loop {
        match rl.readline(">> ") {
            Ok(line) => {
                rl.add_history_entry(&line)?;

                match handle(&line, &mut ctx, &mut env) {
                    Ok(false) => break,
                    Ok(true) => {}
                    Err(err) => eprintln!("{err}"),
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                eprintln!("Error: {err}");
                break;
            }
        }
    }

    Ok(())
}

#[derive(Clone)]
enum Command {
    Eval(Inferable),
    Exec(Checkable),
    Quit,
}

fn handle(line: &str, ctx: &mut Context, env: &mut Env) -> Result<bool> {
    let cmd = Command::from_str(&line)?;

    match cmd {
        Command::Exec(checkable) => {
            checkable.check(&Type::Io(Box::new(Type::Trivial)), ctx, 0)?;

            let value = checkable.eval(env);

            match value {
                Value::Let(x, v_1, _v_2) => {
                    ctx.insert(Name::Global(x), *v_1);
                    // TODO: insert in env
                }
                _ => {}
            }

            Ok(true)
        }
        Command::Eval(inferable) => {
            let ty = inferable.infer(ctx, 0)?;

            let val = inferable.eval(env);
            println!("{} : {}", val.quote(0), ty.quote(0));
            Ok(true)
        }
        Command::Quit => Ok(false),
    }
}

fn parse_command(input: &str) -> IResult<&str, Command> {
    alt((
        preceded(
            char(':'),
            alt((
                map(
                    preceded(pair(tag("exec"), multispace1), parse_checkable),
                    Command::Exec,
                ),
                value(Command::Quit, pair(char('q'), opt(tag("uit")))),
            )),
        ),
        map(parse_inferable, Command::Eval),
    ))(input)
}

impl FromStr for Command {
    type Err = Error<String>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (_remaining, cmd) = terminated(parse_command, eof)(s.trim())
            .finish()
            .map_err(|e| Error::new(e.input.to_owned(), e.code))?;

        Ok(cmd)
    }
}
