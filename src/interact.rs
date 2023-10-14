use anyhow::Result;
use rexpect::spawn;

use crate::project::{CoqProject, prepare_program};
use crate::lexer::{CoqTokenKind, CoqTokenSlice};

static COQ_REGEX: &str = "\r\n[^< ]+ < ";

pub fn run_file(project: &CoqProject, mut tokens : CoqTokenSlice) -> Result<()> {
    let mut process = spawn(&prepare_program(project), Some(1000))?;
    process.exp_regex(COQ_REGEX)?;

    let mut index: usize = 0;
    while !tokens.is_empty() {
        index += 1;
        if tokens[index - 1].kind == CoqTokenKind::Dot {
            let query = tokens.cut(index);
            process.send_line(&query.to_string())?;

            let (answer, _) = process.exp_regex(COQ_REGEX)?;
            print!("{}\n {}\n", query, answer);

            index = 0;
        }
    }

    Ok(())
}

#[test]
pub fn interact() -> Result<()> {
    let mut program = spawn("coqtop", Some(1000))?;
    let (out, _) = program.exp_regex("\r\n[^< ]+ < ")?;
    program.send_line("From Coq Require Import Classical. Section MinimalElements.")?;
    let (x, _) = program.exp_regex("\r\n[^< ]+ < ")?;
    Ok(())
}
