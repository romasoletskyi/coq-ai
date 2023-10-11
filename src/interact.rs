use std::io::BufRead;
use anyhow::Result;
use rexpect::spawn;

use crate::project::{CoqProject, prepare_program};

static COQ_REGEX: &str = "\r\n[^< ]+ < ";

pub fn run_file(project: &CoqProject, path: &str) -> Result<()> {
    let file = std::fs::File::open(path)?;
    let reader = std::io::BufReader::new(file);
    let mut process = spawn(&prepare_program(project), Some(1000))?;
    let (x, _ ) = process.exp_regex(COQ_REGEX)?;

    for line in reader.lines() {
        process.send_line(&line?)?;
        let (answer, _) = process.exp_regex(COQ_REGEX)?;
        println!("[ {} ]", answer);
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
