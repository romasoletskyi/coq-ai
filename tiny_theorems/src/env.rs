use std::fmt::Display;
use std::rc::Rc;

use anyhow::{bail, Ok, Result};

use crate::{gen::Statement, solver::{use_tactic, ProofStep, State}};

#[derive(Debug)]
enum EnvError {
    UnsolvedGoals,
    OutsideProof
}

impl Display for EnvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::UnsolvedGoals => write!(f, "there are unsolved goals"),
            EnvError::OutsideProof => write!(f, "outside of proof mode")
        }
    }
}

pub struct Env {
    states: Vec<Rc<State>>
}

impl Env {
    pub fn new() -> Env {
        Env { states: Vec::new() }
    }

    pub fn current_state(&self) -> Option<Rc<State>> {
        self.states.last().cloned()
    }

    pub fn load_statement(&mut self, statement: &Statement) -> Result<()> {
        if self.states.is_empty() {
            self.states = vec![Rc::new(State::new(statement.to_expression()))];
            Ok(())
        } else {
            bail!(EnvError::UnsolvedGoals);
        }
    }

    pub fn step(&mut self, step: ProofStep) -> Result<()> {
        if let Some(state) = self.states.pop() {
            if let Some(tactic) = step.into() {
                for state in use_tactic(&state, &tactic)?.into_iter().rev() {
                    self.states.push(state);
                }
            } else {
                self.states.push(state);
            }
            Ok(())
        } else {
            bail!(EnvError::OutsideProof);
        }
    }
}