use std::fmt::Display;
use std::sync::Arc;

use anyhow::{bail, Ok, Result};

use crate::{gen::Statement, solver::{use_tactic, ProofStep, State}};

#[derive(Debug)]
pub enum EnvError {
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
    states: Vec<Arc<State>>
}

impl Env {
    pub fn new() -> Env {
        Env { states: Vec::new() }
    }

    pub fn current_state(&self) -> Option<&Arc<State>> {
        self.states.last()
    }

    pub fn reset(&mut self) {
        self.states.clear();
    }

    pub fn load_statement(&mut self, statement: &Statement) -> Result<()> {
        if self.states.is_empty() {
            self.states = vec![Arc::new(State::new(statement.to_expression()))];
            Ok(())
        } else {
            bail!(EnvError::UnsolvedGoals);
        }
    }

    pub fn step(&mut self, step: ProofStep) -> Result<()> {
        if let Some(state) = self.states.last() {
            if let Some(tactic) = step.into() {
                use_tactic(state, &tactic).and_then(|states| {
                    self.states.pop();
                    self.states.extend(states.into_iter().rev());
                    Ok(())
                })?;
            }
            Ok(())
        } else {
            bail!(EnvError::OutsideProof);
        }
    }
}