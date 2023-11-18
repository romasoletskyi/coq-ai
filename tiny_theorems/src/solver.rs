use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;

use anyhow::{bail, Result};

use crate::parser::Expression;

struct Hypothesis {
    name: String,
    goals: Vec<Rc<Expression>>,
}

pub struct Solver {
    hyp: HashMap<Rc<Expression>, Hypothesis>,
    names: Vec<String>,
    goal: Rc<Expression>,
    level: usize,
}

#[derive(Debug)]
enum SolverError {
    NoMatch,
}

impl Display for SolverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SolverError::NoMatch => write!(f, "can't find hypothesis"),
        }
    }
}

enum ProofStep {
    Intros(Vec<String>),
    Apply(String),
    Bullet(usize),
}

impl Display for ProofStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofStep::Intros(intros) => {
                write!(f, "intros")?;
                for name in intros {
                    write!(f, " {}", name)?;
                }
                write!(f, ".")
            }
            ProofStep::Apply(apply) => write!(f, " apply {}.", apply),
            Self::Bullet(level) => {
                let size = 1 + (level - 1) / 3;
                let symbol = match (level - 1) % 3 {
                    0 => '-',
                    1 => '+',
                    _ => '*',
                };
                writeln!(f, "")?;
                for _ in 0..*level {
                    write!(f, "  ")?;
                }
                for _ in 0..size {
                    write!(f, "{}", symbol)?;
                }
                std::result::Result::Ok(())
            }
        }
    }
}

fn search_names(props: &mut Vec<char>, expr: &Rc<Expression>) {
    match &**expr {
        Expression::Implication(implication) => {
            search_names(props, &implication.left);
            search_names(props, &implication.right);
        }
        Expression::Basic(symbol) => {
            props.push(*symbol);
        }
    }
}

fn find_names(expr: &Rc<Expression>) -> Vec<char> {
    let mut props = Vec::new();
    search_names(&mut props, &expr);
    props
}

impl Solver {
    fn new(
        mut expr: Rc<Expression>,
        mut naming: Box<dyn FnMut(&Rc<Expression>) -> String>,
    ) -> Self {
        let mut known = Vec::new();
        while let Expression::Implication(implication) = &*expr {
            known.push(implication.left.clone());
            expr = implication.right.clone();
        }

        let mut hyp = HashMap::new();
        let mut names = Vec::new();

        for mut hypothesis in known {
            let mut goals = Vec::new();
            let name = naming(&hypothesis);
            loop {
                hyp.insert(
                    hypothesis.clone(),
                    Hypothesis {
                        name: name.clone(),
                        goals: goals.clone(),
                    },
                );
                if let Expression::Implication(implication) = &*hypothesis {
                    goals.push(implication.left.clone());
                    hypothesis = implication.right.clone();
                } else {
                    break;
                }
            }
            names.push(name);
        }

        Solver {
            hyp,
            names,
            goal: expr,
            level: 0,
        }
    }

    fn solve(&mut self) -> Result<Vec<ProofStep>> {
        let mut proof = vec![ProofStep::Intros(self.names.clone())];
        let mut goals = vec![(0, 0, self.goal.clone())];
        while !goals.is_empty() {
            let (jump, level, goal) = goals.pop().unwrap();

            self.level = level;
            if jump != 0 {
                proof.push(ProofStep::Bullet(level));
            }

            if let Some(hypothesis) = self.hyp.get(&goal) {
                proof.push(ProofStep::Apply(hypothesis.name.clone()));
                let jump = if hypothesis.goals.len() > 1 { 1 } else { 0 };
                for goal in hypothesis.goals.iter().rev() {
                    goals.push((jump, self.level + jump, goal.clone()));
                }
            } else {
                bail!(SolverError::NoMatch);
            }
        }
        Ok(proof)
    }
}

#[cfg(test)]
mod tests {
    use super::{find_names, Solver};
    use crate::parser::{parse, tokenize, Expression};
    use std::rc::Rc;

    fn check(data: &str) {
        let tokens = tokenize(data).unwrap();
        let expr = parse(tokens.as_slice()).unwrap();

        let mut solver = Solver::new(
            expr,
            Box::new(|expr: &Rc<Expression>| {
                let names = find_names(expr);
                let mut hyp = "H".to_string();
                for name in names {
                    hyp.push(name);
                }
                hyp
            }),
        );
        let solution = solver.solve().unwrap();
        for step in solution {
            print!("{}", step);
        }
    }

    #[test]
    fn simple() {
        check("(P -> Q) -> P -> Q");
    }

    #[test]
    fn complex() {
        check(
            "(P -> Q) -> (P -> R) -> (T -> R) ->
            (S -> T ->  U) -> ((P -> Q) -> (P -> S)) ->
            T -> P -> U",
        );
    }
}
