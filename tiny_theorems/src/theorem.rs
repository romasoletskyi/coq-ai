use std::collections::HashSet;
use std::fmt::Display;
use std::io::Read;

use rand::Rng;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use anyhow::{bail, Result};

use crate::gen::Statement;
use crate::parser::{parse, tokenize};
use crate::refine::NormalStatement;
use crate::solver::ProofStep;

pub struct Theorem {
    name: String,
    pub props: Vec<char>,
    pub statement: Statement,
    pub proof: Vec<ProofStep>,
}

impl Theorem {
    pub fn new(
        name: String,
        props: Vec<char>,
        statement: Statement,
        proof: Vec<ProofStep>,
    ) -> Self {
        Theorem {
            name,
            props,
            statement,
            proof,
        }
    }
}

impl Display for Theorem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Theorem {}: forall (", self.name)?;
        for (i, symbol) in self.props.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", symbol)?;
        }
        writeln!(f, " : Prop), {}.", self.statement.to_expression())?;
        writeln!(f, "Proof.")?;
        write!(
            f,
            "{}",
            ProofStep::Intros(self.props.iter().map(|c| c.to_string()).collect())
        )?;

        for step in &self.proof {
            write!(f, "{}", step)?;
        }

        writeln!(f, "\nQed.")
    }
}

pub struct TheoremNameGenerator {
    names: HashSet<String>,
    rng: ChaCha8Rng,
}

impl TheoremNameGenerator {
    pub fn new() -> Self {
        TheoremNameGenerator {
            names: HashSet::new(),
            rng: ChaCha8Rng::from_entropy(),
        }
    }

    pub fn generate_name(&mut self) -> String {
        let mut name = String::new();
        for _ in 0..6 {
            name.push(self.rng.gen_range('a'..'{'));
        }
        self.names.insert(name.clone());
        name
    }
}

pub struct TheoremParser<'a> {
    reader: &'a mut dyn Read,
}

impl<'a> TheoremParser<'a> {
    pub fn new(reader: &'a mut dyn Read) -> Self {
        TheoremParser { reader }
    }

    fn read_amount(&mut self, size: usize) -> Result<String> {
        let mut buffer = vec![0; size];
        self.reader.read_exact(&mut buffer)?;
        Ok(String::from_utf8(buffer)?)
    }

    fn read_until(&mut self, stop: fn(char) -> bool) -> Result<String> {
        let mut buffer = [0; 1];
        let mut s = String::new();
        loop {
            self.reader.read_exact(&mut buffer)?;
            let ch = buffer[0] as char;
            if stop(ch) {
                break;
            } else {
                s.push(ch);
            }
        }
        Ok(s)
    }

    fn parse_tactic(data: &str) -> Result<Vec<ProofStep>> {
        if data.starts_with("apply") {
            return Ok(vec![ProofStep::Apply(data[6..].to_string())]);
        }
        if data.starts_with("intros") {
            return Ok(vec![ProofStep::Intros(
                data[7..].split(' ').map(|x| x.to_string()).collect(),
            )]);
        }
        if data.starts_with(['-', '+', '*']) {
            let (bullet, left) = data.split_once(' ').unwrap();
            let level = 1
                + 3 * (bullet.len() - 1)
                + match bullet.chars().next().unwrap() {
                    '-' => 0,
                    '+' => 1,
                    _ => 2,
                };
            let mut tactic = vec![ProofStep::Bullet(level)];
            tactic.extend(Self::parse_tactic(left)?.into_iter());
            return Ok(tactic);
        }
        bail!("tactic not matched");
    }

    pub fn next(&mut self) -> Result<Theorem> {
        self.read_until(|ch| ch == 'T')?;
        if &self.read_amount(7)? != "heorem " {
            bail!("doesn't start with theorem");
        }
        let name = self.read_amount(6)?;
        if &self.read_amount(10)? != ": forall (" {
            bail!("doesn't contain forall");
        }

        let mut props = Vec::new();
        loop {
            let ch = self.read_amount(2)?.chars().next().unwrap();
            if ch != ':' {
                props.push(ch);
            } else {
                break;
            }
        }

        if &self.read_amount(7)? != "Prop), " {
            bail!("doesn't contain Prop");
        }

        let stop = |ch| ch == '.';
        let data = self.read_until(stop)?;
        let tokens = tokenize(&data)?;
        let expr = parse(tokens.as_slice())?;
        let statement = NormalStatement::new(Statement::new(expr)).into();

        if !self.read_until(stop)?.ends_with("Proof") {
            bail!("doesn't begin with Proof");
        }

        let mut prop_intro = false;
        let mut proof = Vec::new();
        loop {
            let chunk = self.read_until(stop)?;
            let data = chunk.trim();
            if data == "Qed" {
                break;
            } else {
                if prop_intro {
                    proof.extend(Self::parse_tactic(data)?.into_iter());
                } else {
                    prop_intro = true;
                }
            }
        }

        Ok(Theorem {
            name,
            props,
            statement,
            proof,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::TheoremParser;

    fn check(data: &str) {
        let mut cursor = Cursor::new(data.as_bytes());
        let mut parser = TheoremParser::new(&mut cursor);
        let theorem = parser.next().unwrap();
        println!("{}", theorem);
    }

    #[test]
    fn bullets() {
        check("Theorem weofxf: forall (A B C : Prop), ((A -> B) -> B) -> ((A -> C) -> C) -> (A -> B) -> (B -> A -> C) -> (C -> B -> A) -> A.
        Proof.
        intros A B C. intros HABB HACC HAB HBAC HCBA. apply HCBA. 
          - apply HACC. intros HA. apply HBAC. 
            + apply HAB. apply HA. 
            + apply HA. 
          - apply HABB. intros HA0. apply HAB. apply HA0. 
        Qed.");
    }
}
