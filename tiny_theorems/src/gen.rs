use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::io::Write;
use std::rc::Rc;

use rand::SeedableRng;
use rand::{seq::SliceRandom, Rng};
use rand_chacha::ChaCha8Rng;

use crate::parser::{Expression, Implication};
use crate::solver::{find_shortest, get_proof, sample_proof, ProofStep};
use crate::valid::analyze;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    hyp: Vec<Rc<Expression>>,
    goal: Rc<Expression>,
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_expression())
    }
}

impl Statement {
    fn to_expression(&self) -> Rc<Expression> {
        let mut expr = self.goal.clone();
        for hypothesis in self.hyp.iter().rev() {
            expr = Rc::new(Expression::Implication(Implication {
                left: hypothesis.clone(),
                right: expr,
            }));
        }
        expr
    }
}

struct Mutator {
    hyp_cum_prob: Vec<f64>,
    goal_change_prob: f64,
}

impl Mutator {
    fn new(hyp_prob: Vec<f64>, goal_change_prob: f64) -> Self {
        let hyp_cum_prob = hyp_prob
            .iter()
            .filter_map({
                let mut sum = 0.0;
                move |x| {
                    sum += x;
                    Some(sum)
                }
            })
            .collect();
        Mutator {
            hyp_cum_prob,
            goal_change_prob,
        }
    }

    fn get_hyp_index<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        let p = rng.gen_range(0.0..1.0);
        let mut index = 0;
        while self.hyp_cum_prob[index] < p {
            index += 1;
        }
        index
    }

    fn choose_goal<R: Rng + ?Sized>(
        &self,
        rng: &mut R,
        old: Rc<Expression>,
        new: &Vec<Rc<Expression>>,
    ) -> Rc<Expression> {
        let p = rng.gen_range(0.0..1.0);
        if p < self.goal_change_prob {
            new[rng.gen_range(0..new.len())].clone()
        } else {
            old
        }
    }
}

pub struct StatementGenerator {
    symbols: Vec<char>,
    update_length: usize,
    mutator: Mutator,
    rng: ChaCha8Rng,
}

impl StatementGenerator {
    fn new(symbols_num: usize, update_length: usize, mutator: Mutator, seed: u64) -> Self {
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let mut s = HashSet::new();
        while s.len() < symbols_num {
            s.insert(rng.gen_range('A'..'['));
        }
        let mut symbols: Vec<char> = s.iter().copied().collect();
        symbols.sort();

        StatementGenerator {
            symbols,
            update_length,
            mutator,
            rng: rand::SeedableRng::seed_from_u64(seed),
        }
    }

    fn gen_char(&mut self) -> char {
        self.symbols[self.rng.gen_range(0..self.symbols.len())]
    }

    fn gen_different_chars(&mut self, num: usize) -> Vec<char> {
        let mut symbols = self.symbols.clone();
        symbols.shuffle(&mut self.rng);
        symbols[..num].to_vec()
    }

    fn gen_hypothesis(&mut self) -> Rc<Expression> {
        Rc::new(match self.mutator.get_hyp_index(&mut self.rng) {
            0 => Expression::Basic(self.gen_char()),
            1 => {
                let s = self.gen_different_chars(2);
                Expression::Implication(Implication {
                    left: Rc::new(Expression::Basic(s[0])),
                    right: Rc::new(Expression::Basic(s[1])),
                })
            }
            2 => {
                let s = self.gen_different_chars(2);
                Expression::Implication(Implication {
                    left: Rc::new(Expression::Implication(Implication {
                        left: Rc::new(Expression::Basic(s[0])),
                        right: Rc::new(Expression::Basic(s[1])),
                    })),
                    right: Rc::new(Expression::Basic(self.gen_char())),
                })
            }
            3 => {
                let s = self.gen_different_chars(3);
                Expression::Implication(Implication {
                    left: Rc::new(Expression::Basic(s[0])),
                    right: Rc::new(Expression::Implication(Implication {
                        left: Rc::new(Expression::Basic(s[1])),
                        right: Rc::new(Expression::Basic(s[2])),
                    })),
                })
            }
            4 => {
                let s = self.gen_different_chars(2);
                let t = self.gen_different_chars(2);
                Expression::Implication(Implication {
                    left: Rc::new(Expression::Implication(Implication {
                        left: Rc::new(Expression::Basic(s[0])),
                        right: Rc::new(Expression::Basic(s[1])),
                    })),
                    right: Rc::new(Expression::Implication(Implication {
                        left: Rc::new(Expression::Basic(t[0])),
                        right: Rc::new(Expression::Basic(t[1])),
                    })),
                })
            }
            _ => {
                let s = self.gen_different_chars(4);
                Expression::Implication(Implication {
                    left: Rc::new(Expression::Basic(s[0])),
                    right: Rc::new(Expression::Implication(Implication {
                        left: Rc::new(Expression::Basic(s[1])),
                        right: Rc::new(Expression::Implication(Implication {
                            left: Rc::new(Expression::Basic(s[2])),
                            right: Rc::new(Expression::Basic(s[3])),
                        })),
                    })),
                })
            }
        })
    }

    fn initalize_statement(&self) -> Statement {
        let goal = Rc::new(Expression::Basic(self.symbols[0]));
        Statement {
            hyp: vec![goal.clone()],
            goal,
        }
    }

    fn mutate_statement(
        &mut self,
        old_statement: &Statement,
        sample: usize,
    ) -> Vec<(Statement, Vec<ProofStep>)> {
        let mut statements = Vec::new();
        for _ in 0..sample {
            let mut statement = old_statement.clone();

            for _ in 0..self.update_length {
                statement.hyp.push(self.gen_hypothesis());
            }
            println!("mut hyp {}", statement);

            let goals: Vec<_> = analyze(&statement.hyp)
                .iter()
                .filter(|&expr| match **expr {
                    Expression::Basic(_) => true,
                    _ => false,
                })
                .cloned()
                .collect();
            if !goals.is_empty() {
                statement.goal = self
                    .mutator
                    .choose_goal(&mut self.rng, statement.goal, &goals);
            }
            println!("mut goal {}", statement);

            let proof = get_proof(&mut self.rng, statement.to_expression(), |state, rng| {
                sample_proof(find_shortest(state), rng)
            });
            println!("proved");

            if let ProofStep::Intros(intros) = &proof[0] {
                println!("{:?}", intros);
                let hyp_names: HashMap<_, _> = intros
                    .iter()
                    .map({
                        let mut index: usize = 0;
                        move |name| {
                            index += 1;
                            (name.clone(), index - 1)
                        }
                    })
                    .collect();

                println!("{:?}", hyp_names);
                println!("{:?}", proof);
                let mut used_set = HashSet::new();
                for i in 1..proof.len() {
                    if let ProofStep::Apply(name) = &proof[i] {
                        if let Some(&index) = hyp_names.get(name) {
                            used_set.insert(index);
                        }
                    }
                }
                let mut used: Vec<_> = used_set.iter().copied().collect();
                used.sort();

                statement.hyp = used
                    .iter()
                    .map(|&index| statement.hyp[index].clone())
                    .collect();
            } else {
                panic!("proof doesn't start with intros");
            }

            let mut sorted_statement = statement.clone();
            sorted_statement.hyp.sort();

            statements.push((
                sorted_statement,
                get_proof(&mut self.rng, statement.to_expression(), |state, rng| {
                    sample_proof(find_shortest(state), rng)
                }),
            ));
        }
        statements
    }
}

pub struct TheoremPrinter {
    names: HashSet<String>,
    rng: ChaCha8Rng,
}

impl TheoremPrinter {
    fn new() -> Self {
        TheoremPrinter {
            names: HashSet::new(),
            rng: ChaCha8Rng::from_entropy(),
        }
    }

    fn generate_name(&mut self) -> String {
        let mut name = String::new();
        for _ in 0..6 {
            name.push(self.rng.gen_range('a'..'{'));
        }
        name
    }

    pub fn print(
        &mut self,
        f: &mut dyn Write,
        generator: &StatementGenerator,
        statement: &Statement,
        proof: &Vec<ProofStep>,
    ) -> std::io::Result<()> {
        let mut name = String::new();
        loop {
            name = self.generate_name();
            if !self.names.contains(&name) {
                self.names.insert(name.clone());
                break;
            }
        }

        write!(f, "Theorem {}: forall", name)?;
        for symbol in &generator.symbols {
            write!(f, " {}", symbol)?;
        }
        writeln!(f, ", {}.", statement.to_expression())?;
        writeln!(f, "Proof.")?;
        write!(
            f,
            "{}",
            ProofStep::Intros(generator.symbols.iter().map(|c| c.to_string()).collect())
        )?;

        for step in proof {
            write!(f, "{}", step)?;
        }

        writeln!(f, "\nQed.")
    }
}

#[cfg(test)]
mod tests {
    use super::{Mutator, StatementGenerator, TheoremPrinter};

    #[test]
    fn mutate_statements() {
        let mut gen = StatementGenerator::new(
            5,
            2,
            Mutator::new(vec![0.2, 0.2, 0.2, 0.2, 0.1, 0.1], 0.5),
            0,
        );
        let mut printer = TheoremPrinter::new();
        let mut statements = vec![gen.initalize_statement()];

        let sample = 10;
        let pool = 10;

        for _ in 0..20 {
            let mut mutated: Vec<_> = statements
                .iter()
                .flat_map(|statement| gen.mutate_statement(statement, sample))
                .collect();
            mutated.sort_by(|a, b| b.1.len().cmp(&a.1.len()));
            mutated.dedup_by(|a, b| a.0.eq(&b.0));

            let cut_len = mutated.len().min(pool);
            for i in 0..cut_len {
                let mut handle = std::io::stdout().lock();
                let (statement, proof) = &mutated[i];
                printer.print(&mut handle, &gen, statement, proof).unwrap();
            }

            statements = mutated[..cut_len]
                .iter()
                .map(|(statement, _)| statement)
                .cloned()
                .collect();

            for statement in &statements {
                println!("{}", statement);
            }
        }
    }
}
