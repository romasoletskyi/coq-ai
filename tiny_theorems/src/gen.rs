use std::collections::{hash_map::DefaultHasher, HashMap, HashSet};
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use rand::{seq::SliceRandom, Rng};
use rand_chacha::ChaCha8Rng;

use crate::parser::{Expression, Implication, UniqueExpression};
use crate::refiner::NormalStatement;
use crate::solver::{get_proof, ProofStep};
use crate::valid::analyze;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Statement {
    pub hyp: Vec<Arc<Expression>>,
    pub goal: Arc<Expression>,
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_expression())
    }
}

impl From<UniqueStatement> for Statement {
    fn from(value: UniqueStatement) -> Self {
        Statement {
            hyp: value.hyp.into_iter().map(|x| x.into()).collect(),
            goal: value.goal.into(),
        }
    }
}

impl Statement {
    pub fn new(goal: Arc<Expression>) -> Self {
        Statement {
            hyp: Vec::new(),
            goal,
        }
    }

    pub fn to_expression(&self) -> Arc<Expression> {
        let mut expr = self.goal.clone();
        for hypothesis in self.hyp.iter().rev() {
            expr = Arc::new(Expression::Implication(Implication {
                left: hypothesis.clone(),
                right: expr,
            }));
        }
        expr
    }
}

pub struct UniqueStatement {
    hyp: Vec<Box<UniqueExpression>>,
    goal: Box<UniqueExpression>,
}

impl From<Statement> for UniqueStatement {
    fn from(value: Statement) -> Self {
        UniqueStatement {
            hyp: value.hyp.iter().map(|x| x.clone().into()).collect(),
            goal: value.goal.into(),
        }
    }
}

pub struct Mutator {
    hyp_cum_prob: Vec<f64>,
    goal_change_prob: f64,
}

impl Mutator {
    pub fn new(hyp_prob: Vec<f64>, goal_change_prob: f64) -> Self {
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
        old: Arc<Expression>,
        new: &Vec<Arc<Expression>>,
    ) -> Arc<Expression> {
        let p = rng.gen_range(0.0..1.0);
        if p < self.goal_change_prob {
            new[rng.gen_range(0..new.len())].clone()
        } else {
            old
        }
    }
}

pub fn generate_prop_symbols(symbol_num: usize) -> Vec<char> {
    let mut symbols = Vec::new();
    for i in 0..symbol_num {
        symbols.push(b'A'.wrapping_add(i as u8) as char);
    }
    symbols
}

pub struct StatementGenerator {
    symbols: Vec<char>,
    update_length: usize,
    mutator: Mutator,
    rng: ChaCha8Rng,
}

impl StatementGenerator {
    pub fn new(symbols: Vec<char>, update_length: usize, mutator: Mutator, seed: u64) -> Self {
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

    fn gen_hypothesis(&mut self) -> Arc<Expression> {
        Arc::new(match self.mutator.get_hyp_index(&mut self.rng) {
            0 => Expression::Basic(self.gen_char()),
            1 => {
                let s = self.gen_different_chars(2);
                Expression::Implication(Implication {
                    left: Arc::new(Expression::Basic(s[0])),
                    right: Arc::new(Expression::Basic(s[1])),
                })
            }
            2 => {
                let s = self.gen_different_chars(2);
                Expression::Implication(Implication {
                    left: Arc::new(Expression::Implication(Implication {
                        left: Arc::new(Expression::Basic(s[0])),
                        right: Arc::new(Expression::Basic(s[1])),
                    })),
                    right: Arc::new(Expression::Basic(self.gen_char())),
                })
            }
            3 => {
                let s = self.gen_different_chars(3);
                Expression::Implication(Implication {
                    left: Arc::new(Expression::Basic(s[0])),
                    right: Arc::new(Expression::Implication(Implication {
                        left: Arc::new(Expression::Basic(s[1])),
                        right: Arc::new(Expression::Basic(s[2])),
                    })),
                })
            }
            4 => {
                let s = self.gen_different_chars(2);
                let t = self.gen_different_chars(2);
                Expression::Implication(Implication {
                    left: Arc::new(Expression::Implication(Implication {
                        left: Arc::new(Expression::Basic(s[0])),
                        right: Arc::new(Expression::Basic(s[1])),
                    })),
                    right: Arc::new(Expression::Implication(Implication {
                        left: Arc::new(Expression::Basic(t[0])),
                        right: Arc::new(Expression::Basic(t[1])),
                    })),
                })
            }
            _ => {
                let s = self.gen_different_chars(4);
                Expression::Implication(Implication {
                    left: Arc::new(Expression::Basic(s[0])),
                    right: Arc::new(Expression::Implication(Implication {
                        left: Arc::new(Expression::Basic(s[1])),
                        right: Arc::new(Expression::Implication(Implication {
                            left: Arc::new(Expression::Basic(s[2])),
                            right: Arc::new(Expression::Basic(s[3])),
                        })),
                    })),
                })
            }
        })
    }

    pub fn initalize_statement(symbols: &[char]) -> Statement {
        let goal = Arc::new(Expression::Basic(symbols[0]));
        Statement {
            hyp: vec![goal.clone()],
            goal,
        }
    }

    pub fn mutate_statement(
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
            let goals: Vec<_> = analyze(&statement.hyp)
                .iter()
                .filter(|&expr| matches!(**expr, Expression::Basic(_)))
                .cloned()
                .collect();
            if !goals.is_empty() {
                statement.goal = self
                    .mutator
                    .choose_goal(&mut self.rng, statement.goal, &goals);
            }

            let proof = get_proof(statement.to_expression());

            if let ProofStep::Intros(intros) = &proof[0] {
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

                let mut used_set = HashSet::new();
                for step in proof.iter().skip(1) {
                    if let ProofStep::Apply(name) = step {
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

            statement = NormalStatement::new(statement).into();
            statements.push((statement.clone(), get_proof(statement.to_expression())));
        }
        statements
    }
}

pub struct StatementBank {
    pub hashes: HashSet<u64>,
}

impl StatementBank {
    pub fn new() -> Self {
        StatementBank {
            hashes: HashSet::new(),
        }
    }

    fn hash(statement: &Statement) -> u64 {
        let mut hasher = DefaultHasher::new();
        statement.hash(&mut hasher);
        hasher.finish()
    }

    pub fn len(&self) -> usize {
        self.hashes.len()
    }

    pub fn contains(&self, statement: &Statement) -> bool {
        self.hashes.contains(&StatementBank::hash(statement))
    }

    pub fn insert(&mut self, statement: &Statement) {
        self.hashes.insert(StatementBank::hash(statement));
    }
}

#[cfg(test)]
mod tests {
    use super::{generate_prop_symbols, Mutator, StatementGenerator};
    use crate::theorem::{Theorem, TheoremNameGenerator};

    #[test]
    fn mutate_statements() {
        let symbols = generate_prop_symbols(4);
        let mut statements = vec![StatementGenerator::initalize_statement(&symbols)];

        let mut gen = StatementGenerator::new(
            symbols.clone(),
            2,
            Mutator::new(vec![0.2, 0.2, 0.2, 0.2, 0.1, 0.1], 0.5),
            0,
        );
        let mut name_gen = TheoremNameGenerator::new();

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
                let (statement, proof) = &mutated[i];
                print!(
                    "{}",
                    Theorem::new(
                        name_gen.generate_name(),
                        symbols.clone(),
                        statement.clone(),
                        proof.clone()
                    )
                );
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
