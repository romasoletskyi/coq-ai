use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::Hasher;
use std::rc::Rc;

use crate::gen::Statement;
use crate::parser::{Expression, Implication};

struct Alphabet {
    map: HashMap<char, u8>,
    hash: HashMap<char, Vec<(u64, u64)>>,
    current: u8,
}

impl Alphabet {
    fn new() -> Self {
        Alphabet {
            map: HashMap::new(),
            hash: HashMap::new(),
            current: 0,
        }
    }

    fn encode_hypothesis(&mut self, expr: &Rc<Expression>) {
        let mut hasher = DefaultHasher::new();
        let mut traces = Vec::new();
        let mut nodes = vec![expr.clone()];

        while let Some(node) = nodes.pop() {
            match &*node {
                Expression::Basic(letter) => {
                    hasher.write_u8(*self.map.entry(*letter).or_insert(self.current));
                    traces.push((*letter, hasher.finish()));
                }
                Expression::Implication(imp) => {
                    nodes.push(imp.left.clone());
                    nodes.push(imp.right.clone());
                }
            }
        }

        for (letter, key) in traces {
            self.hash
                .entry(letter)
                .or_default()
                .push((key, hasher.finish()));
        }
    }

    fn rename_letters(&mut self) -> u8 {
        for letter in self.map.keys() {
            self.hash.entry(*letter).or_default().sort();
        }

        let mut hashes: Vec<_> = self.hash.iter().collect();
        hashes.sort_by(|a, b| a.1.cmp(b.1));

        self.current = 0;
        for i in 0..hashes.len() {
            if i > 0 && hashes[i].1 != hashes[i - 1].1 {
                self.current += 1;
            }
            self.map.insert(*hashes[i].0, self.current);
        }

        self.hash.clear();
        self.current + 1
    }

    fn dedup_letters(&mut self) {
        let mut names: Vec<_> = self.map.iter().map(|x| (*x.0, *x.1)).collect();
        names.sort_by(|a, b| (a.1, a.0).cmp(&(b.1, b.0)));

        self.current = 0;
        for (letter, _) in names {
            self.map.insert(letter, self.current);
            self.current += 1;
        }
    }

    fn rename_expression(&self, expr: &Rc<Expression>) -> Rc<Expression> {
        Rc::new(match &**expr {
            Expression::Basic(letter) => {
                Expression::Basic(b'A'.wrapping_add(*self.map.get(letter).unwrap()) as char)
            }
            Expression::Implication(imp) => Expression::Implication(Implication {
                left: self.rename_expression(&imp.left),
                right: self.rename_expression(&imp.right),
            }),
        })
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct NormalStatement(Statement);

impl From<NormalStatement> for Statement {
    fn from(value: NormalStatement) -> Self {
        value.0
    }
}

impl NormalStatement {
    pub fn new(mut statement: Statement) -> Self {
        while let Expression::Implication(imp) = &*statement.goal {
            statement.hyp.push(imp.left.clone());
            statement.goal = imp.right.clone();
        }

        let mut alphabet = Alphabet::new();
        let mut distinct = None;

        loop {
            for hyp in &statement.hyp {
                alphabet.encode_hypothesis(hyp);
            }
            let new_distinct = alphabet.rename_letters();
            if new_distinct as usize == alphabet.map.len() || distinct == Some(new_distinct) {
                break;
            } else {
                distinct = Some(new_distinct);
            }
        }
        alphabet.dedup_letters();

        let mut normal = Statement::new(alphabet.rename_expression(&statement.goal));
        for hyp in &statement.hyp {
            normal.hyp.push(alphabet.rename_expression(hyp));
        }
        normal.hyp.sort();

        NormalStatement(normal)
    }
}

mod tests {
    use crate::{
        gen::Statement,
        parser::{parse, tokenize},
    };

    use super::NormalStatement;

    fn check(data: &str) {
        let tokens = tokenize(data).unwrap();
        let goal = parse(tokens.as_slice()).unwrap();
        let normal = NormalStatement::new(Statement::new(goal));
        println!("{}", normal.0);
    }

    #[test]
    fn basic() {
        check("((N -> M) -> N) -> (M -> N -> O -> S) -> (M -> N -> R) -> (N -> R -> O) -> M -> S");
        check("(M -> N -> O -> S) -> (M -> N -> R) -> M -> ((N -> M) -> N) -> (N -> R -> O) -> S");
        check("(M -> Y -> Z -> S) -> (M -> Y -> R) -> M -> ((Y -> M) -> Y) -> (Y -> R -> Z) -> S");
    }

    #[test]
    fn symmetry() {
        check("(A -> C) -> (B -> C) -> C");
        check("(B -> C) -> (A -> C) -> C");
        check("(C -> A) -> (B -> A) -> A");
        check("(B -> A) -> (C -> A) -> A");
        check("(C -> B) -> (A -> B) -> B");
        check("(A -> B) -> (C -> B) -> B");
    }
}
