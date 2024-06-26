use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::parser::Expression;

pub struct Prover {
    hyp: HashSet<Arc<Expression>>,
    imp: HashMap<Arc<Expression>, Vec<Arc<Expression>>>,
}

impl Prover {
    fn new() -> Self {
        Prover {
            hyp: HashSet::new(),
            imp: HashMap::new(),
        }
    }

    fn insert_hyp(&mut self, hypothesis: &Arc<Expression>) {
        if self.hyp.contains(hypothesis) {
            return;
        }
        self.hyp.insert(hypothesis.clone());
        if let Expression::Implication(implication) = &**hypothesis {
            let mut expr = implication.left.clone();
            loop {
                self.imp
                    .entry(expr.clone())
                    .or_default()
                    .push(implication.right.clone());
                if self.hyp.contains(&expr) {
                    for implied in &self.imp.get(&expr).unwrap().clone() {
                        self.insert_hyp(implied);
                    }
                }
                if let Expression::Implication(imp) = &*expr {
                    expr = imp.right.clone();
                } else {
                    break;
                }
            }
        }
        if self.imp.contains_key(hypothesis) {
            for implied in &self.imp.get(hypothesis).unwrap().clone() {
                self.insert_hyp(implied);
            }
        }
    }

    fn analyze(&mut self, hyp: &Vec<Arc<Expression>>) {
        for hypothesis in hyp {
            if !self.hyp.contains(hypothesis) {
                self.insert_hyp(hypothesis);
            }
        }
    }

    fn proven(self) -> Vec<Arc<Expression>> {
        self.hyp.iter().cloned().collect()
    }
}

pub fn analyze(hyp: &Vec<Arc<Expression>>) -> Vec<Arc<Expression>> {
    let mut prover = Prover::new();
    prover.analyze(hyp);
    prover.proven()
}

#[cfg(test)]
mod tests {
    use std::vec;

    use crate::parser::{parse, tokenize};
    use crate::valid::analyze;

    fn check(data: Vec<&str>) {
        let hyp = data
            .iter()
            .map(|s| parse(tokenize(s).unwrap().as_slice()).unwrap())
            .collect();
        let proven = analyze(&hyp);

        for expr in proven {
            println!("{}", expr);
        }
    }

    #[test]
    fn simple() {
        check(vec!["P -> Q", "P"]);
    }

    #[test]
    fn logic() {
        check(vec!["Q", "(P -> Q) -> R"]);
    }

    #[test]
    fn overflow1() {
        check(vec!["M", "R -> M", "M -> R"]);
    }

    #[test]
    fn overflow2() {
        check(vec!["M", "(S -> R) -> M", "M -> R"]);
    }

    #[test]
    fn complex() {
        check(vec![
            "P -> Q",
            "P -> R",
            "T -> R",
            "S -> T -> U",
            "(P -> Q) -> (P -> S)",
            "T",
            "P",
        ]);
    }
}
