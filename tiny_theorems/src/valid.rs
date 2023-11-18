use std::collections::HashMap;
use std::rc::Rc;

use crate::parser::Expression;

pub struct Prover {
    hyp: HashMap<Rc<Expression>, usize>,
    imp: HashMap<Rc<Expression>, Vec<Rc<Expression>>>,
    index: usize,
}

impl Prover {
    fn new() -> Self {
        Prover {
            hyp: HashMap::new(),
            imp: HashMap::new(),
            index: 0,
        }
    }

    fn store(&mut self, expr: Rc<Expression>) {
        if *self.hyp.entry(expr.clone()).or_insert_with(|| self.index) == self.index {
            if let Expression::Implication(implication) = &*expr {
                self.imp
                    .entry(implication.left.clone())
                    .or_default()
                    .push(implication.right.clone());
            }
            self.index += 1;
        }
    }

    fn contains_hyp(&self, hyp: &Rc<Expression>) -> bool {
        self.hyp.contains_key(hyp)
    }

    fn get_imp(&self, left: &Rc<Expression>) -> Vec<Rc<Expression>> {
        if let Some(vec) = self.imp.get(left) {
            vec.clone()
        } else {
            Vec::new()
        }
    }
}

fn update_provable(prover: &mut Prover, expr: Rc<Expression>) {
    prover.store(expr.clone());
    match &*expr {
        Expression::Implication(implication) => {
            if prover.contains_hyp(&implication.left.clone()) {
                update_provable(prover, implication.right.clone());
            }
        }
        _ => {}
    }
    for proof in prover.get_imp(&expr) {
        update_provable(prover, proof);
    }
}

fn analyze_with_prover(prover: &mut Prover, expr: Rc<Expression>) {
    match &*expr {
        Expression::Implication(implication) => {
            update_provable(prover, implication.left.clone());
            analyze_with_prover(prover, implication.right.clone());
        }
        _ => {}
    }
}

pub fn analyze(expr: Rc<Expression>) -> Prover {
    let mut prover = Prover::new();
    analyze_with_prover(&mut prover, expr.into());
    prover
}

#[cfg(test)]
mod tests {
    use super::analyze;
    use crate::parser::{parse, tokenize};

    fn check(data: &str) {
        let tokens = tokenize(data).unwrap();
        let expr = parse(tokens.as_slice()).unwrap();
        let prover = analyze(expr);

        for (expr, index) in prover.hyp {
            println!("{}: {}", index, expr);
        }
    }

    #[test]
    fn simple() {
        check("(P -> Q) -> P -> Z");
    }

    #[test]
    fn complex() {
        check(
            "(P -> Q) -> (P -> R) -> (T -> R) ->
            (S -> T ->  U) -> ((P -> Q) -> (P -> S)) ->
            T -> P -> Z",
        );
    }
}
