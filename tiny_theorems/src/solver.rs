use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt::{Display, Write};
use std::iter::zip;
use std::rc::Rc;

use anyhow::{bail, Result};
use rand::Rng;

use crate::parser::Expression;

/* During each step of proof we have a state [H |- goal] consisting of
premises H and a single goal. Using tactics we can change the state
by either changing premises H (for instance, destruct H) or goal.
After applying tactic we can have one or multiple goals to solve.

Each state can be in three states - unseen, dead, alive. Dead states
do not have tactics that we can apply and are not solved. Alive states
need to provide a list of possible tactics that can be applied and
for each tactic a list of goals required to solve.

For instance [HP: P |- P] is an alive goal solved as
[HP: P |- P] => apply HP => [] - we have no further goals.

It may happen so that there is a recursion, which we need to forbid
[H: Q -> P -> P |- P] => apply H => [H: Q -> P -> P |- Q]
                                 => [H: Q -> P -> P |- P]

After constructing a full graph of states we can collect all proofs
using depth-first search. */

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct State {
    hyp: BTreeMap<String, Rc<Expression>>,
    goal: Rc<Expression>,
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for hyp in self.hyp.keys() {
            write!(f, "{} ", hyp)?;
        }
        write!(f, "|- {}]", self.goal)
    }
}

#[derive(Debug, Clone)]
enum Tactic {
    Apply(String),
    Intros(Vec<String>),
}

impl Display for Tactic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Apply(hyp) => write!(f, "apply {}", hyp),
            Self::Intros(intros) => {
                write!(f, "intros")?;
                for intro in intros {
                    write!(f, " {}", intro)?;
                }
                std::fmt::Result::Ok(())
            }
        }
    }
}

#[derive(Debug)]
enum TacticError {
    WrongName(String),
    WrongHypothesis,
}

impl Display for TacticError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TacticError::WrongName(name) => write!(f, "can't find hypothesis with name {}", name),
            TacticError::WrongHypothesis => write!(f, "hypothesis implication doesn't match goal"),
        }
    }
}

#[derive(Debug, Clone)]
struct TacticApplication {
    tactic: Tactic,
    states: Vec<Rc<RefCell<StateNode>>>,
}

#[derive(Debug, Clone)]
struct StateNode {
    state: Rc<State>,
    tactic_apps: Vec<TacticApplication>,
}

impl Display for StateNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut visited = HashSet::new();
        let mut nodes = vec![self.clone()];
        while let Some(node) = nodes.pop() {
            visited.insert(node.state.clone());
            for app in &node.tactic_apps {
                let mut s = String::new();
                write!(&mut s, "{} => {} => ", node.state, app.tactic)?;
                write!(f, "{}", s)?;
                if app.states.is_empty() {
                    writeln!(f, "[]")?;
                } else {
                    writeln!(f, "{}", app.states[0].borrow().state)?;
                    for i in 1..app.states.len() {
                        write!(f, "{:>width$}", "", width = s.len())?;
                        writeln!(f, "{}", app.states[i].borrow().state)?;
                    }
                }
                for state in &app.states {
                    if !visited.contains(&state.borrow().state) {
                        nodes.push(state.borrow().clone());
                    }
                }
            }
        }
        std::fmt::Result::Ok(())
    }
}

// A common util for hypothesis naming

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

pub fn find_names(expr: &Rc<Expression>) -> Vec<char> {
    let mut props = Vec::new();
    search_names(&mut props, expr);
    props
}

pub fn name_simple_hypothesis(expr: &Rc<Expression>) -> String {
    let names = find_names(expr);
    let mut hyp = "H".to_string();
    for name in names {
        hyp.push(name);
    }
    hyp
}

pub struct Solver {
    naming: Box<dyn FnMut(&Rc<Expression>) -> String>,
    visited: HashMap<Rc<State>, Rc<RefCell<StateNode>>>,
}

impl Solver {
    fn unfold_expression(mut expr: Rc<Expression>) -> (Vec<Rc<Expression>>, Rc<Expression>) {
        let mut premise = Vec::new();
        while let Expression::Implication(imp) = &*expr {
            premise.push(imp.left.clone());
            expr = imp.right.clone();
        }
        (premise, expr)
    }

    fn use_tactic(&mut self, state: &Rc<State>, tactic: &Tactic) -> Result<Vec<Rc<State>>> {
        match tactic {
            Tactic::Apply(name) => {
                let hyp = if let Some(hyp) = state.hyp.get(name) {
                    hyp
                } else {
                    bail!(TacticError::WrongName(name.clone()));
                }
                .clone();

                let (to_prove, hyp) = Solver::unfold_expression(hyp);
                if hyp != state.goal {
                    bail!(TacticError::WrongHypothesis);
                }

                Ok(to_prove
                    .iter()
                    .map(|goal| {
                        Rc::new(State {
                            hyp: state.hyp.clone(),
                            goal: goal.clone(),
                        })
                    })
                    .collect())
            }
            Tactic::Intros(names) => {
                let (intros, goal) = Solver::unfold_expression(state.goal.clone());
                let mut new_state = (**state).clone();

                new_state.goal = goal;
                for (name, intro) in zip(names, intros) {
                    new_state.hyp.insert(name.clone(), intro);
                }

                Ok(vec![Rc::new(new_state)])
            }
        }
    }

    fn solve(&mut self, state: &Rc<State>) -> Rc<RefCell<StateNode>> {
        if let Some(node) = self.visited.get(state) {
            return node.clone();
        } else {
            self.visited.insert(
                state.clone(),
                Rc::new(RefCell::new(StateNode {
                    state: state.clone(),
                    tactic_apps: Vec::new(),
                })),
            );
        }

        let tactics = if let Expression::Implication(_) = *state.goal {
            let (intros, _) = Solver::unfold_expression(state.goal.clone());
            let mut names = Vec::new();
            for intro in intros {
                names.push((self.naming)(&intro));
            }
            vec![Tactic::Intros(names)]
        } else {
            state
                .hyp
                .keys()
                .map(|name| Tactic::Apply(name.clone()))
                .collect()
        };

        let mut tactic_apps = Vec::new();
        for tactic in tactics {
            if let Ok(states) = self.use_tactic(state, &tactic) {
                tactic_apps.push(TacticApplication {
                    tactic,
                    states: states.iter().map(|new| self.solve(new)).collect(),
                })
            }
        }

        *(self.visited.get(state).unwrap().borrow_mut()) = StateNode {
            state: state.clone(),
            tactic_apps,
        };
        self.visited.get(state).unwrap().clone()
    }
}

fn find_solved(
    node: &Rc<RefCell<StateNode>>,
    visited: &mut HashSet<Rc<State>>,
    solved: &mut HashSet<Rc<State>>,
) {
    visited.insert(node.borrow().state.clone());
    for app in &node.borrow().tactic_apps {
        if app.states.is_empty() {
            solved.insert(node.borrow().state.clone());
        } else {
            let mut done = true;
            for node in &app.states {
                if !visited.contains(&node.borrow().state) {
                    find_solved(node, visited, solved);
                }
                if !solved.contains(&node.borrow().state) {
                    done = false;
                    break;
                }
            }
            if done {
                solved.insert(node.borrow().state.clone());
            }
        }
    }
}

fn prune_node(
    node: &Rc<RefCell<StateNode>>,
    pruned: &mut HashMap<Rc<State>, Rc<RefCell<StateNode>>>,
    solved: &HashSet<Rc<State>>,
) -> Rc<RefCell<StateNode>> {
    if let Some(node) = pruned.get(&node.borrow().state) {
        return node.clone();
    } else {
        pruned.insert(
            node.borrow().state.clone(),
            Rc::new(RefCell::new(StateNode {
                state: node.borrow().state.clone(),
                tactic_apps: Vec::new(),
            })),
        );
    }
    let mut tactic_apps = Vec::new();
    for app in &node.borrow().tactic_apps {
        if app.states.is_empty() {
            tactic_apps.push(app.clone());
        } else {
            let mut done = true;
            for node in &app.states {
                if !solved.contains(&node.borrow().state) {
                    done = false;
                }
            }
            if done {
                tactic_apps.push(TacticApplication {
                    tactic: app.tactic.clone(),
                    states: app
                        .states
                        .iter()
                        .map(|node| prune_node(node, pruned, solved))
                        .collect(),
                })
            }
        }
    }
    *(pruned.get(&node.borrow().state).unwrap().borrow_mut()) = StateNode {
        state: node.borrow().state.clone(),
        tactic_apps,
    };
    pruned.get(&node.borrow().state).unwrap().clone()
}

fn prune(node: Rc<RefCell<StateNode>>) -> Rc<RefCell<StateNode>> {
    let mut visited = HashSet::new();
    let mut solved = HashSet::new();
    find_solved(&node, &mut visited, &mut solved);
    let mut pruned = HashMap::new();
    prune_node(&node, &mut pruned, &solved)
}

#[derive(Debug, Clone)]
pub enum ProofStep {
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
                write!(f, ". ")
            }
            ProofStep::Apply(apply) => write!(f, "apply {}. ", apply),
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
                write!(f, " ")?;
                std::result::Result::Ok(())
            }
        }
    }
}

fn sample_proof<R: Rng + ?Sized>(state: Rc<RefCell<StateNode>>, rng: &mut R) -> Vec<ProofStep> {
    let mut proof = Vec::new();
    let mut states = vec![state];
    let mut levels = vec![(0, false)];

    while let Some(state) = states.pop() {
        let (level, bullet) = levels.pop().unwrap();

        let index = rng.gen_range(0..state.borrow().tactic_apps.len());
        let step = match state.borrow().tactic_apps[index].tactic.clone() {
            Tactic::Intros(names) => ProofStep::Intros(names),
            Tactic::Apply(hyp) => ProofStep::Apply(hyp),
        };

        if bullet {
            proof.push(ProofStep::Bullet(level));
        }
        proof.push(step);

        let next_states = &state.borrow().tactic_apps[index].states;
        for next in next_states.iter().rev() {
            states.push(next.clone());
        }
        if next_states.len() == 1 {
            levels.push((level, false));
        } else {
            for _ in 0..next_states.len() {
                levels.push((level + 1, true));
            }
        }
    }

    proof
}

#[derive(Debug, Clone)]
struct SolvedTactic {
    tactic: Tactic,
    states: Vec<Rc<State>>,
}

#[derive(Debug)]
struct TacticChecker {
    required: HashSet<Rc<State>>,
    satisfied: HashSet<Rc<State>>,
}

#[derive(Debug)]
struct RequirementChecker {
    tactics: Vec<TacticChecker>,
}

impl RequirementChecker {
    fn new(state: &Rc<RefCell<StateNode>>) -> Self {
        let mut tactics = Vec::new();
        for app in &state.borrow().tactic_apps {
            tactics.push(TacticChecker {
                required: app
                    .states
                    .iter()
                    .map(|node| node.borrow().state.clone())
                    .collect(),
                satisfied: HashSet::new(),
            })
        }
        RequirementChecker { tactics }
    }

    fn satisfied(&mut self, state: &Rc<State>) -> Option<usize> {
        for i in 0..self.tactics.len() {
            if self.tactics[i].required.contains(state) {
                self.tactics[i].satisfied.insert(state.clone());
                if self.tactics[i].required.len() == self.tactics[i].satisfied.len() {
                    return Some(i);
                }
            }
        }
        None
    }
}

fn build_shortest(
    state: &Rc<State>,
    solved: &HashMap<Rc<State>, SolvedTactic>,
) -> Rc<RefCell<StateNode>> {
    let solution = solved.get(state).unwrap();
    Rc::new(RefCell::new(StateNode {
        state: state.clone(),
        tactic_apps: vec![TacticApplication {
            tactic: solution.tactic.clone(),
            states: solution
                .states
                .iter()
                .map(|state| build_shortest(state, solved))
                .collect(),
        }],
    }))
}

fn find_shortest(state: Rc<RefCell<StateNode>>) -> Rc<RefCell<StateNode>> {
    let mut states = VecDeque::new();
    let mut solved = HashMap::new();
    let mut required: HashMap<Rc<State>, Vec<Rc<RefCell<StateNode>>>> = HashMap::new();
    let mut checker = HashMap::new();
    states.push_back(state.clone());

    while !states.is_empty() {
        let expand = states.pop_front().unwrap();
        checker
            .entry(expand.borrow().state.clone())
            .or_insert(RequirementChecker::new(&expand));

        let mut done = false;
        for app in &expand.borrow().tactic_apps {
            if app.states.is_empty() {
                solved.insert(
                    expand.borrow().state.clone(),
                    SolvedTactic {
                        tactic: app.tactic.clone(),
                        states: Vec::new(),
                    },
                );
                let mut processed = vec![expand.borrow().state.clone()];
                while let Some(current) = processed.pop() {
                    if let Some(upper) = required.get(&current) {
                        for upper in upper {
                            if let Some(index) = checker
                                .get_mut(&upper.borrow().state)
                                .unwrap()
                                .satisfied(&current)
                            {
                                processed.push(upper.borrow().state.clone());
                                let app = &upper.borrow().tactic_apps[index];
                                solved.insert(
                                    upper.borrow().state.clone(),
                                    SolvedTactic {
                                        tactic: app.tactic.clone(),
                                        states: app
                                            .states
                                            .iter()
                                            .map(|node| node.borrow().state.clone())
                                            .collect(),
                                    },
                                );
                                if upper.borrow().state == state.borrow().state {
                                    done = true;
                                }
                            }
                        }
                    }
                }
            }
            for next in &app.states {
                states.push_back(next.clone());
                required
                    .entry(next.borrow().state.clone())
                    .or_default()
                    .push(expand.clone());
            }
        }
        if done {
            break;
        }
    }

    build_shortest(&state.borrow().state, &solved)
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::{find_names, Solver, State};
    use crate::{
        parser::{parse, tokenize, Expression},
        solver::{find_shortest, prune, sample_proof},
    };
    use std::{
        collections::{BTreeMap, HashMap},
        rc::Rc,
    };

    fn check(data: &str) {
        let tokens = tokenize(data).unwrap();
        let goal = parse(tokens.as_slice()).unwrap();

        let mut solver = Solver {
            naming: Box::new(|expr: &Rc<Expression>| {
                let names = find_names(expr);
                let mut hyp = "H".to_string();
                for name in names {
                    hyp.push(name);
                }
                hyp
            }),
            visited: HashMap::new(),
        };

        let mut solution = solver.solve(&Rc::new(State {
            hyp: BTreeMap::new(),
            goal,
        }));
        println!("{}", solution.borrow());
        solution = prune(solution);

        if !solution.borrow().tactic_apps.is_empty() {
            solution = find_shortest(solution);
            let mut rng = ChaCha8Rng::from_entropy();
            let proof = sample_proof(solution, &mut rng);

            println!("{:?}", proof);
            for step in proof {
                print!("{}", step);
            }
        }
        println!();
        println!("========");
    }

    #[test]
    fn simple() {
        check("(P -> Q) -> P -> Q");
    }

    #[test]
    fn void() {
        check("(P -> Q) -> Q");
    }

    #[test]
    fn apply_loop() {
        check("(P -> P) -> P");
    }

    #[test]
    fn complex() {
        check(
            "(P -> Q) -> (P -> R) -> (T -> R) ->
            (S -> T ->  U) -> ((P -> Q) -> (P -> S)) ->
            T -> P -> U",
        );
    }

    #[test]
    fn overflow_simple() {
        check("((A -> B) -> B) -> B");
    }

    #[test]
    fn overflow_middle() {
        check("((S -> J) -> (L -> S)) -> S -> (S -> J) -> L -> S");
    }

    #[test]
    fn overflow_complex() {
        check(
            "J -> ((P -> J) -> G) -> ((S -> J) -> (L -> S)) -> S -> ((F -> G) -> G) -> 
        (S -> J) -> (G -> S) -> (G -> P) -> (S -> J) -> L -> S",
        );
    }

    #[test]
    fn stack_overflow() {
        check(
            "(O -> Z -> X -> K) -> X -> (K -> X) -> (I -> X -> K -> Z) -> (Z -> K) -> 
        ((X -> C) -> C) -> C -> (O -> Z -> X) -> I -> X -> K -> Z",
        );
    }
}
