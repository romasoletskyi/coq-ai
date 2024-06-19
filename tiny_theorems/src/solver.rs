use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Display;
use std::io::Write;
use std::iter::zip;
use std::sync::Arc;

use anyhow::{bail, Result};

use crate::gen::Statement;
use crate::parser::Expression;

/* During each step of proof we have a state [H |- goal] consisting of
premises H and a single goal. Using tactics we can change the state
by either changing premises H (for instance, destruct H) or goal.
After applying tactic we can have one or multiple goals to solve.

For instance [HP: P |- P] is solved as
[HP: P |- P] => apply HP => [] - we have no further goals.

It may happen so that there are several goals which do not bring us closer
[H: Q -> P -> P |- P] => apply H => [H: Q -> P -> P |- Q]
                                 => [H: Q -> P -> P |- P]

After constructing a full graph of states we can collect shortest proof
using breadth-first search. */

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State {
    pub hyp: BTreeMap<String, Arc<Expression>>,
    context: BTreeSet<Arc<Expression>>,
    pub goal: Arc<Expression>,
}

impl State {
    pub fn new(goal: Arc<Expression>) -> State {
        State {
            hyp: BTreeMap::new(),
            context: BTreeSet::new(),
            goal,
        }
    }

    pub fn from_statement(namer: &mut Namer, statement: &Statement) -> State {
        State {
            hyp: statement
                .hyp
                .iter()
                .map(|x| (namer(x), x.clone()))
                .collect(),
            context: BTreeSet::new(),
            goal: statement.goal.clone(),
        }
    }
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

pub fn print_state(buf: &mut dyn Write, state: &State) -> Result<()> {
    writeln!(buf, "[HYP]")?;
    for (name, hyp) in &state.hyp {
        writeln!(buf, "{}: {}", name, hyp)?;
    }
    Ok(write!(buf, "[GOAL]\n{}\n[TACTIC]\n", state.goal)?)
}

#[derive(Debug, Clone)]
pub enum Tactic {
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

impl From<ProofStep> for Option<Tactic> {
    fn from(value: ProofStep) -> Self {
        match value {
            ProofStep::Apply(hyp) => Some(Tactic::Apply(hyp)),
            ProofStep::Intros(intros) => Some(Tactic::Intros(intros)),
            _ => None,
        }
    }
}

pub fn unfold_expression(mut expr: Arc<Expression>) -> (Vec<Arc<Expression>>, Arc<Expression>) {
    let mut premise = Vec::new();
    while let Expression::Implication(imp) = &*expr {
        premise.push(imp.left.clone());
        expr = imp.right.clone();
    }
    (premise, expr)
}

pub fn use_tactic(state: &State, tactic: &Tactic) -> Result<Vec<Arc<State>>> {
    match tactic {
        Tactic::Apply(name) => {
            let hyp = if let Some(hyp) = state.hyp.get(name) {
                hyp
            } else {
                bail!(TacticError::WrongName(name.clone()));
            }
            .clone();

            let (to_prove, hyp) = unfold_expression(hyp);
            if hyp != state.goal {
                bail!(TacticError::WrongHypothesis);
            }

            Ok(to_prove
                .iter()
                .map(|goal| {
                    Arc::new(State {
                        hyp: state.hyp.clone(),
                        context: state.context.clone(),
                        goal: goal.clone(),
                    })
                })
                .collect())
        }
        Tactic::Intros(names) => {
            let (intros, goal) = unfold_expression(state.goal.clone());
            let mut new_state = state.clone();
            new_state.goal = goal;

            for (name, intro) in zip(names, intros) {
                if !new_state.context.contains(&intro) {
                    new_state.hyp.insert(name.clone(), intro.clone());
                    new_state.context.insert(intro);
                }
            }

            Ok(vec![Arc::new(new_state)])
        }
    }
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
                writeln!(f)?;
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

// A common util for hypothesis naming

fn search_names(props: &mut Vec<char>, expr: &Arc<Expression>) {
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

pub fn find_names(expr: &Arc<Expression>) -> Vec<char> {
    let mut props = Vec::new();
    search_names(&mut props, expr);
    props
}

type Namer = Box<dyn FnMut(&Arc<Expression>) -> String>;

pub fn name_simple_hypothesis() -> Namer {
    let mut storage: HashSet<String> = HashSet::new();
    Box::new(move |expr| {
        let names = find_names(expr);
        let mut hyp = "H".to_string();
        for name in names {
            hyp.push(name);
        }
        let mut index = 0;
        let mut extension = String::new();
        loop {
            if storage.contains(&hyp) {
                for _ in 0..extension.len() {
                    hyp.pop().unwrap();
                }
                extension = index.to_string();
                hyp.push_str(&extension);
                index += 1;
            } else {
                storage.insert(hyp.clone());
                return hyp;
            }
        }
    })
}

struct TacticApplication {
    tactic: Tactic,
    states: Vec<Arc<State>>,
}

#[derive(Debug)]
struct TacticChecker {
    required: HashSet<Arc<State>>,
    satisfied: HashSet<Arc<State>>,
}

#[derive(Debug)]
struct RequirementChecker {
    tactics: Vec<TacticChecker>,
    solution: Option<usize>,
}

impl RequirementChecker {
    fn new(tactic_apps: &Vec<TacticApplication>) -> Self {
        let mut tactics = Vec::new();
        for app in tactic_apps {
            tactics.push(TacticChecker {
                required: app.states.iter().cloned().collect(),
                satisfied: HashSet::new(),
            })
        }
        RequirementChecker {
            tactics,
            solution: None,
        }
    }

    fn satisfied(&mut self, state: &Arc<State>) {
        if self.solution.is_some() {
            return;
        }
        for i in 0..self.tactics.len() {
            if self.tactics[i].required.contains(state) {
                self.tactics[i].satisfied.insert(state.clone());
                if self.tactics[i].required.len() == self.tactics[i].satisfied.len() {
                    self.solution = Some(i);
                    return;
                }
            }
        }
    }
}

pub struct Solver {
    naming: Namer,
    states: HashMap<Arc<State>, Vec<TacticApplication>>,
}

impl Solver {
    fn new(naming: Namer) -> Self {
        Solver {
            naming,
            states: HashMap::new(),
        }
    }

    fn sample_proof(
        &self,
        solved: HashMap<Arc<State>, usize>,
        state: &Arc<State>,
    ) -> Vec<ProofStep> {
        let mut proof = Vec::new();
        let mut states = vec![state.clone()];
        let mut levels = vec![(0, false)];

        while let Some(state) = states.pop() {
            let (level, bullet) = levels.pop().unwrap();
            let tactic_apps = self.states.get(&state).unwrap();
            let index = *solved.get(&state).unwrap();

            let step = match &tactic_apps[index].tactic {
                Tactic::Intros(names) => ProofStep::Intros(names.clone()),
                Tactic::Apply(hyp) => ProofStep::Apply(hyp.clone()),
            };

            if bullet {
                proof.push(ProofStep::Bullet(level));
            }
            proof.push(step);

            let next_states = &tactic_apps[index].states;
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

    fn find_shortest(&mut self, state: &Arc<State>) -> Vec<ProofStep> {
        let mut order = VecDeque::new();
        let mut solved = HashMap::new();
        let mut required: HashMap<_, Vec<_>> = HashMap::new();
        let mut checker = HashMap::new();
        order.push_back(state.clone());

        while let Some(expand) = order.pop_front() {
            if !self.states.contains_key(&expand) {
                let tactics = if let Expression::Implication(_) = *expand.goal {
                    let (intros, _) = unfold_expression(expand.goal.clone());
                    let mut names = Vec::new();
                    for intro in intros {
                        names.push((self.naming)(&intro));
                    }
                    vec![Tactic::Intros(names)]
                } else {
                    expand
                        .hyp
                        .keys()
                        .map(|name| Tactic::Apply(name.clone()))
                        .collect()
                };

                let mut tactic_apps = Vec::new();
                for tactic in tactics {
                    if let Ok(states) = use_tactic(&expand, &tactic) {
                        for state in &states {
                            required
                                .entry(state.clone())
                                .or_default()
                                .push(expand.clone());
                        }
                        if states.is_empty() {
                            solved.insert(expand.clone(), tactic_apps.len());
                        }
                        tactic_apps.push(TacticApplication { tactic, states })
                    }
                }

                checker.insert(expand.clone(), RequirementChecker::new(&tactic_apps));
                self.states.insert(expand.clone(), tactic_apps);
            }

            let tactic_apps = self.states.get(&expand).unwrap();
            if let Some(&index) = solved.get(&expand) {
                for state in &tactic_apps[index].states {
                    order.push_back(state.clone());
                }

                let mut states = vec![expand.clone()];
                let mut solved_states = states.clone();

                while let Some(state) = states.pop() {
                    if let Some(candidates) = required.get(&state) {
                        for candidate in candidates {
                            if !solved.contains_key(candidate) {
                                let check = checker.get_mut(candidate).unwrap();
                                for solved_state in &solved_states {
                                    check.satisfied(solved_state);
                                }
                                if let Some(candidate_index) = check.solution {
                                    solved.insert(candidate.clone(), candidate_index);
                                    solved_states.push(candidate.clone());
                                    states.push(candidate.clone());
                                }
                            }
                        }
                    }
                }
            } else {
                for app in tactic_apps {
                    for state in &app.states {
                        order.push_back(state.clone());
                    }
                }
            }

            if solved.contains_key(state) {
                break;
            }
        }

        self.sample_proof(solved, state)
    }
}

pub fn get_proof(goal: Arc<Expression>) -> Vec<ProofStep> {
    let mut solver = Solver::new(name_simple_hypothesis());
    solver.find_shortest(&Arc::new(State {
        hyp: BTreeMap::new(),
        context: BTreeSet::new(),
        goal,
    }))
}

#[cfg(test)]
mod tests {
    use super::{Solver, State};
    use crate::{
        parser::{parse, tokenize},
        solver::name_simple_hypothesis,
    };
    use std::{
        collections::{BTreeMap, BTreeSet},
        sync::Arc,
    };

    fn check(data: &str) {
        let tokens = tokenize(data).unwrap();
        let goal = parse(tokens.as_slice()).unwrap();

        let mut solver = Solver::new(name_simple_hypothesis());
        let proof = solver.find_shortest(&Arc::new(State::new(goal)));

        println!("{:?}", proof);
        for step in proof {
            print!("{}", step);
        }

        println!();
        println!("========");
    }

    #[test]
    fn memory() {
        for _ in 0..10000 {
            let tokens = tokenize("M -> ((O -> M) -> S) -> (S -> N -> R) -> (S -> M -> N) -> (S -> R -> O) -> (M -> S) -> (O -> R) -> O").unwrap();
            let goal = parse(tokens.as_slice()).unwrap();

            let mut solver = Solver::new(name_simple_hypothesis());
            solver.find_shortest(&Arc::new(State {
                hyp: BTreeMap::new(),
                context: BTreeSet::new(),
                goal,
            }));
        }
    }

    #[test]
    fn simple() {
        check("(P -> Q) -> P -> Q");
    }

    #[test]
    fn repeat() {
        check("M -> ((M -> R) -> R) -> R -> R");
    }

    #[test]
    fn implication() {
        check("(A -> B) -> A -> (D -> B) -> ((C -> D) -> D) -> B");
    }

    #[test]
    fn implication_triple() {
        check("M -> (M -> R) -> (R -> M) -> (M -> R -> S) -> S");
    }

    #[test]
    fn implication_chain() {
        check("M -> (M -> R) -> (R -> S) -> (S -> R) -> S");
    }

    #[test]
    fn implication_chain_complex() {
        check("R -> (M -> R -> S) -> (R -> M) -> (M -> S -> R) -> (M -> R) -> S");
    }

    #[test]
    fn implication_intermediate_goal() {
        check("M -> ((M -> S) -> R) -> S -> R");
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
    fn long() {
        check("M -> ((O -> M) -> S) -> (S -> N -> R) -> (S -> M -> N) -> (S -> R -> O) -> (M -> S) -> (O -> R) -> O");
    }

    #[test]
    fn tricky() {
        check("M -> (N -> S) -> ((N -> S) -> N) -> S");
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

    #[test]
    fn double() {
        check("((A -> D) -> B -> C) -> ((B -> C) -> B) -> ((C -> B) -> B) -> (A -> D) -> (B -> C -> A) -> A");
        check("((A -> D) -> B -> C) -> ((B -> C) -> B) -> ((C -> B) -> B) -> (A -> D) -> (B -> C -> A) -> A");
    }

    #[test]
    fn proper_naming() {
        check("((A -> B) -> D) -> ((A -> D) -> A -> C) -> (A -> B) -> A -> C");
    }
}
