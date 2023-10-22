use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;

use anyhow::{bail, Ok, Result};
use rexpect::session::PtySession;
use rexpect::spawn;

use crate::lexer::{tokenize, tokenize_whitespace, CoqToken, CoqTokenKind, CoqTokenSlice};
use crate::parser::{get_names, parse, CoqExpression};
use crate::project::{prepare_program, CoqProject};

static COQ_REGEX: &str = "\r\n[^< ]+ < ";

#[derive(Debug)]
enum InteractError {
    UnexpectedPhrase,
}

impl Display for InteractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            InteractError::UnexpectedPhrase => write!(f, "InteractError: unexpected phrase"),
        }
    }
}

enum CoqPhrase<'a> {
    Phrase(CoqTokenSlice<'a>),
    Bullet(CoqTokenSlice<'a>),
}

impl<'a> ToString for CoqPhrase<'a> {
    fn to_string(&self) -> String {
        match &self {
            CoqPhrase::Phrase(slice) => slice.to_string(),
            CoqPhrase::Bullet(slice) => slice.to_string(),
        }
    }
}

struct CoqPhraser<'a> {
    tokens: CoqTokenSlice<'a>,
}

impl<'a> CoqPhraser<'a> {
    fn new(tokens: CoqTokenSlice<'a>) -> Self {
        CoqPhraser { tokens }
    }

    fn definite_advance(&mut self, process: &mut PtySession) -> Result<(CoqPhrase<'a>, String)> {
        let mut index = 0;
        let query = match &self.tokens[0].kind {
            CoqTokenKind::BracketCurlyLeft | CoqTokenKind::BracketCurlyRight => {
                CoqPhrase::Bullet(self.tokens.cut(1))
            }
            CoqTokenKind::Dash | CoqTokenKind::Plus | CoqTokenKind::Star => {
                let symbol = &self.tokens[0].kind;
                while &self.tokens[index].kind == symbol && index < self.tokens.len() {
                    index += 1;
                }
                CoqPhrase::Bullet(self.tokens.cut(index))
            }
            _ => {
                while self.tokens[index].kind != CoqTokenKind::Dot && index < self.tokens.len() {
                    index += 1;
                }
                CoqPhrase::Phrase(self.tokens.cut(index + 1))
            }
        };

        process.send_line(&query.to_string())?;
        let (mut answer, _) = process.exp_regex(COQ_REGEX)?;
        answer.push('\n');
        Ok((query, answer))
    }

    fn advance(&mut self, process: &mut PtySession) -> Result<Option<(CoqPhrase<'a>, String)>> {
        if self.tokens.is_empty() {
            Ok(None)
        } else {
            Ok(Some(self.definite_advance(process)?))
        }
    }
}

#[derive(Eq, Hash, PartialEq, Clone, Copy)]
struct Index(usize);

#[derive(Eq, Hash, PartialEq, Clone)]
pub struct Name(String);

impl From<Name> for String {
    fn from(value: Name) -> Self {
        value.0
    }
}

impl From<String> for Name {
    fn from(value: String) -> Self {
        Name(value)
    }
}

#[derive(Eq, Hash, PartialEq, Clone)]
pub struct Definition(String);

impl Definition {
    pub fn from(s: String) -> Self {
        Definition(s)
    }
}

struct DefinitionStorage {
    names: HashMap<Name, Index>,
    def: HashMap<Index, Definition>,
    bag: HashMap<Definition, Index>,
    index: Index,
}

impl DefinitionStorage {
    fn new() -> Self {
        DefinitionStorage {
            names: vec!["Type", "Set", "Prop", "SProp"]
                .into_iter()
                .map(|x| (Name(x.to_string()), Index(0)))
                .collect(),
            def: HashMap::new(),
            bag: HashMap::new(),
            index: Index(1),
        }
    }

    fn contains(&self, name: &Name) -> bool {
        self.names.contains_key(name)
    }

    fn store(&mut self, name: Name, def: Definition) -> (Index, bool) {
        let (index, new) = if let Some(&ind) = self.bag.get(&def) {
            (ind, false)
        } else {
            self.bag.insert(def.clone(), self.index);
            self.def.insert(self.index, def);
            let ind = self.index;
            self.index.0 += 1;
            (ind, true)
        };
        self.names.insert(name, index);
        (index, new)
    }

    fn get(&self, index: &Index) -> Option<&Definition> {
        self.def.get(index)
    }

    fn erase(&mut self, name: Name) {
        self.names.remove(&name);
    }
}

struct State {
    definitions: Vec<String>,
    goal: String,
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for definition in &self.definitions {
            writeln!(f, "{}", definition)?;
        }
        write!(f, "{}", self.goal)
    }
}

/// Produces context needed to understand current state of proof.
/// Context contains all unfolded definitions of functions/types and proof goal
struct CoqContext {
    /// Storage of all definitions seen by CoqContext, indexed by Index
    storage: DefinitionStorage,
    /// Theorem goal
    goal: String,
    /// Definitions registered in nested sections, separated by bottom in blocks [x1 x2 ...] [y1 y2 ...] ...
    register: Vec<(Index, Name)>,
    /// Start of each registered block
    bottom: Vec<usize>,
}

impl CoqContext {
    fn new() -> Self {
        CoqContext {
            storage: DefinitionStorage::new(),
            goal: String::new(),
            register: Vec::new(),
            bottom: Vec::new(),
        }
    }

    fn open_section(&mut self) {
        self.bottom.push(self.register.len());
    }

    fn close_section(&mut self) {
        if let Some(bottom) = self.bottom.pop() {
            let length = self.register.len();
            for _ in bottom..length {
                let (_, name) = self.register.pop().unwrap();
                self.storage.erase(name);
            }
        }
    }

    fn check_name(process: &mut PtySession, name: Name) -> Result<(String, Vec<CoqToken>)> {
        process.send_line(&format!("Print {}.", String::from(name)))?;
        let (answer, _) = process.exp_regex(COQ_REGEX)?;
        let mut tokens = tokenize(&answer)?;
        tokens.push(CoqToken::new(CoqTokenKind::NewLine, 0, 0));
        Ok((answer, tokens))
    }

    fn contains(&self, name: &Name) -> bool {
        if name.0.parse::<usize>().is_ok() {
            false
        } else {
            self.storage.contains(name)
        }
    }

    fn store(&mut self, name: Name, def: Definition) -> bool {
        let (index, new) = self.storage.store(name.clone(), def);
        self.register.push((index, name));
        new
    }

    /// Unfolds definition recursively and correspondingly updates context
    fn unfold(&mut self, process: &mut PtySession, expression: &CoqExpression) -> Result<()> {
        let mut names = get_names(expression);
        while !names.is_empty() {
            let name = Name::from(names.pop().unwrap());
            if !self.contains(&name) {
                let (answer, answer_tokens) = Self::check_name(process, name.clone())?;
                if self.store(name, Definition::from(answer.clone())) {
                    let tokens = CoqTokenSlice::from(answer_tokens.as_slice());
                    for s in get_names(&parse(tokens)?) {
                        names.push(s);
                    }
                }
            }
        }
        Ok(())
    }

    /// Adds definition seen by Coq with given name
    fn add(&mut self, process: &mut PtySession, name: &str) -> Result<()> {
        let (answer, answer_tokens) = CoqContext::check_name(process, Name(name.to_string()))?;
        let expr = parse(CoqTokenSlice::from(answer_tokens.as_slice()))?;
        self.store(Name(name.to_string()), Definition::from(answer.clone()));
        self.unfold(process, &expr)
    }

    /// Get all registered definitions and current goal
    fn get_state(&self) -> State {
        let mut definitions = Vec::new();
        for (index, _) in &self.register {
            definitions.push(self.storage.get(index).unwrap().0.clone());
        }
        State {
            definitions,
            goal: self.goal.clone(),
        }
    }
}

fn init_process(project: &CoqProject) -> Result<PtySession> {
    let mut process = spawn(&prepare_program(project), Some(2000))?;
    process.exp_regex(COQ_REGEX)?;
    process.send_line("Unset Printing Notations.")?;
    process.exp_regex(COQ_REGEX)?;
    Ok(process)
}

pub fn run_file(project: &CoqProject, data: &str) -> Result<()> {
    let mut process = init_process(project)?;
    let data_tokens = tokenize(data)?;
    let mut phraser = CoqPhraser::new(CoqTokenSlice::from(data_tokens.as_slice()));
    let mut context = CoqContext::new();

    while let Some((phrase, raw_answer)) = phraser.advance(&mut process)? {
        let answer = tokenize_whitespace(&raw_answer)?;
        let expression = match phrase {
            CoqPhrase::Phrase(query) => parse(query)?,
            _ => bail!(InteractError::UnexpectedPhrase),
        };

        match &expression {
            CoqExpression::Theorem(_) => {
                let goal = parse(CoqTokenSlice::from(answer.as_slice()))?;
                context.unfold(&mut process, &goal)?;
                phraser.advance(&mut process)?.expect("expected Proof.");

                while let Some((phrase, raw_answer)) = phraser.advance(&mut process)? {
                    if let CoqPhrase::Phrase(query) = phrase {
                        if parse(query)? == CoqExpression::Qed {
                            break;
                        }
                    }
                    context.goal = raw_answer.clone();
                    println!("{}", context.get_state());
                }
            }
            CoqExpression::Inductive(inductive) => context.add(&mut process, &inductive.name)?,
            CoqExpression::Definition(definition) => context.add(&mut process, &definition.name)?,
            CoqExpression::SectionStart(_) => context.open_section(),
            CoqExpression::SectionEnd(_) => context.close_section(),
            _ => {}
        }
    }

    Ok(())
}