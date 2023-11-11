use std::collections::{HashMap, VecDeque};
use std::fmt::Display;
use std::hash::Hash;
use std::io::Write;

use anyhow::{bail, Ok, Result};
use rexpect::session::PtySession;
use rexpect::spawn;

use crate::lexer::{tokenize, CoqToken, CoqTokenKind, CoqTokenSlice};
use crate::parser;
use crate::parser::{get_names, parse_early, CoqExpression};
use crate::project::{prepare_program, CoqProject};
use crate::tactic;

static COQ_REGEX: &str = "\r\n[^< ]+ < ";

#[derive(Debug)]
enum InteractError {
    UnexpectedPhrase(CoqToken),
}

impl Display for InteractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            InteractError::UnexpectedPhrase(token) => write!(f, "InteractError: unexpected phrase at {}", token),
        }
    }
}

enum CoqPhrase<'a> {
    Phrase(CoqTokenSlice<'a>),
    Bullet(CoqTokenSlice<'a>),
}

impl<'a> CoqPhrase<'a> {
    fn slice(&self) -> CoqTokenSlice<'a> {
        match &self {
            CoqPhrase::Phrase(slice) => slice,
            CoqPhrase::Bullet(slice) => slice,
        }
        .clone()
    }
}

impl<'a> ToString for CoqPhrase<'a> {
    fn to_string(&self) -> String {
        match &self {
            CoqPhrase::Phrase(slice) => slice.to_string(),
            CoqPhrase::Bullet(slice) => slice.to_string(),
        }
    }
}

struct CoqAnswer<'a> {
    phrase: CoqPhrase<'a>,
    raw_phrase: &'a str,
    raw_answer: String,
}

struct CoqPhraser<'a> {
    data: &'a str,
    tokens: CoqTokenSlice<'a>,
    pivot: usize,
}

impl<'a> CoqPhraser<'a> {
    fn new(data: &'a str, tokens: CoqTokenSlice<'a>) -> Self {
        CoqPhraser {
            data,
            tokens,
            pivot: 0,
        }
    }

    fn skip_whitespace(&mut self) {
        let mut index = 0;
        while index < self.tokens.len() && self.tokens[index].kind == CoqTokenKind::NewLine {
            index += 1;
        }
        self.tokens.cut(index);
    }

    fn consume_until_dot(&mut self) -> CoqPhrase<'a> {
        let mut index = 0;
        while index < self.tokens.len() && self.tokens[index].kind != CoqTokenKind::Dot {
            index += 1;
        }
        CoqPhrase::Phrase(self.tokens.cut(index + 1))
    }

    fn consume_bullet(&mut self) -> CoqPhrase<'a> {
        let symbol = &self.tokens[0].kind;
        let mut index = 0;
        while index < self.tokens.len() && &self.tokens[index].kind == symbol {
            index += 1;
        }
        CoqPhrase::Bullet(self.tokens.cut(index))
    }

    fn analyze_word(&mut self, word: String) -> CoqPhrase<'a> {
        if word.parse::<usize>().is_ok() {
            if self.tokens[1].kind == CoqTokenKind::Colon {
                if self.tokens[2].kind == CoqTokenKind::BracketCurlyLeft {
                    return CoqPhrase::Bullet(self.tokens.cut(3));
                }
            }
        }
        self.consume_until_dot()
    }

    fn definite_advance(&mut self, process: &mut PtySession) -> Result<CoqAnswer<'a>> {
        let phrase = match &self.tokens[0].kind {
            CoqTokenKind::Word(word) => self.analyze_word(word.clone()),
            CoqTokenKind::BracketCurlyLeft | CoqTokenKind::BracketCurlyRight => {
                CoqPhrase::Bullet(self.tokens.cut(1))
            }
            CoqTokenKind::Dash | CoqTokenKind::Plus | CoqTokenKind::Star => self.consume_bullet(),
            _ => self.consume_until_dot(),
        };

        process.send_line(&phrase.to_string())?;
        let (mut raw_answer, _) = process.exp_regex(COQ_REGEX)?;
        raw_answer.push('\n');

        let slice = phrase.slice();
        let end = slice[slice.len() - 1].end;
        let answer = CoqAnswer {
            phrase,
            raw_phrase: &self.data[self.pivot..end],
            raw_answer,
        };

        self.pivot = end;
        Ok(answer)
    }

    fn advance(&mut self, process: &mut PtySession) -> Result<Option<CoqAnswer<'a>>> {
        self.skip_whitespace();
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

impl Name {
    fn get_printable(&self) -> &str {
        if self.0.starts_with("@") {
            &self.0[1..]
        } else {
            &self.0
        }
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Eq, Hash, PartialEq, Clone)]
struct DefinitionBody(String);

#[derive(Eq, Hash, PartialEq, Clone)]
struct Definition {
    body: DefinitionBody,
    depend: Vec<Name>,
}

struct DefinitionStorage {
    names: HashMap<Name, Index>,
    def: HashMap<Index, Definition>,
    bag: HashMap<DefinitionBody, Index>,
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

    fn contains_name(&self, name: &Name) -> bool {
        self.names.contains_key(name)
    }

    fn contains_definition(&self, def: &DefinitionBody) -> bool {
        self.bag.contains_key(def)
    }

    fn store(&mut self, name: Name, def: Definition) -> Index {
        self.bag.insert(def.body.clone(), self.index);
        self.def.insert(self.index, def);
        let index = self.index;
        self.index.0 += 1;
        self.names.insert(name, index);
        index
    }

    fn get(&self, index: &Index) -> Option<&Definition> {
        self.def.get(index)
    }

    fn erase(&mut self, name: Name) {
        self.names.remove(&name);
    }
}

/// Produces context needed to understand current state of proof.
/// Context contains all unfolded definitions of functions/types and proof goal
struct CoqContext {
    /// Storage of all definitions seen by CoqContext, indexed by Index
    storage: DefinitionStorage,
    /// Definitions registered in nested sections, separated by bottom in blocks [x1 x2 ...] [y1 y2 ...] ...
    register: Vec<(Index, Name)>,
    /// Start of each registered block
    bottom: Vec<usize>,
}

impl CoqContext {
    fn new() -> Self {
        CoqContext {
            storage: DefinitionStorage::new(),
            register: Vec::new(),
            bottom: Vec::new(),
        }
    }

    fn get_definition(&self, index: &Index) -> Option<&Definition> {
        self.storage.get(index)
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

    fn check_name(process: &mut PtySession, name: &Name) -> Result<(String, Vec<CoqToken>)> {
        set_notation(process)?;
        process.send_line(&format!("Print {}.", name.get_printable()))?;
        let (mut answer, _) = process.exp_regex(COQ_REGEX)?;
        answer = answer.split("Arguments").next().unwrap().trim().to_string();
        unset_notation(process)?;

        process.send_line(&format!("Print {}.", name.get_printable()))?;
        let (raw_answer, _) = process.exp_regex(COQ_REGEX)?;
        let mut tokens = tokenize(&raw_answer)?;
        tokens.push(CoqToken::new(CoqTokenKind::NewLine, 0, 0));

        Ok((answer, tokens))
    }

    fn contains_name(&self, name: &Name) -> bool {
        if name.0.parse::<usize>().is_ok() {
            true
        } else {
            self.storage.contains_name(name)
        }
    }

    fn contains_definition(&self, def: &DefinitionBody) -> bool {
        self.storage.contains_definition(&def)
    }

    fn store(&mut self, name: Name, def: Definition) {
        let index = self.storage.store(name.clone(), def);
        self.register.push((index, name));
    }

    /// Unfolds definition recursively and correspondingly updates context
    fn unfold(
        &mut self,
        process: &mut PtySession,
        expression: &CoqExpression,
    ) -> Result<Vec<Name>> {
        let mut names = VecDeque::new();
        for name in get_names(expression) {
            names.push_back(name);
        }
        let depend = names.iter().map(|x| Name(x.clone())).collect();
        while !names.is_empty() {
            let name = Name(names.pop_front().unwrap());
            if !self.contains_name(&name) {
                let (answer, answer_tokens) = Self::check_name(process, &name)?;
                let body = DefinitionBody(answer.clone());
                if !self.contains_definition(&body) {
                    let tokens = CoqTokenSlice::from(answer_tokens.as_slice());
                    let expr = parser::parse(tokens)?;
                    if let CoqExpression::Tactic(_) = &expr {
                        bail!(InteractError::UnexpectedPhrase(tokens[0].clone()));
                    }
                    let mut depend = Vec::new();
                    for s in get_names(&expr) {
                        depend.push(Name(s.clone()));
                        names.push_back(s);
                    }
                    self.store(name, Definition { body, depend })
                }
            }
        }
        Ok(depend)
    }

    /// Adds definition seen by Coq with given name
    fn add(&mut self, process: &mut PtySession, name: &str) -> Result<()> {
        let stored_name = Name(name.to_string());
        let (answer, answer_tokens) = Self::check_name(process, &stored_name)?;
        let expr = parser::parse(CoqTokenSlice::from(answer_tokens.as_slice()))?;
        if let CoqExpression::Tactic(_) = &expr {
            bail!(InteractError::UnexpectedPhrase(answer_tokens[0].clone()));
        }

        let depend = self.unfold(process, &expr)?;
        self.store(
            Name(name.to_string()),
            Definition {
                body: DefinitionBody(answer),
                depend,
            },
        );
        Ok(())
    }
}

struct State {
    definitions: Vec<String>,
    premise: String,
    proof: String,
    goal: String,
    tactic: String,
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<|context|> ")?;
        for definition in &self.definitions {
            writeln!(f, "{}", definition)?;
        }
        writeln!(f, "<|premise|> {}", self.premise)?;
        writeln!(f, "<|proof|> {}", self.proof)?;
        writeln!(f, "<|goal|> {}", self.goal)?;
        writeln!(f, "<|tactic|> {}", self.tactic)
    }
}

impl State {
    fn new() -> Self {
        Self {
            definitions: Vec::new(),
            premise: String::new(),
            proof: String::new(),
            goal: String::new(),
            tactic: String::new(),
        }
    }

    fn definitions(&mut self, context: &CoqContext) -> &mut Self {
    for (index, _) in context.register.iter().rev() {
            self.definitions
                .push(context.get_definition(index).unwrap().body.0.clone())
        }
        self
    }

    fn premise(&mut self, premise: &str) -> &mut Self {
        self.premise = premise.to_string();
        self
    }

    fn extend_proof(&mut self, tactic: &str) -> &mut Self {
        self.proof.push_str(tactic);
        self
    }

    fn goal(&mut self, goal: &str) -> &mut Self {
        self.goal = goal.to_string();
        self
    }

    fn tactic(&mut self, tactic: &str) -> &mut Self {
        self.tactic = tactic.to_string();
        self
    }

    fn get_tactic(&self) -> String {
        self.tactic.clone()
    }
}

fn set_notation(process: &mut PtySession) -> Result<()> {
    process.send_line("Set Printing Notations.")?;
    process.exp_regex(COQ_REGEX)?;
    Ok(())
}

fn unset_notation(process: &mut PtySession) -> Result<()> {
    process.send_line("Unset Printing Notations.")?;
    process.exp_regex(COQ_REGEX)?;
    Ok(())
}

fn init_process(project: &CoqProject) -> Result<PtySession> {
    let mut process = spawn(&prepare_program(project), Some(5000))?;
    process.exp_regex(COQ_REGEX)?;
    process.send_line("Set Printing Depth 1000.")?;
    process.exp_regex(COQ_REGEX)?;
    unset_notation(&mut process)?;
    Ok(process)
}

pub fn run_file(project: &CoqProject, data: &str, writer: &mut std::fs::File) -> Result<()> {
    let data_tokens = tokenize(data)?;
    let mut process = init_process(project)?;
    let mut phraser = CoqPhraser::new(data, CoqTokenSlice::from(data_tokens.as_slice()));
    let mut context = CoqContext::new();

    while let Some(CoqAnswer {
        phrase,
        raw_phrase,
        raw_answer,
    }) = phraser.advance(&mut process)?
    {
        let answer = tokenize(&raw_answer)?;
        let expression = match phrase {
            CoqPhrase::Phrase(query) => parse_early(query)?,
            _ => bail!(InteractError::UnexpectedPhrase(answer[0].clone())),
        };

        match &expression {
            CoqExpression::Theorem(_) => {
                let goal = parser::parse(CoqTokenSlice::from(answer.as_slice()))?;
                context.open_section();
                context.unfold(&mut process, &goal)?;

                let mut state = State::new();
                state
                    .definitions(&context)
                    .premise(&raw_phrase)
                    .goal(&raw_answer)
                    .tactic("Proof.");
                writeln!(writer, "{}", state).unwrap();

                phraser.advance(&mut process)?.expect("expected Proof.");
                let mut previous_goal = String::new();
                set_notation(&mut process)?;

                while let Some(CoqAnswer {
                    phrase,
                    raw_phrase,
                    raw_answer,
                }) = phraser.advance(&mut process)?
                {
                    if let CoqPhrase::Phrase(query) = phrase {
                        match parser::parse(query)? {
                            CoqExpression::Qed => break,
                            CoqExpression::Tactic(query) => {
                                //let tactic = tactic::parse(CoqTokenSlice::from(query.as_slice()))?;
                                //println!("{:?}", tactic);
                            }
                            _ => bail!(InteractError::UnexpectedPhrase(query[0].clone())),
                        }
                    }

                    let tactic = state.get_tactic();
                    state
                        .extend_proof(&tactic)
                        .goal(&previous_goal)
                        .tactic(&raw_phrase);
                    previous_goal = raw_answer.trim().to_string();
                    writeln!(writer, "{}", state).unwrap();
                }
                unset_notation(&mut process)?;
                context.close_section();
            }
            CoqExpression::Assumption(assumption) => {
                for name in &assumption.names {
                    context.add(&mut process, name)?;
                }
            }
            CoqExpression::Inductive(inductive) => context.add(&mut process, &inductive.name)?,
            CoqExpression::Definition(definition) => context.add(&mut process, &definition.name)?,
            CoqExpression::Fixpoint(fixpoint) => context.add(&mut process, &fixpoint.name)?,
            CoqExpression::SectionStart(_) => context.open_section(),
            CoqExpression::SectionEnd(_) => context.close_section(),
            CoqExpression::From | CoqExpression::Set | CoqExpression::Unset | CoqExpression::Import(_) => {}
            _ => bail!(InteractError::UnexpectedPhrase(answer[0].clone())),
        }
    }

    Ok(())
}
