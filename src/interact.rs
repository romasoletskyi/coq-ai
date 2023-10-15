use std::collections::{HashMap, VecDeque};
use std::hash::Hash;

use anyhow::{Ok, Result};
use rexpect::session::PtySession;
use rexpect::spawn;

use crate::lexer::{tokenize, CoqTokenKind, CoqTokenSlice};
use crate::parser::get_names;
use crate::project::{prepare_program, CoqProject};

static COQ_REGEX: &str = "\r\n[^< ]+ < ";

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
            names: HashMap::new(),
            def: HashMap::new(),
            bag: HashMap::new(),
            index: Index(0),
        }
    }

    fn contains(&self, name: &Name) -> bool {
        self.names.contains_key(name)
    }

    fn store(&mut self, name: Name, def: Definition) {
        let index = if let Some(&ind) = self.bag.get(&def) {
            ind
        } else {
            self.bag.insert(def.clone(), self.index);
            self.def.insert(self.index, def);
            let ind = self.index;
            self.index.0 += 1;
            ind
        };
        self.names.insert(name, index);
    }
}

struct CoqContext {
    storage: DefinitionStorage,
}

impl CoqContext {
    fn new() -> Self {
        CoqContext {
            storage: DefinitionStorage::new(),
        }
    }

    fn check_name(process: &mut PtySession, name: &Name) -> Result<String> {
        process.send_line(&format!("Check {}.", String::from((*name).clone())))?;
        let (answer, _) = process.exp_regex(COQ_REGEX)?;
        Ok(answer)
    }

    fn contains(&self, name: &Name) -> bool {
        self.storage.contains(name)
    }

    fn store(&mut self, name: Name, def: Definition) {
        self.storage.store(name, def);
    }

    fn update(&mut self, process: &mut PtySession, query: CoqTokenSlice) -> Result<()> {
        let mut names = VecDeque::new();
        for name in get_names(query)? {
            names.push_back(name);
        }

        while !names.is_empty() {
            let name = Name::from(names.pop_front().unwrap());
            if !self.contains(&name) {
                let answer = Self::check_name(process, &name)?;
                self.store(name, Definition::from(answer.clone()));

                let answer_tokens = tokenize(&answer);
                let tokens = CoqTokenSlice::from(answer_tokens.as_slice());
                for s in get_names(tokens)? {
                    names.push_front(s);
                }
            }
        }

        Ok(())
    }
}

pub fn run_file(project: &CoqProject, data: &str) -> Result<()> {
    let mut process = spawn(&prepare_program(project), Some(1000))?;
    process.exp_regex(COQ_REGEX)?;

    let data_tokens = tokenize(data);
    let mut tokens = CoqTokenSlice::from(data_tokens.as_slice());
    let mut context = CoqContext::new();
    let mut index: usize = 0;

    while !tokens.is_empty() {
        index += 1;
        if tokens[index - 1].kind == CoqTokenKind::Dot {
            let query = tokens.cut(index);
            context.update(&mut process, query)?;
            process.send_line(&query.to_string())?;

            let (answer, _) = process.exp_regex(COQ_REGEX)?;
            print!("{}\n {}\n", query, answer);

            index = 0;
        }
    }

    Ok(())
}
