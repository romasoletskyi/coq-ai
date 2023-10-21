use anyhow::{bail, Ok, Result};
use std::{collections::HashSet, fmt::Display};

use crate::lexer::{CoqToken, CoqTokenKind, CoqTokenSlice};

#[derive(Debug)]
enum ParserError {
    Eof,
    UnexpectedToken(CoqToken),
    UnexpectedQuery,
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParserError::Eof => write!(f, "EOF"),
            ParserError::UnexpectedToken(token) => write!(f, "unexpected token {}", token),
            ParserError::UnexpectedQuery => write!(f, "unexpected query"),
        }
    }
}

#[derive(Debug, PartialEq)]
struct SimpleBinder {
    name: String,
}

impl Display for SimpleBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, PartialEq)]
struct ExplicitBinder {
    names: Vec<String>,
    term: Box<Type>,
}

impl Display for ExplicitBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for name in &self.names {
            write!(f, "{} ", name)?;
        }
        write!(f, ": {})", *self.term)
    }
}

#[derive(Debug, PartialEq)]
struct ImplicitBinder {
    names: Vec<String>,
    term: Option<Box<Type>>,
}

impl Display for ImplicitBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for i in 0..self.names.len() - 1 {
            write!(f, "{} ", self.names[i])?;
        }
        write!(f, "{}", self.names[self.names.len() - 1])?;
        if let Some(term) = &self.term {
            write!(f, " : {}", *term)?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, PartialEq)]
enum Binder {
    Simple(SimpleBinder),
    Explicit(ExplicitBinder),
    Implicit(ImplicitBinder),
}

impl Display for Binder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Binder::Simple(binder) => write!(f, "{}", binder),
            Binder::Explicit(binder) => write!(f, "{}", binder),
            Binder::Implicit(binder) => write!(f, "{}", binder),
        }
    }
}

#[derive(Debug, PartialEq)]
struct OpenBinder {
    names: Vec<String>,
    term: Box<Type>,
}

impl Display for OpenBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for name in &self.names {
            write!(f, "{} ", name)?;
        }
        write!(f, ": {}", *self.term)
    }
}

#[derive(Debug, PartialEq)]
struct Binders {
    binders: Vec<Binder>,
}

impl Display for Binders {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for binder in &self.binders {
            write!(f, "{} ", binder)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, PartialEq)]
enum OpenBinders {
    OpenBinder(OpenBinder),
    Binders(Binders),
}

impl Display for OpenBinders {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpenBinders::OpenBinder(binder) => write!(f, "{}", binder),
            OpenBinders::Binders(binders) => write!(f, "{}", binders),
        }
    }
}

#[derive(Debug, PartialEq)]
enum QuantifierToken {
    ForAll,
    Exists,
}

impl Display for QuantifierToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuantifierToken::ForAll => write!(f, "forall"),
            QuantifierToken::Exists => write!(f, "exists"),
        }
    }
}

impl TryFrom<&CoqToken> for QuantifierToken {
    type Error = anyhow::Error;

    fn try_from(value: &CoqToken) -> std::result::Result<Self, Self::Error> {
        match &value.kind {
            CoqTokenKind::Word(word) => match word.as_str() {
                "forall" => Ok(QuantifierToken::ForAll),
                "exists" => Ok(QuantifierToken::Exists),
                _ => bail!(ParserError::UnexpectedToken(value.clone())),
            },
            _ => bail!(ParserError::UnexpectedToken(value.clone())),
        }
    }
}

#[derive(Debug, PartialEq)]
struct Quantifier {
    token: QuantifierToken,
    binder: Box<OpenBinders>,
    has: Box<Type>,
}

impl Display for Quantifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}, {}", self.token, self.binder, self.has)
    }
}

#[derive(Debug, PartialEq)]
struct Fun {
    from: Box<Type>,
    to: Box<Type>,
}

impl Display for Fun {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} -> {}", *self.from, *self.to)
    }
}

#[derive(Debug, PartialEq)]
enum Type {
    Quantifier(Quantifier),
    Fun(Fun),
    Custom(Vec<CoqToken>),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Quantifier(term) => write!(f, "{}", term),
            Type::Fun(term) => write!(f, "{}", term),
            Type::Custom(tokens) => write!(f, "{}", CoqTokenSlice::from(tokens.as_slice())),
        }
    }
}

#[derive(Debug, PartialEq)]
enum TheoremToken {
    Theorem,
    Lemma,
    Fact,
    Remark,
    Corollary,
    Proposition,
    Property,
}

impl TryFrom<&CoqToken> for TheoremToken {
    type Error = anyhow::Error;

    fn try_from(value: &CoqToken) -> std::result::Result<Self, Self::Error> {
        match &value.kind {
            CoqTokenKind::Word(word) => match word.as_str() {
                "Theorem" => Ok(TheoremToken::Theorem),
                "Lemma" => Ok(TheoremToken::Lemma),
                "Fact" => Ok(TheoremToken::Fact),
                "Remark" => Ok(TheoremToken::Remark),
                "Corollary" => Ok(TheoremToken::Corollary),
                "Proposition" => Ok(TheoremToken::Proposition),
                "Property" => Ok(TheoremToken::Property),
                _ => bail!(ParserError::UnexpectedToken(value.clone())),
            },
            _ => bail!(ParserError::UnexpectedToken(value.clone())),
        }
    }
}

impl Display for TheoremToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            TheoremToken::Theorem => write!(f, "Theorem"),
            TheoremToken::Lemma => write!(f, "Lemma"),
            TheoremToken::Fact => write!(f, "Fact"),
            TheoremToken::Remark => write!(f, "Remark"),
            TheoremToken::Corollary => write!(f, "Corollary"),
            TheoremToken::Proposition => write!(f, "Proposition"),
            TheoremToken::Property => write!(f, "Property"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Theorem {
    token: TheoremToken,
    name: String,
    binders: Vec<Binder>,
    term: Box<Type>,
}

impl Display for Theorem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.token, self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        write!(f, " : {}", self.term)
    }
}

#[derive(Debug, PartialEq)]
struct Constructor {
    name: String,
    binders: Vec<Binder>,
    term: Option<Box<Type>>,
}

impl Display for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        if let Some(term) = &self.term {
            write!(f, " : {}", term)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub struct Inductive {
    pub name: String,
    binders: Vec<Binder>,
    term: Box<Type>,
    constructors: Vec<Constructor>,
}

impl Display for Inductive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Inductive {}", self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        write!(f, " : {} := ", self.term)?;
        for i in 0..self.constructors.len() - 1 {
            write!(f, "{} |", self.constructors[i])?;
        }
        write!(f, " {}.", self.constructors[self.constructors.len() - 1])
    }
}

#[derive(Debug, PartialEq)]
enum DefinitionToken {
    Definition,
    Example,
}

impl Display for DefinitionToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            DefinitionToken::Definition => write!(f, "Definition"),
            DefinitionToken::Example => write!(f, "Example"),
        }
    }
}

impl TryFrom<&CoqToken> for DefinitionToken {
    type Error = anyhow::Error;

    fn try_from(value: &CoqToken) -> std::result::Result<Self, Self::Error> {
        match &value.kind {
            CoqTokenKind::Word(word) => match word.as_str() {
                "Definition" => Ok(DefinitionToken::Definition),
                "Example" => Ok(DefinitionToken::Example),
                _ => bail!(ParserError::UnexpectedToken(value.clone())),
            },
            _ => bail!(ParserError::UnexpectedToken(value.clone())),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Definition {
    token: DefinitionToken,
    pub name: String,
    binders: Vec<Binder>,
    sort: Option<Box<Type>>,
    term: Box<Type>,
}

impl Display for Definition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.token, self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        if let Some(sort) = &self.sort {
            write!(f, " : {}", sort)?;
        }
        write!(f, " := {}", self.term)
    }
}

#[derive(Debug, PartialEq)]
struct Hypothesis {
    name: String,
    term: Box<Type>,
}

impl Display for Hypothesis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.name, self.term)
    }
}

#[derive(Debug, PartialEq)]
pub struct Goal {
    premise: Vec<Hypothesis>,
    conclusion: Box<Type>,
}

impl Display for Goal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for hypothesis in &self.premise {
            writeln!(f, "{}", hypothesis)?;
        }
        writeln!(f, "============================")?;
        write!(f, "{}", self.conclusion)
    }
}

#[derive(Debug, PartialEq)]
pub enum CoqExpression {
    Theorem(Theorem),
    Inductive(Inductive),
    Definition(Definition),
    Goal(Vec<Goal>),
    SectionStart(String),
    SectionEnd(String),
    Proof,
    Qed,
}

impl Display for CoqExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            CoqExpression::Theorem(theorem) => write!(f, "{}", theorem),
            CoqExpression::Inductive(inductive) => write!(f, "{}", inductive),
            CoqExpression::Definition(definition) => write!(f, "{}", definition),
            CoqExpression::Goal(goals) => {
                write!(
                    f,
                    "{} {}\n\n",
                    goals.len(),
                    if goals.len() > 1 { "goals" } else { "goal" }
                )?;
                for goal in goals {
                    writeln!(f, "{}", goal)?;
                }
                std::fmt::Result::Ok(())
            }
            CoqExpression::SectionStart(name) => write!(f, "Section {}", name),
            CoqExpression::SectionEnd(name) => write!(f, "End {}", name),
            CoqExpression::Proof => write!(f, "Proof"),
            CoqExpression::Qed => write!(f, "Qed"),
        }
    }
}

struct CoqParser<'a> {
    index: usize,
    slice: CoqTokenSlice<'a>,
}

impl<'a> CoqParser<'a> {
    fn new(slice: CoqTokenSlice<'a>) -> Self {
        CoqParser { index: 0, slice }
    }

    fn current(&self) -> Result<&CoqToken> {
        if self.index >= self.slice.len() {
            bail!(ParserError::Eof);
        }
        Ok(&self.slice[self.index])
    }

    fn advance(&mut self) {
        self.index += 1;
    }

    fn skip_line(&mut self) {
        while self.slice[self.index].kind != CoqTokenKind::NewLine && self.index < self.slice.len()
        {
            self.advance();
        }
        self.advance();
    }

    /// parses type and puts carret on next token
    fn parse_type(&mut self, pred: fn(&CoqTokenKind) -> bool) -> Result<Box<Type>> {
        if let CoqTokenKind::Word(word) = &self.current()?.kind {
            if let std::result::Result::Ok(token) = QuantifierToken::try_from(self.current()?) {
                self.advance();
                let binder = Box::new(self.parse_open_binder()?);
                self.advance();
                return Ok(Box::new(Type::Quantifier(Quantifier {
                    token,
                    binder,
                    has: self.parse_type(pred)?,
                })));
            }
        }

        if let CoqTokenKind::BracketLeft = &self.current()?.kind {
            self.advance();
            let term = self.parse_type(|kind| &CoqTokenKind::BracketRight == kind)?;
            self.advance();

            if pred(&self.current()?.kind) {
                return Ok(term);
            } else if CoqTokenKind::Arrow == self.current()?.kind {
                self.advance();
                return Ok(Box::new(Type::Fun(Fun {
                    from: term,
                    to: self.parse_type(pred)?,
                })));
            }
            bail!(ParserError::UnexpectedToken(self.current()?.clone()))
        }

        let mut tokens = Vec::new();
        loop {
            let token = self.current()?;
            if CoqTokenKind::Arrow == token.kind {
                let from = Box::new(Type::Custom(tokens));
                self.advance();
                return Ok(Box::new(Type::Fun(Fun {
                    from,
                    to: self.parse_type(pred)?,
                })));
            } else if pred(&token.kind) {
                return Ok(Box::new(Type::Custom(tokens)));
            }
            tokens.push(token.clone());
            self.advance();
        }
    }

    fn parse_name(&mut self) -> Result<String> {
        let token = self.current()?;
        if let CoqTokenKind::Word(name) = &token.kind {
            Ok(name.clone())
        } else {
            bail!(ParserError::UnexpectedToken(token.clone()));
        }
    }

    fn parse_binder(&mut self) -> Result<Binder> {
        match &self.current()?.kind {
            CoqTokenKind::Word(name) => Ok(Binder::Simple(SimpleBinder { name: name.clone() })),
            CoqTokenKind::BracketLeft => {
                let mut names = Vec::new();
                loop {
                    self.advance();
                    if self.current()?.kind == CoqTokenKind::Colon {
                        break;
                    }
                    names.push(self.parse_name()?);
                }

                self.advance();
                let term = self.parse_type(|token| &CoqTokenKind::BracketRight == token)?;

                self.advance();
                Ok(Binder::Explicit(ExplicitBinder { names, term }))
            }
            CoqTokenKind::BracketCurlyLeft => {
                let mut seen_colon = false;
                let mut names = Vec::new();
                loop {
                    self.advance();
                    let kind = &self.current()?.kind;
                    if kind == &CoqTokenKind::Colon {
                        seen_colon = true;
                        break;
                    } else if kind == &CoqTokenKind::BracketCurlyRight {
                        break;
                    }
                    names.push(self.parse_name()?);
                }

                self.advance();
                let term = if seen_colon {
                    let term =
                        self.parse_type(|token| &CoqTokenKind::BracketCurlyRight == token)?;
                    self.advance();
                    Some(term)
                } else {
                    None
                };

                Ok(Binder::Implicit(ImplicitBinder { names, term }))
            }
            _ => bail!(ParserError::UnexpectedToken(self.current()?.clone())),
        }
    }

    fn parse_open_binder(&mut self) -> Result<OpenBinders> {
        let mut names = Vec::new();
        while let CoqTokenKind::Word(_) = &self.current()?.kind {
            let name = self.parse_name()?;
            self.advance();
            names.push(name);
        }

        //  we suppose that open_binders are used only as:
        //      forall (open_binders), (type)
        if CoqTokenKind::Colon == self.current()?.kind {
            self.advance();
            let term = self.parse_type(|token| &CoqTokenKind::Comma == token)?;
            Ok(OpenBinders::OpenBinder(OpenBinder { names, term }))
        } else {
            let binders = if names.is_empty() {
                let mut binders = Vec::new();
                while CoqTokenKind::Comma != self.current()?.kind {
                    binders.push(self.parse_binder()?);
                }
                binders
            } else {
                names
                    .iter()
                    .map(|name| Binder::Simple(SimpleBinder { name: name.clone() }))
                    .collect()
            };
            Ok(OpenBinders::Binders(Binders { binders }))
        }
    }

    fn parse_theorem(&mut self, token: TheoremToken) -> Result<Theorem> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            let mut binders = Vec::new();
            while CoqTokenKind::Colon != self.current()?.kind {
                binders.push(self.parse_binder()?);
            }

            self.advance();
            return Ok(Theorem {
                token,
                binders,
                name,
                term: self.parse_type(|token| &CoqTokenKind::Dot == token)?,
            });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_constructor(&mut self) -> Result<Constructor> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            let mut binders = Vec::new();
            while CoqTokenKind::Colon != self.current()?.kind {
                binders.push(self.parse_binder()?);
            }

            let pred =
                |token: &CoqTokenKind| &CoqTokenKind::Dot == token || &CoqTokenKind::Pipe == token;
            let term = if pred(&self.current()?.kind) {
                None
            } else {
                if CoqTokenKind::Colon != self.current()?.kind {
                    bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                }
                self.advance();
                Some(self.parse_type(pred)?)
            };

            return Ok(Constructor {
                name,
                binders,
                term,
            });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_inductive(&mut self) -> Result<Inductive> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            let mut binders = Vec::new();
            while CoqTokenKind::Colon != self.current()?.kind {
                binders.push(self.parse_binder()?);
            }

            self.advance();
            let term = self.parse_type(|token| &CoqTokenKind::Define == token)?;
            self.advance();

            let mut constructors = Vec::new();
            while CoqTokenKind::Dot != self.current()?.kind {
                if CoqTokenKind::Pipe == self.current()?.kind {
                    self.advance();
                }
                constructors.push(self.parse_constructor()?);
            }

            return Ok(Inductive {
                name,
                binders,
                term,
                constructors,
            });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_definition(&mut self, token: DefinitionToken) -> Result<Definition> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            let mut binders = Vec::new();

            while self.current()?.kind != CoqTokenKind::Define
                && self.current()?.kind != CoqTokenKind::Colon
            {
                binders.push(self.parse_binder()?);
            }

            let sort = if self.current()?.kind == CoqTokenKind::Colon {
                self.advance();
                Some(self.parse_type(|token| token == &CoqTokenKind::Define)?)
            } else {
                None
            };

            self.advance();
            let term = self.parse_type(|token| token == &CoqTokenKind::Dot)?;

            return Ok(Definition {
                token,
                name,
                binders,
                sort,
                term,
            });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_hypothesis(&mut self) -> Result<Hypothesis> {
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            self.advance();
            let term = self.parse_type(|token| token == &CoqTokenKind::NewLine)?;
            self.advance();
            return Ok(Hypothesis { name, term });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_goal(&mut self) -> Result<Goal> {
        let mut premise = Vec::new();
        while (self.current()?.kind != CoqTokenKind::Eq) {
            premise.push(self.parse_hypothesis()?);
        }
        self.skip_line();
        let conclusion = self.parse_type(|token| token == &CoqTokenKind::NewLine)?;
        self.advance();
        Ok(Goal {
            premise,
            conclusion,
        })
    }

    fn parse_goals(&mut self, number: usize) -> Result<Vec<Goal>> {
        self.skip_line();
        let mut goals = Vec::new();
        goals.push(self.parse_goal()?);

        for _ in 1..number {
            self.skip_line();
            let conclusion = self.parse_type(|token| token == &CoqTokenKind::NewLine)?;
            self.advance();
            goals.push(Goal {
                premise: Vec::new(),
                conclusion,
            });
        }

        Ok(goals)
    }

    fn parse_expression(&mut self) -> Result<CoqExpression> {
        let token = self.current()?;
        if let CoqTokenKind::Word(word) = &token.kind {
            if let std::result::Result::Ok(token) = TheoremToken::try_from(token) {
                return Ok(CoqExpression::Theorem(self.parse_theorem(token)?));
            }
            if let std::result::Result::Ok(token) = DefinitionToken::try_from(token) {
                return Ok(CoqExpression::Definition(self.parse_definition(token)?));
            }
            if let std::result::Result::Ok(number) = word.parse::<usize>() {
                return Ok(CoqExpression::Goal(self.parse_goals(number)?));
            }
            match word.as_str() {
                "Inductive" => return Ok(CoqExpression::Inductive(self.parse_inductive()?)),
                "Section" => {
                    self.advance();
                    return Ok(CoqExpression::SectionStart(self.parse_name()?));
                }
                "End" => {
                    self.advance();
                    return Ok(CoqExpression::SectionEnd(self.parse_name()?));
                }
                "Proof" => Ok(CoqExpression::Proof),
                "Qed" => Ok(CoqExpression::Qed),
                _ => bail!(ParserError::UnexpectedQuery),
            }?;
        }
        bail!(ParserError::UnexpectedQuery);
    }
}

/// Collector for gathering names within Coq expressions
struct NameCollector {
    known: HashSet<String>,
    seen: HashSet<String>,
    register: Vec<String>,
    bottom: Vec<usize>,
}

impl NameCollector {
    fn new() -> Self {
        NameCollector {
            known: HashSet::new(),
            seen: HashSet::new(),
            register: Vec::new(),
            bottom: Vec::new(),
        }
    }

    fn open(&mut self) {
        self.bottom.push(self.register.len());
    }

    fn register(&mut self, name: &String) {
        if !self.known.contains(name) {
            self.known.insert(name.clone());
            self.register.push(name.clone());
        }
    }

    fn see(&mut self, word: &String) {
        if !self.known.contains(word) && !self.seen.contains(word) {
            self.seen.insert(word.clone());
        }
    }

    fn close(&mut self) {
        if let Some(until) = self.bottom.pop() {
            let length = self.register.len();
            for _ in until..length {
                let name = self.register.pop().unwrap();
                self.known.remove(&name);
            }
        }
    }

    fn collect(mut self) -> Vec<String> {
        self.seen.drain().collect()
    }

    fn get_binder_names(&mut self, binder: &Binder) {
        match binder {
            Binder::Explicit(explicit) => {
                for name in &explicit.names {
                    self.register(name);
                }
                self.get_type_names(&explicit.term);
            }
            Binder::Implicit(implicit) => {
                for name in &implicit.names {
                    self.register(name);
                }
                if let Some(term) = &implicit.term {
                    self.get_type_names(term);
                }
            }
            Binder::Simple(simple) => self.register(&simple.name),
        }
    }

    fn get_open_binders_names(&mut self, binder: &Box<OpenBinders>) {
        match &**binder {
            OpenBinders::Binders(binders) => {
                for binder in &binders.binders {
                    self.get_binder_names(binder);
                }
            }
            OpenBinders::OpenBinder(binder) => {
                for name in &binder.names {
                    self.register(name);
                    self.get_type_names(&binder.term);
                }
            }
        }
    }

    fn get_type_names(&mut self, term: &Box<Type>) {
        match &**term {
            Type::Quantifier(forall) => {
                self.open();
                self.get_open_binders_names(&forall.binder);
                self.get_type_names(&forall.has);
                self.close();
            }
            Type::Fun(fun) => {
                self.get_type_names(&fun.from);
                self.get_type_names(&fun.to);
            }
            Type::Custom(tokens) => {
                for token in tokens {
                    if let CoqTokenKind::Word(word) = &token.kind {
                        self.see(word);
                    }
                }
            }
        }
    }

    fn get_theorem_names(&mut self, theorem: &Theorem) {
        self.open();
        for binder in &theorem.binders {
            self.get_binder_names(binder);
        }
        self.get_type_names(&theorem.term);
        self.close();
    }

    fn get_constructor_names(&mut self, constructor: &Constructor) {
        self.open();
        for binder in &constructor.binders {
            self.get_binder_names(binder);
        }
        if let Some(term) = &constructor.term {
            self.get_type_names(term);
        }
        self.close();
    }

    fn get_inductive_names(&mut self, inductive: &Inductive) {
        self.open();
        for binder in &inductive.binders {
            self.get_binder_names(binder);
        }
        self.get_type_names(&inductive.term);
        for constructor in &inductive.constructors {
            self.get_constructor_names(constructor);
        }
        self.close();
    }

    fn get_definition_names(&mut self, definition: &Definition) {
        self.open();
        for binder in &definition.binders {
            self.get_binder_names(binder);
        }
        self.get_type_names(&definition.term);
        self.close();
    }

    fn get_goal_names(&mut self, goal: &Goal) {
        self.open();
        for hypothesis in &goal.premise {
            self.register(&hypothesis.name);
            self.get_type_names(&hypothesis.term);
        }
        self.get_type_names(&goal.conclusion);
        self.close();
    }

    fn get_expression_names(&mut self, expression: &CoqExpression) {
        match expression {
            CoqExpression::Theorem(theorem) => self.get_theorem_names(theorem),
            CoqExpression::Inductive(inductive) => self.get_inductive_names(inductive),
            CoqExpression::Definition(definition) => self.get_definition_names(definition),
            CoqExpression::Goal(goals) => {
                for goal in goals {
                    self.get_goal_names(goal);
                }
            }
            _ => {}
        }
    }
}

pub fn parse(query: CoqTokenSlice) -> Result<CoqExpression> {
    let mut parser = CoqParser::new(query);
    parser.parse_expression()
}

pub fn get_names(expression: &CoqExpression) -> Vec<String> {
    let mut collector = NameCollector::new();
    collector.get_expression_names(&expression);
    collector.collect()
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::{tokenize, CoqTokenSlice},
        parser::{CoqParser, NameCollector},
    };

    fn check(data: &str) {
        let tokens = tokenize(data);
        println!("{:?}", tokens);

        let mut parser = CoqParser::new(CoqTokenSlice::from(tokens.as_slice()));
        let expr = parser.parse_expression().unwrap();

        println!("{}", expr);
        println!("{:?}", expr);

        let mut collector = NameCollector::new();
        collector.get_expression_names(&expr);
        let names = collector.collect();

        println!("{:?}", names);
    }

    #[test]
    fn theorem_plus_n_sm() {
        check("Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).");
    }

    #[test]
    fn inductive_nat() {
        check("Inductive nat : Set :=  O : nat | S : nat -> nat.");
    }

    #[test]
    fn inductive_le() {
        check("Inductive le (n : nat) : nat -> Prop := le_n : n <= n | le_S : forall m : nat, n <= m -> n <= Datatypes.S m.");
    }

    #[test]
    fn compact() {
        check(
            "Definition compact (X:TopologicalSpace) :=
        forall C:Family X,
          (forall U:Ensemble X, In C U -> open U) ->
          FamilyUnion C = Full_set ->
          exists C':Family X,
            Finite C' /\\ Included C' C /\\
            FamilyUnion C' = Full_set.",
        );
    }

    #[test]
    fn goals() {
        check(
            "3 goals
  
        X : Type
        goal : eq 2 2
        ============================
        eq 1 1
      
      goal 2 is:
       eq 0 0
      goal 3 is:
       forall n m : nat, eq (S (Nat.add n m)) (Nat.add n (S m))
      
      ",
        );
    }
}
