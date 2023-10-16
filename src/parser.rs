use anyhow::{bail, Ok, Result};
use std::{fmt::Display, collections::HashSet};

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

/*enum SortToken {
    SProp,
    Prop,
    Set,
    Type,
}

impl TryFrom<&CoqToken> for SortToken {
    type Error = anyhow::Error;

    fn try_from(value: &CoqToken) -> std::result::Result<Self, Self::Error> {
        match &value.kind {
            CoqTokenKind::Word(word) => match word.as_str() {
                "SProp" => Ok(SortToken::SProp),
                "Prop" => Ok(SortToken::Prop),
                "Set" => Ok(SortToken::Set),
                "Type" => Ok(SortToken::Type),
                _ => bail!(ParserError::UnexpectedToken(value.clone())),
            },
            _ => bail!(ParserError::UnexpectedToken(value.clone())),
        }
    }
}*/

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

static FORALL: &str = "forall";

#[derive(Debug, PartialEq)]
struct ForAll {
    binder: Box<OpenBinders>,
    has: Box<Type>,
}

impl Display for ForAll {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "forall {}, {}", *self.binder, *self.has)
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
    ForAll(ForAll),
    Fun(Fun),
    Custom(Vec<CoqToken>),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::ForAll(term) => write!(f, "{}", term),
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
struct Theorem {
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
    term: Option<Box<Type>>
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

static INDUCTIVE: &str = "Inductive";

#[derive(Debug, PartialEq)]
struct Inductive {
    name: String,
    binders: Vec<Binder>,
    term: Box<Type>,
    constructors: Vec<Constructor>
}

impl Display for Inductive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Inductive {}", self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        write!(f, " : {} := ", self.term)?;
        for i in 0..self.constructors.len()-1 {
            write!(f, "{} |", self.constructors[i])?;
        }
        write!(f, " {}.", self.constructors[self.constructors.len()-1])
    }
}

#[derive(Debug, PartialEq)]
enum CoqExpression {
    Theorem(Theorem),
    Inductive(Inductive)
}

impl Display for CoqExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            CoqExpression::Theorem(theorem) => write!(f, "{}", theorem),
            CoqExpression::Inductive(def) => write!(f, "{}", def)
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
        if self.slice.len() < self.index {
            bail!(ParserError::Eof);
        }
        Ok(&self.slice[self.index])
    }

    fn peek(&self) -> Result<&CoqToken> {
        if self.slice.len() < self.index + 1 {
            bail!(ParserError::Eof);
        }
        Ok(&self.slice[self.index + 1])
    }

    fn advance(&mut self) {
        self.index += 1;
    }

    fn parse_type(&mut self, pred: fn(&CoqTokenKind) -> bool) -> Result<Box<Type>> {
        if let CoqTokenKind::Word(word) = &self.current()?.kind {
            if word == FORALL {
                self.advance();
                let binder = Box::new(self.parse_open_binder()?);
                self.advance();
                return Ok(Box::new(Type::ForAll(ForAll {
                    binder,
                    has: self.parse_type(pred)?,
                })));
            }
        }

        if let CoqTokenKind::BracketLeft = &self.current()?.kind {
            self.advance();
            let term = self.parse_type(|kind| &CoqTokenKind::BracketRight == kind)?;
            self.advance();
            let next = self.peek()?;

            if pred(&next.kind) {
                return Ok(term);
            }
            if CoqTokenKind::Arrow == next.kind {
                self.advance();
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
                    let term = self.parse_type(|token| &CoqTokenKind::BracketCurlyRight == token)?;
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
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            let mut binders = Vec::new();
            while CoqTokenKind::Colon != self.current()?.kind {
                binders.push(self.parse_binder()?);
            }

            let pred = |token: &CoqTokenKind| &CoqTokenKind::Dot == token || &CoqTokenKind::Pipe == token;
            let term = if pred(&self.current()?.kind) {
                None
            } else {
                if CoqTokenKind::Colon != self.current()?.kind {
                    bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                }
                self.advance();
                Some(self.parse_type(pred)?)
            };

            return Ok(Constructor { name, binders, term });
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

            return Ok(Inductive { name, binders, term, constructors });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_expression(&mut self) -> Result<CoqExpression> {
        let token = self.current()?;
        if let CoqTokenKind::Word(word) = &token.kind {
            if let std::result::Result::Ok(token) = TheoremToken::try_from(token) {
                return Ok(CoqExpression::Theorem(self.parse_theorem(token)?));
            }
            if word.as_str() == INDUCTIVE {
                return Ok(CoqExpression::Inductive(self.parse_inductive()?));
            }
        }
        bail!(ParserError::UnexpectedQuery);
    }
}

struct NameCollector {
    known: HashSet<String>,
    seen: HashSet<String>,
    register: Vec<String>,
    bottom: Vec<usize>
}

impl NameCollector {
    fn new() -> Self {
        NameCollector { known: HashSet::new(), seen: HashSet::new(), register: Vec::new(), bottom: Vec::new() }
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
            },
            Binder::Implicit(implicit) => {
                for name in &implicit.names {
                    self.register(name);
                }
                if let Some(term) = &implicit.term {
                    self.get_type_names(term);
                }
            },
            Binder::Simple(simple) => self.register(&simple.name)
        }
    }

    fn get_open_binders_names(&mut self, binder: &Box<OpenBinders>) {
        match &**binder {
            OpenBinders::Binders(binders) => {
                for binder in &binders.binders {
                    self.get_binder_names(binder);
                }
            },
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
            Type::ForAll(forall) => {
                self.open();
                self.get_open_binders_names(&forall.binder);
                self.get_type_names(&forall.has);
                self.close();
            },
            Type::Fun(fun) => {
                self.get_type_names(&fun.from);
                self.get_type_names(&fun.to);
            },
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

    fn get_expression_names(&mut self, expression: &CoqExpression) {
        match expression {
            CoqExpression::Theorem(theorem) => self.get_theorem_names(theorem),
            CoqExpression::Inductive(inductive) => self.get_inductive_names(inductive)
        }
    }
}

pub fn get_names(query: CoqTokenSlice) -> Result<Vec<String>> {
    let mut parser = CoqParser::new(query);
    let expression = parser.parse_expression()?;
    let mut collector = NameCollector::new();
    collector.get_expression_names(&expression);
    Ok(collector.collect())
}

#[cfg(test)]
mod tests {
    use super::CoqParser;
    use crate::{lexer::{tokenize, CoqTokenSlice}, parser::NameCollector};

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
        // think about module paths A.B.C
        check("Inductive le (n : nat) : nat -> Prop := le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m.");
    }
}
