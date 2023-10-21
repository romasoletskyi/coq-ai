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
            ParserError::Eof => write!(f, "ParserError: EOF"),
            ParserError::UnexpectedToken(token) => {
                write!(f, "ParserError: unexpected token {}", token)
            }
            ParserError::UnexpectedQuery => write!(f, "ParserError: unexpected query"),
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
    typ: Box<Term>,
}

impl Display for ExplicitBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for name in &self.names {
            write!(f, "{} ", name)?;
        }
        write!(f, ": {})", *self.typ)
    }
}

#[derive(Debug, PartialEq)]
struct ImplicitBinder {
    names: Vec<String>,
    typ: Option<Box<Term>>,
}

impl Display for ImplicitBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for i in 0..self.names.len() - 1 {
            write!(f, "{} ", self.names[i])?;
        }
        write!(f, "{}", self.names[self.names.len() - 1])?;
        if let Some(typ) = &self.typ {
            write!(f, " : {}", *typ)?;
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
    typ: Box<Term>,
}

impl Display for OpenBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for name in &self.names {
            write!(f, "{} ", name)?;
        }
        write!(f, ": {}", *self.typ)
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
struct Quantifier {
    token: String,
    binder: Box<OpenBinders>,
    has: Box<Term>,
}

impl Display for Quantifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}, {}", self.token, self.binder, self.has)
    }
}

#[derive(Debug, PartialEq)]
struct FunType {
    from: Box<Term>,
    to: Box<Term>,
}

impl Display for FunType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} -> {}", *self.from, *self.to)
    }
}

static WITH: &str = "with";

static END: &str = "end";

#[derive(Debug, PartialEq)]
struct MatchCase {
    pattern: Box<Term>,
    term: Box<Term>,
}

#[derive(Debug, PartialEq)]
struct Match {
    input: Box<Term>,
    cases: Vec<MatchCase>,
}

impl Display for Match {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "match {} with\n", self.input)?;
        for case in &self.cases {
            write!(f, "| {} => {}", case.pattern, case.term)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, PartialEq)]
enum Term {
    Quantifier(Quantifier),
    FunType(FunType),
    Match(Match),
    Fixpoint(Fixpoint),
    Custom(Vec<CoqToken>),
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Quantifier(typ) => write!(f, "{}", typ),
            Term::FunType(typ) => write!(f, "{}", typ),
            Term::Match(mat) => write!(f, "{}", mat),
            Term::Fixpoint(fix) => write!(f, "{}", fix),
            Term::Custom(tokens) => write!(f, "{}", CoqTokenSlice::from(tokens.as_slice())),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Theorem {
    token: String,
    name: String,
    binders: Vec<Binder>,
    typ: Box<Term>,
}

impl Display for Theorem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.token, self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        write!(f, " : {}", self.typ)
    }
}

#[derive(Debug, PartialEq)]
struct Constructor {
    name: String,
    binders: Vec<Binder>,
    typ: Option<Box<Term>>,
}

impl Display for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        if let Some(typ) = &self.typ {
            write!(f, " : {}", typ)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub struct Inductive {
    pub name: String,
    binders: Vec<Binder>,
    typ: Box<Term>,
    constructors: Vec<Constructor>,
}

impl Display for Inductive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Inductive {}", self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        write!(f, " : {} := ", self.typ)?;
        for i in 0..self.constructors.len() - 1 {
            write!(f, "{} |", self.constructors[i])?;
        }
        write!(f, " {}.", self.constructors[self.constructors.len() - 1])
    }
}

#[derive(Debug, PartialEq)]
pub struct Definition {
    token: String,
    pub name: String,
    binders: Vec<Binder>,
    sort: Option<Box<Term>>,
    typ: Box<Term>,
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
        write!(f, " := {}", self.typ)
    }
}

static STRUCT: &str = "struct";

#[derive(Debug, PartialEq)]
struct FixAnnotation {
    name: String,
}

impl Display for FixAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{struct {}}}", self.name)
    }
}

#[derive(Debug, PartialEq)]
pub struct Fixpoint {
    name: String,
    binders: Vec<Binder>,
    annotation: Option<FixAnnotation>,
    typ: Option<Box<Term>>,
    term: Box<Term>,
}

impl Display for Fixpoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Fixpoint {}", self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        if let Some(annotation) = &self.annotation {
            write!(f, " {}", annotation)?;
        }
        if let Some(typ) = &self.typ {
            write!(f, " : {}", typ)?;
        }
        write!(f, " := {}", self.term)
    }
}

#[derive(Debug, PartialEq)]
pub struct PrintVariable {
    name: String,
    term: Box<Term>,
    typ: Box<Term>,
}

impl Display for PrintVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {} : {}", self.name, self.term, self.typ)
    }
}

#[derive(Debug, PartialEq)]
struct Hypothesis {
    name: String,
    typ: Box<Term>,
}

impl Display for Hypothesis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.name, self.typ)
    }
}

#[derive(Debug, PartialEq)]
pub struct Goal {
    premise: Vec<Hypothesis>,
    conclusion: Box<Term>,
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
    Fixpoint(Fixpoint),
    PrintVariable(PrintVariable),
    Tactic(Vec<CoqToken>),
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
            CoqExpression::Fixpoint(fixpoint) => write!(f, "{}", fixpoint),
            CoqExpression::PrintVariable(variable) => write!(f, "{}", variable),
            CoqExpression::Tactic(tactic) => write!(f, "{}", CoqTokenSlice::from(tactic.as_slice())),
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

    fn peek(&self) -> Result<&CoqToken> {
        if self.index + 1 >= self.slice.len() {
            bail!(ParserError::Eof);
        }
        Ok(&self.slice[self.index + 1])
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

    /// parses term and puts carret on next token
    fn parse_term(&mut self, pred: fn(&CoqTokenKind) -> bool) -> Result<Box<Term>> {
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(word) = kind {
            match word.as_str() {
                "forall" | "exists" => {
                    self.advance();
                    let binder = Box::new(self.parse_open_binder()?);
                    self.advance();
                    return Ok(Box::new(Term::Quantifier(Quantifier {
                        token: word,
                        binder,
                        has: self.parse_term(pred)?,
                    })));
                }
                "match" => {
                    self.advance();
                    let input =
                        self.parse_term(|token| token == &CoqTokenKind::Word(WITH.to_string()))?;
                    self.advance();

                    let mut cases = Vec::new();
                    while &self.current()?.kind == &CoqTokenKind::Pipe {
                        self.advance();
                        let pattern = self.parse_term(|token| token == &CoqTokenKind::Case)?;
                        self.advance();
                        let term = self.parse_term(|token| {
                            token == &CoqTokenKind::Pipe
                                || token == &CoqTokenKind::Word(END.to_string())
                        })?;
                        cases.push(MatchCase { pattern, term });
                    }
                    self.advance();
                    return Ok(Box::new(Term::Match(Match { input, cases })));
                }
                "fix" => return Ok(Box::new(Term::Fixpoint(self.parse_fixpoint(pred)?))),
                _ => {}
            }
        }

        if let CoqTokenKind::BracketLeft = &self.current()?.kind {
            self.advance();
            let term = self.parse_term(|kind| &CoqTokenKind::BracketRight == kind)?;
            self.advance();

            if pred(&self.current()?.kind) {
                return Ok(term);
            } else if CoqTokenKind::Arrow == self.current()?.kind {
                self.advance();
                return Ok(Box::new(Term::FunType(FunType {
                    from: term,
                    to: self.parse_term(pred)?,
                })));
            }
            bail!(ParserError::UnexpectedToken(self.current()?.clone()))
        }

        let mut tokens = Vec::new();
        loop {
            let token = self.current()?;
            if CoqTokenKind::Arrow == token.kind {
                let from = Box::new(Term::Custom(tokens));
                self.advance();
                return Ok(Box::new(Term::FunType(FunType {
                    from,
                    to: self.parse_term(pred)?,
                })));
            } else if pred(&token.kind) {
                return Ok(Box::new(Term::Custom(tokens)));
            }
            tokens.push(token.clone());
            self.advance();
        }
    }

    fn parse_name(&mut self) -> Result<String> {
        let token = self.current()?.clone();
        match token.kind {
            CoqTokenKind::Word(name) => Ok(name),
            CoqTokenKind::Underscore => Ok("_".to_string()),
            _ => bail!(ParserError::UnexpectedToken(token.clone())),
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
                let typ = self.parse_term(|token| &CoqTokenKind::BracketRight == token)?;

                self.advance();
                Ok(Binder::Explicit(ExplicitBinder { names, typ }))
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
                let typ = if seen_colon {
                    let term =
                        self.parse_term(|token| &CoqTokenKind::BracketCurlyRight == token)?;
                    self.advance();
                    Some(term)
                } else {
                    None
                };

                Ok(Binder::Implicit(ImplicitBinder { names, typ }))
            }
            _ => bail!(ParserError::UnexpectedToken(self.current()?.clone())),
        }
    }

    fn parse_open_binder(&mut self) -> Result<OpenBinders> {
        let mut names = Vec::new();
        loop {
            match self.parse_name() {
                std::result::Result::Ok(name) => {
                    names.push(name);
                    self.advance();
                }
                _ => break,
            };
        }

        //  we suppose that open_binders are used only as:
        //      forall (open_binders), (type)
        if CoqTokenKind::Colon == self.current()?.kind {
            self.advance();
            let typ = self.parse_term(|token| &CoqTokenKind::Comma == token)?;
            Ok(OpenBinders::OpenBinder(OpenBinder { names, typ }))
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

    fn parse_theorem(&mut self, token: String) -> Result<Theorem> {
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
                typ: self.parse_term(|token| &CoqTokenKind::Dot == token)?,
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

            let pred =
                |token: &CoqTokenKind| &CoqTokenKind::Dot == token || &CoqTokenKind::Pipe == token;
            let typ = if pred(&self.current()?.kind) {
                None
            } else {
                if CoqTokenKind::Colon != self.current()?.kind {
                    bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                }
                self.advance();
                Some(self.parse_term(pred)?)
            };

            return Ok(Constructor { name, binders, typ });
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
            let typ = self.parse_term(|token| &CoqTokenKind::Define == token)?;
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
                typ,
                constructors,
            });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_definition(&mut self, token: String) -> Result<Definition> {
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
                Some(self.parse_term(|token| token == &CoqTokenKind::Define)?)
            } else {
                None
            };

            self.advance();
            let typ = self.parse_term(|token| token == &CoqTokenKind::Dot)?;

            return Ok(Definition {
                token,
                name,
                binders,
                sort,
                typ,
            });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_fixpoint_annotation(&mut self) -> Result<FixAnnotation> {
        self.advance();
        self.advance();
        let name = self.parse_name()?;
        self.advance();
        self.advance();
        Ok(FixAnnotation { name })
    }

    fn parse_fixpoint(&mut self, pred: fn(&CoqTokenKind) -> bool) -> Result<Fixpoint> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            let mut binders = Vec::new();
            let mut annotation = None;
            let mut typ = None;

            loop {
                let mut stop = false;
                if self.current()?.kind == CoqTokenKind::BracketCurlyLeft
                    && self.peek()?.kind == CoqTokenKind::Word(STRUCT.to_string())
                {
                    annotation = Some(self.parse_fixpoint_annotation()?);
                    stop = true;
                }
                if self.current()?.kind == CoqTokenKind::Colon {
                    self.advance();
                    typ = Some(self.parse_term(|token| token == &CoqTokenKind::Define)?);
                    stop = true;
                }
                if stop {
                    break;
                }
                binders.push(self.parse_binder()?);
            }

            self.advance();
            return Ok(Fixpoint {
                name,
                binders,
                annotation,
                typ,
                term: self.parse_term(pred)?,
            });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_print_variable(&mut self, name: String) -> Result<PrintVariable> {
        self.advance();
        self.advance();
        let term = self.parse_term(|token| token == &CoqTokenKind::Colon)?;
        self.advance();
        let typ = self.parse_term(|token| {
            token == &CoqTokenKind::NewLine || token == &CoqTokenKind::Word("Arguments".to_string())
        })?;
        Ok(PrintVariable { name, term, typ })
    }

    fn parse_hypothesis(&mut self) -> Result<Hypothesis> {
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            self.advance();
            let typ = self.parse_term(|token| token == &CoqTokenKind::NewLine)?;
            self.advance();
            return Ok(Hypothesis { name, typ });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_goal(&mut self) -> Result<Goal> {
        let mut premise = Vec::new();
        while self.current()?.kind != CoqTokenKind::Eq {
            premise.push(self.parse_hypothesis()?);
        }
        self.skip_line();
        let conclusion = self.parse_term(|token| token == &CoqTokenKind::NewLine)?;
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
            let conclusion = self.parse_term(|token| token == &CoqTokenKind::NewLine)?;
            self.advance();
            goals.push(Goal {
                premise: Vec::new(),
                conclusion,
            });
        }

        Ok(goals)
    }

    fn parse_expression(&mut self) -> Result<CoqExpression> {
        let token = self.current()?.clone();
        if let CoqTokenKind::Word(word) = token.kind {
            if let std::result::Result::Ok(number) = word.parse::<usize>() {
                return Ok(CoqExpression::Goal(self.parse_goals(number)?));
            }
            return match word.as_str() {
                "Theorem" | "Lemma" | "Fact" | "Remark" | "Corollary" | "Proposition"
                | "Property" => Ok(CoqExpression::Theorem(self.parse_theorem(word)?)),
                "Inductive" => Ok(CoqExpression::Inductive(self.parse_inductive()?)),
                "Definition" | "Example" => {
                    Ok(CoqExpression::Definition(self.parse_definition(word)?))
                }
                "Fixpoint" => Ok(CoqExpression::Fixpoint(
                    self.parse_fixpoint(|token| token == &CoqTokenKind::Dot)?,
                )),
                "Section" => {
                    self.advance();
                    Ok(CoqExpression::SectionStart(self.parse_name()?))
                }
                "End" => {
                    self.advance();
                    Ok(CoqExpression::SectionEnd(self.parse_name()?))
                }
                "Proof" => Ok(CoqExpression::Proof),
                "Qed" => Ok(CoqExpression::Qed),
                _ => {
                    if let std::result::Result::Ok(token) = self.peek(){
                        if token.kind == CoqTokenKind::Eq {
                            Ok(CoqExpression::PrintVariable(self.parse_print_variable(word)?))
                        } else {
                            Ok(CoqExpression::Tactic(self.slice.clone().into()))
                        }
                    } else {
                        Ok(CoqExpression::Tactic(self.slice.clone().into()))
                    }
                }
            };
        }
        bail!(ParserError::UnexpectedQuery);
    }
}

enum NameCollectorMode {
    Seeing,
    Registering,
}

/// Collector for gathering names within Coq expressions
struct NameCollector {
    known: HashSet<String>,
    seen: HashSet<String>,
    register: Vec<String>,
    bottom: Vec<usize>,
    mode: NameCollectorMode,
}

impl NameCollector {
    fn new() -> Self {
        NameCollector {
            known: HashSet::new(),
            seen: HashSet::new(),
            register: Vec::new(),
            bottom: Vec::new(),
            mode: NameCollectorMode::Seeing,
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
                self.get_term_names(&explicit.typ);
            }
            Binder::Implicit(implicit) => {
                for name in &implicit.names {
                    self.register(name);
                }
                if let Some(term) = &implicit.typ {
                    self.get_term_names(term);
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
                    self.get_term_names(&binder.typ);
                }
            }
        }
    }

    fn get_term_names(&mut self, term: &Box<Term>) {
        match &**term {
            Term::Quantifier(forall) => {
                self.open();
                self.get_open_binders_names(&forall.binder);
                self.get_term_names(&forall.has);
                self.close();
            }
            Term::FunType(fun) => {
                self.get_term_names(&fun.from);
                self.get_term_names(&fun.to);
            }
            Term::Match(mat) => {
                self.open();
                self.mode = NameCollectorMode::Registering;
                self.get_term_names(&mat.input);
                self.mode = NameCollectorMode::Seeing;

                for case in &mat.cases {
                    // ISSUE - 1
                    // consider pattern | S n' => ...
                    // currently it is out of our capabilities to understand
                    // that S is a function and n' is a free variable

                    self.mode = NameCollectorMode::Registering;
                    self.get_term_names(&case.pattern);
                    self.mode = NameCollectorMode::Seeing;

                    self.get_term_names(&case.term);
                }
                self.close();
            }
            Term::Custom(tokens) => {
                for token in tokens {
                    if let CoqTokenKind::Word(word) = &token.kind {
                        match self.mode {
                            NameCollectorMode::Seeing => self.see(word),
                            NameCollectorMode::Registering => self.register(word),
                        };
                    }
                }
            }
            Term::Fixpoint(fixpoint) => self.get_fixpoint_names(fixpoint),
        }
    }

    fn get_theorem_names(&mut self, theorem: &Theorem) {
        self.open();
        for binder in &theorem.binders {
            self.get_binder_names(binder);
        }
        self.get_term_names(&theorem.typ);
        self.close();
    }

    fn get_constructor_names(&mut self, constructor: &Constructor) {
        self.open();
        for binder in &constructor.binders {
            self.get_binder_names(binder);
        }
        if let Some(term) = &constructor.typ {
            self.get_term_names(term);
        }
        self.close();
    }

    fn get_inductive_names(&mut self, inductive: &Inductive) {
        self.open();
        for binder in &inductive.binders {
            self.get_binder_names(binder);
        }
        self.get_term_names(&inductive.typ);
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
        self.get_term_names(&definition.typ);
        self.close();
    }

    fn get_fixpoint_names(&mut self, fixpoint: &Fixpoint) {
        self.open();
        self.register(&fixpoint.name);
        for binder in &fixpoint.binders {
            self.get_binder_names(binder);
        }
        if let Some(typ) = &fixpoint.typ {
            self.get_term_names(typ);
        }
        self.get_term_names(&fixpoint.term);
        self.close();
    }

    fn get_print_variable_names(&mut self, variable: &PrintVariable) {
        self.open();
        self.get_term_names(&variable.term);
        self.get_term_names(&variable.typ);
        self.close();
    }

    fn get_goal_names(&mut self, goal: &Goal) {
        self.open();
        for hypothesis in &goal.premise {
            self.register(&hypothesis.name);
            self.get_term_names(&hypothesis.typ);
        }
        self.get_term_names(&goal.conclusion);
        self.close();
    }

    fn get_expression_names(&mut self, expression: &CoqExpression) {
        match expression {
            CoqExpression::Theorem(theorem) => self.get_theorem_names(theorem),
            CoqExpression::Inductive(inductive) => self.get_inductive_names(inductive),
            CoqExpression::Definition(definition) => self.get_definition_names(definition),
            CoqExpression::Fixpoint(fixpoint) => self.get_fixpoint_names(fixpoint),
            CoqExpression::PrintVariable(variable) => self.get_print_variable_names(variable),
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
        lexer::{tokenize, CoqToken, CoqTokenKind, CoqTokenSlice},
        parser::{CoqParser, NameCollector},
    };

    fn check(data: &str) {
        let mut tokens = tokenize(data).unwrap();
        tokens.push(CoqToken::new(CoqTokenKind::NewLine, 0, 0));
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
    fn inductive_nat_complete() {
        check(
            "Inductive nat : Set :=  O : nat | S : nat -> nat.
                    Arguments S _%nat_scope",
        )
    }

    #[test]
    fn inductive_le() {
        check("Inductive le (n : nat) : nat -> Prop := le_n : n <= n | le_S : forall m : nat, n <= m -> n <= Datatypes.S m.");
    }

    #[test]
    fn inductive_eq() {
        check(
            "Inductive eq (A : Type) (x : A) : forall _ : A, Prop :=  eq_refl : eq x x.

        Arguments eq {A}%type_scope x _
        Arguments eq_refl {A}%type_scope {x}, [_] _
        ",
        );
    }

    #[test]
    fn definition_compact() {
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
    fn fixpoint_factorial() {
        check(
            "Fixpoint factorial (n:nat) : nat :=
                    match n with
                    | O => S O
                    | S n' => mult n (factorial n')
                    end.",
        );
    }

    #[test]
    fn fixpoint_add_definition() {
        check(
            "Nat.add = 
        fix add (n m : nat) {struct n} : nat :=
          match n with
          | 0 => m
          | S p => S (add p m)
          end
             : forall (_ : nat) (_ : nat), nat",
        );
    }

    #[test]
    fn goals() {
        check(
            "3 goals
  
        X : Term
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
