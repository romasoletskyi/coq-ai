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
enum OpenBinders {
    OpenBinder(OpenBinder),
    Binders(Vec<Binder>),
}

impl Display for OpenBinders {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpenBinders::OpenBinder(binder) => write!(f, "{}", binder),
            OpenBinders::Binders(binders) => {
                for binder in binders {
                    write!(f, "{} ", binder)?;
                }
                std::fmt::Result::Ok(())
            }
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
        writeln!(f, "match {} with", self.input)?;
        for case in &self.cases {
            write!(f, "| {} => {}", case.pattern, case.term)?;
        }
        std::fmt::Result::Ok(())
    }
}

static THEN: &str = "then";

static ELSE: &str = "else";

#[derive(Debug, PartialEq)]
struct IfTerm {
    if_term: Box<Term>,
    then_term: Box<Term>,
    else_term: Box<Term>,
}

impl Display for IfTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "if {} then {} else {}",
            self.if_term, self.then_term, self.else_term
        )
    }
}

static IN: &str = "in";

static AS: &str = "as";

#[derive(Debug, PartialEq)]
struct BasicLetIn {
    name: String,
    binders: Vec<Binder>,
    typ: Option<Box<Term>>,
    def: Box<Term>,
    main: Box<Term>,
}

impl Display for BasicLetIn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "let {}", self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        if let Some(typ) = &self.typ {
            write!(f, " : {}", typ)?;
        }
        write!(f, " := {} in {}", self.def, self.main)
    }
}

#[derive(Debug, PartialEq)]
struct DestructLetIn {
    names: Vec<String>,
    ret: Option<(Option<String>, Box<Term>)>,
    destruct: Box<Term>,
    main: Box<Term>,
}

impl Display for DestructLetIn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "let ({}", self.names[0])?;
        for i in 1..self.names.len() {
            write!(f, ", {}", self.names[i])?;
        }
        write!(f, ") ")?;
        if let Some((as_name, ret_typ)) = &self.ret {
            if let Some(name) = as_name {
                write!(f, "as {} ", name)?;
            }
            write!(f, "return {} ", ret_typ)?;
        }
        write!(f, ":= {} in {}", self.destruct, self.main)
    }
}

#[derive(Debug, PartialEq)]
enum LetIn {
    BasicLetIn(BasicLetIn),
    DestructLetIn(DestructLetIn),
}

impl Display for LetIn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LetIn::BasicLetIn(term) => write!(f, "{}", term),
            LetIn::DestructLetIn(term) => write!(f, "{}", term),
        }
    }
}

#[derive(Debug, PartialEq)]
struct Function {
    binder: OpenBinders,
    term: Box<Term>,
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fun {} => {}", self.binder, self.term)
    }
}

#[derive(Debug, PartialEq)]
struct RecordFieldTerm {
    name: String,
    binders: Vec<Binder>,
    term: Box<Term>,
}

impl Display for RecordFieldTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        write!(f, " := {}", self.term)
    }
}

#[derive(Debug, PartialEq)]
struct RecordTerm {
    fields: Vec<RecordFieldTerm>,
}

impl Display for RecordTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{|")?;
        for i in 0..self.fields.len() - 1 {
            write!(f, " {};", self.fields[i])?;
        }
        if !self.fields.is_empty() {
            write!(f, " {}", self.fields[self.fields.len() - 1])?;
        }
        write!(f, " |}}")
    }
}

#[derive(Debug, PartialEq)]
enum ApplicationArgument {
    Simple(Box<BasicTerm>),
    Annotated(String, Box<Term>),
}

#[derive(Debug, PartialEq)]
struct Application {
    fun: Box<BasicTerm>,
    args: Vec<ApplicationArgument>,
}

impl Display for Application {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.fun)?;
        for arg in &self.args {
            match arg {
                ApplicationArgument::Simple(argument) => write!(f, " {}", argument)?,
                ApplicationArgument::Annotated(name, argument) => {
                    write!(f, " ({} := {})", name, argument)?
                }
            };
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, PartialEq)]
enum BasicTerm {
    Brackets(Box<Term>),
    Match(Match),
    Custom(CoqToken),
}

impl Display for BasicTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BasicTerm::Brackets(term) => write!(f, "({})", term),
            BasicTerm::Match(mat) => write!(f, "{}", mat),
            BasicTerm::Custom(token) => write!(f, "{}", token),
        }
    }
}

impl Default for BasicTerm {
    fn default() -> Self {
        Self::Custom(CoqToken::default())
    }
}

#[derive(Debug, PartialEq)]
enum Term {
    Quantifier(Quantifier),
    If(IfTerm),
    LetIn(LetIn),
    Function(Function),
    Fixpoint(Fixpoint),
    Record(RecordTerm),
    Application(Application),
    BasicTerm(Box<BasicTerm>),
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Quantifier(typ) => write!(f, "{}", typ),
            Term::If(term) => write!(f, "{}", term),
            Term::LetIn(term) => write!(f, "{}", term),
            Term::Function(fun) => write!(f, "{}", fun),
            Term::Fixpoint(fix) => write!(f, "{}", fix),
            Term::Record(record) => write!(f, "{}", record),
            Term::Application(app) => write!(f, "{}", app),
            Term::BasicTerm(term) => write!(f, "{}", term),
        }
    }
}

impl Default for Term {
    fn default() -> Self {
        Self::BasicTerm(Box::default())
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
pub struct Assumption {
    token: String,
    pub names: Vec<String>,
    typ: Box<Term>,
}

impl Display for Assumption {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ", self.token)?;
        for name in &self.names {
            write!(f, "{} ", name)?;
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

#[derive(Debug, PartialEq)]
struct FieldSpec {
    binders: Vec<Binder>,
    typ: Option<Box<Term>>,
    term: Option<Box<Term>>,
}

impl Display for FieldSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.binders.is_empty() {
            write!(f, "{}", self.binders[0])?;
        }
        for i in 1..self.binders.len() {
            write!(f, " {}", self.binders[i])?;
        }
        if let Some(typ) = &self.typ {
            write!(f, " {}", typ)?;
        }
        if let Some(term) = &self.term {
            write!(f, " := {}", term)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, PartialEq)]
struct RecordField {
    name: String,
    spec: Option<FieldSpec>,
}

impl Display for RecordField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if let Some(spec) = &self.spec {
            write!(f, " {}", spec)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, PartialEq)]
struct RecordBody {
    name: Option<String>,
    fields: Vec<RecordField>,
    arg: Option<String>,
}

impl Display for RecordBody {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "{} {{", name)?;
        }
        if !self.fields.is_empty() {
            write!(f, "{}", self.fields[0])?;
        }
        for i in 1..self.fields.len() {
            write!(f, "; {}", self.fields[i])?;
        }
        write!(f, "}}")?;
        if let Some(arg) = &self.arg {
            write!(f, " as {}", arg)?;
        }
        std::fmt::Result::Ok(())
    }
}

#[derive(Debug, PartialEq)]
pub struct Record {
    token: String,
    name: String,
    binders: Vec<Binder>,
    sort: Option<Box<Term>>,
    body: Option<RecordBody>,
}

impl Display for Record {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.token, self.name)?;
        for binder in &self.binders {
            write!(f, " {}", binder)?;
        }
        if let Some(sort) = &self.sort {
            write!(f, " : {}", sort)?;
        }
        if let Some(body) = &self.body {
            write!(f, " := {}", body)?;
        }
        std::fmt::Result::Ok(())
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
    names: Vec<String>,
    typ: Box<Term>,
}

impl Display for Hypothesis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.names[0])?;
        for i in 1..self.names.len() {
            write!(f, ", {}", self.names[i])?;
        }
        write!(f, " : {}", self.typ)
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
    Assumption(Assumption),
    Inductive(Inductive),
    Definition(Definition),
    Record(Record),
    Fixpoint(Fixpoint),
    PrintVariable(PrintVariable),
    Tactic(Vec<CoqToken>),
    Goal(Vec<Goal>),
    SectionStart(String),
    SectionEnd(String),
    Proof,
    Qed,
    From,
    Set,
    Unset,
}

impl Display for CoqExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            CoqExpression::Theorem(theorem) => write!(f, "{}", theorem),
            CoqExpression::Assumption(assumption) => write!(f, "{}", assumption),
            CoqExpression::Inductive(inductive) => write!(f, "{}", inductive),
            CoqExpression::Definition(definition) => write!(f, "{}", definition),
            CoqExpression::Record(record) => write!(f, "{}", record),
            CoqExpression::Fixpoint(fixpoint) => write!(f, "{}", fixpoint),
            CoqExpression::PrintVariable(variable) => write!(f, "{}", variable),
            CoqExpression::Tactic(tactic) => {
                write!(f, "{}", CoqTokenSlice::from(tactic.as_slice()))
            }
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
            CoqExpression::From => write!(f, "From"),
            CoqExpression::Set => write!(f, "Set"),
            CoqExpression::Unset => write!(f, "Unset"),
        }
    }
}

struct CoqParser<'a> {
    slice: CoqTokenSlice<'a>,
    index: usize,
    early: bool,
    skip_whitespace: bool,
}

impl<'a> CoqParser<'a> {
    fn new(slice: CoqTokenSlice<'a>, early: bool) -> Self {
        CoqParser {
            slice,
            index: 0,
            early,
            skip_whitespace: true,
        }
    }

    fn current(&self) -> Result<&CoqToken> {
        if self.index >= self.slice.len() {
            bail!(ParserError::Eof);
        }
        Ok(&self.slice[self.index])
    }

    fn peek(&self, amount: usize) -> Result<&CoqToken> {
        if self.index + amount >= self.slice.len() {
            bail!(ParserError::Eof);
        }
        Ok(&self.slice[self.index + amount])
    }

    fn advance(&mut self) {
        self.index += 1;
        while self.skip_whitespace
            && self.index + 1 < self.slice.len()
            && self.slice[self.index].kind == CoqTokenKind::NewLine
        {
            self.index += 1;
        }
    }

    fn skip_line(&mut self) {
        while self.index < self.slice.len() && self.slice[self.index].kind != CoqTokenKind::NewLine
        {
            self.index += 1;
        }
        self.index += 1;
    }

    fn parse_basic_term(&mut self) -> Result<Box<BasicTerm>> {
        let token = self.current()?.clone();
        if let CoqTokenKind::Word(word) = &token.kind {
            if word == "match" {
                self.advance();
                let input =
                    self.parse_term(|token| token == &CoqTokenKind::Word(WITH.to_string()))?;
                self.advance();

                let mut cases = Vec::new();
                while self.current()?.kind == CoqTokenKind::Pipe {
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
                return Ok(Box::new(BasicTerm::Match(Match { input, cases })));
            }
        }
        if let CoqTokenKind::BracketLeft = &self.current()?.kind {
            self.advance();
            let term = self.parse_term(|kind| &CoqTokenKind::BracketRight == kind)?;
            self.advance();
            return Ok(Box::new(BasicTerm::Brackets(term)));
        }
        self.advance();
        Ok(Box::new(BasicTerm::Custom(token)))
    }

    fn parse_argument(&mut self) -> Result<ApplicationArgument> {
        if self.current()?.kind == CoqTokenKind::BracketLeft {
            if let CoqTokenKind::Word(name) = self.peek(1)?.kind.clone() {
                if self.peek(2)?.kind == CoqTokenKind::Define {
                    for _ in 0..3 {
                        self.advance();
                    }
                    let term = self.parse_term(|token| token == &CoqTokenKind::BracketRight)?;
                    self.advance();
                    return Ok(ApplicationArgument::Annotated(name, term));
                }
            }
        }
        Ok(ApplicationArgument::Simple(self.parse_basic_term()?))
    }

    /// parses term and puts carret on stop token
    fn parse_term(&mut self, stop: fn(&CoqTokenKind) -> bool) -> Result<Box<Term>> {
        let kind = self.current()?.kind.clone();
        match kind {
            CoqTokenKind::Word(word) => match word.as_str() {
                "forall" | "exists" | "exists!" => {
                    self.advance();
                    let binder =
                        Box::new(self.parse_open_binder(|token| token == &CoqTokenKind::Comma)?);
                    self.advance();
                    return Ok(Box::new(Term::Quantifier(Quantifier {
                        token: word,
                        binder,
                        has: self.parse_term(stop)?,
                    })));
                }
                "if" => {
                    self.advance();
                    let if_term =
                        self.parse_term(|token| token == &CoqTokenKind::Word(THEN.to_string()))?;
                    self.advance();
                    let then_term =
                        self.parse_term(|token| token == &CoqTokenKind::Word(ELSE.to_string()))?;
                    self.advance();
                    return Ok(Box::new(Term::If(IfTerm {
                        if_term,
                        then_term,
                        else_term: self.parse_term(stop)?,
                    })));
                }
                "let" => {
                    self.advance();
                    let kind = self.current()?.kind.clone();
                    if let CoqTokenKind::Word(name) = kind {
                        self.advance();
                        let mut binders = Vec::new();
                        while self.current()?.kind != CoqTokenKind::Colon
                            && self.current()?.kind != CoqTokenKind::Define
                        {
                            binders.push(self.parse_binder()?);
                        }
                        let typ = if self.current()?.kind == CoqTokenKind::Colon {
                            self.advance();
                            Some(self.parse_term(|token| token == &CoqTokenKind::Define)?)
                        } else {
                            None
                        };
                        self.advance();
                        let def =
                            self.parse_term(|token| token == &CoqTokenKind::Word(IN.to_string()))?;
                        self.advance();
                        return Ok(Box::new(Term::LetIn(LetIn::BasicLetIn(BasicLetIn {
                            name,
                            binders,
                            typ,
                            def,
                            main: self.parse_term(stop)?,
                        }))));
                    } else if CoqTokenKind::BracketLeft == kind {
                        self.advance();
                        let mut names = Vec::new();
                        while self.current()?.kind != CoqTokenKind::BracketRight {
                            names.push(self.parse_name()?);
                            self.advance();
                            if self.current()?.kind == CoqTokenKind::Comma {
                                self.advance();
                            }
                        }
                        self.advance();
                        let kind = self.current()?.kind.clone();
                        let ret = if let CoqTokenKind::Word(word) = kind {
                            let as_name = if &word == "as" {
                                self.advance();
                                let s = Some(self.parse_name()?);
                                self.advance();
                                s
                            } else {
                                None
                            };
                            self.advance();
                            Some((
                                as_name,
                                self.parse_term(|token| token == &CoqTokenKind::Define)?,
                            ))
                        } else {
                            None
                        };
                        self.advance();
                        let destruct =
                            self.parse_term(|token| token == &CoqTokenKind::Word(IN.to_string()))?;
                        self.advance();
                        return Ok(Box::new(Term::LetIn(LetIn::DestructLetIn(DestructLetIn {
                            names,
                            ret,
                            destruct,
                            main: self.parse_term(stop)?,
                        }))));
                    }
                    bail!(ParserError::UnexpectedToken(self.current()?.clone()))
                }
                "fun" => {
                    self.advance();
                    let binder = self.parse_open_binder(|token| token == &CoqTokenKind::Case)?;
                    self.advance();
                    return Ok(Box::new(Term::Function(Function {
                        binder,
                        term: self.parse_term(stop)?,
                    })));
                }
                "fix" => return Ok(Box::new(Term::Fixpoint(self.parse_fixpoint(stop)?))),
                _ => {}
            },
            CoqTokenKind::BracketCurlyLeft => {
                self.advance();
                if self.current()?.kind != CoqTokenKind::Pipe {
                    bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                }
                self.advance();

                let mut fields = Vec::new();
                while self.current()?.kind != CoqTokenKind::Pipe {
                    let name = self.parse_name()?;
                    self.advance();

                    let mut binders = Vec::new();
                    while self.current()?.kind != CoqTokenKind::Define {
                        binders.push(self.parse_binder()?);
                    }

                    self.advance();
                    let term = self.parse_term(|token| {
                        token == &CoqTokenKind::SemiColon || token == &CoqTokenKind::Pipe
                    })?;
                    fields.push(RecordFieldTerm {
                        name,
                        binders,
                        term,
                    });

                    if self.current()?.kind == CoqTokenKind::SemiColon {
                        self.advance();
                    }
                }

                self.advance();
                self.advance();
                return Ok(Box::new(Term::Record(RecordTerm { fields })));
            }
            _ => {}
        }

        let term = self.parse_basic_term()?;
        let mut args = Vec::new();
        while !stop(&self.current()?.kind) {
            args.push(self.parse_argument()?);
        }

        if args.is_empty() {
            Ok(Box::new(Term::BasicTerm(term)))
        } else {
            Ok(Box::new(Term::Application(Application { fun: term, args })))
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
            CoqTokenKind::Underscore => Ok(Binder::Simple(SimpleBinder {
                name: "_".to_string(),
            })),
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
                let typ = self.parse_term(|token| token == &CoqTokenKind::BracketRight)?;

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
                        self.parse_term(|token| token == &CoqTokenKind::BracketCurlyRight)?;
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

    fn parse_open_binder(&mut self, stop: fn(&CoqTokenKind) -> bool) -> Result<OpenBinders> {
        let mut names = Vec::new();
        while let std::result::Result::Ok(name) = self.parse_name() {
            names.push(name);
            self.advance();
        }

        if CoqTokenKind::Colon == self.current()?.kind {
            self.advance();
            let typ = self.parse_term(stop)?;
            Ok(OpenBinders::OpenBinder(OpenBinder { names, typ }))
        } else {
            let binders = if names.is_empty() {
                let mut binders = Vec::new();
                while !stop(&self.current()?.kind) {
                    binders.push(self.parse_binder()?);
                }
                binders
            } else {
                names
                    .iter()
                    .map(|name| Binder::Simple(SimpleBinder { name: name.clone() }))
                    .collect()
            };
            Ok(OpenBinders::Binders(binders))
        }
    }

    fn parse_theorem(&mut self, token: String) -> Result<Theorem> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            if self.early {
                return Ok(Theorem {
                    token,
                    name,
                    binders: Vec::default(),
                    typ: Box::default(),
                });
            }

            self.advance();
            let mut binders = Vec::new();
            while CoqTokenKind::Colon != self.current()?.kind {
                binders.push(self.parse_binder()?);
            }

            self.advance();
            return Ok(Theorem {
                token,
                name,
                binders,
                typ: self.parse_term(|token| &CoqTokenKind::Dot == token)?,
            });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_assumption(
        &mut self,
        token: String,
        stop: fn(&CoqTokenKind) -> bool,
    ) -> Result<Assumption> {
        let mut names = Vec::new();
        while self.current()?.kind != CoqTokenKind::Colon {
            names.push(self.parse_name()?);
            self.advance();
        }

        if self.early {
            return Ok(Assumption {
                token,
                names,
                typ: Box::default(),
            });
        }

        self.advance();
        Ok(Assumption {
            token,
            names,
            typ: self.parse_term(stop)?,
        })
    }

    fn parse_constructor(&mut self) -> Result<Constructor> {
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            self.advance();
            let mut binders = Vec::new();
            while CoqTokenKind::Colon != self.current()?.kind {
                binders.push(self.parse_binder()?);
            }

            let stop =
                |token: &CoqTokenKind| &CoqTokenKind::Dot == token || &CoqTokenKind::Pipe == token;
            let typ = if stop(&self.current()?.kind) {
                None
            } else {
                if CoqTokenKind::Colon != self.current()?.kind {
                    bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                }
                self.advance();
                Some(self.parse_term(stop)?)
            };

            return Ok(Constructor { name, binders, typ });
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
    }

    fn parse_inductive(&mut self) -> Result<Inductive> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            if self.early {
                return Ok(Inductive {
                    name,
                    binders: Vec::default(),
                    typ: Box::default(),
                    constructors: Vec::default(),
                });
            }

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
            if self.early {
                return Ok(Definition {
                    token,
                    name,
                    binders: Vec::default(),
                    sort: None,
                    typ: Box::default(),
                });
            }

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

    fn parse_field_spec(&mut self) -> Result<FieldSpec> {
        let mut binders = Vec::new();
        while self.current()?.kind != CoqTokenKind::Colon
            && self.current()?.kind != CoqTokenKind::Define
        {
            binders.push(self.parse_binder()?);
        }
        let typ = if self.current()?.kind == CoqTokenKind::Colon {
            self.advance();
            Some(self.parse_term(|token| {
                token == &CoqTokenKind::Define
                    || token == &CoqTokenKind::SemiColon
                    || token == &CoqTokenKind::BracketCurlyRight
            })?)
        } else {
            None
        };
        let term = if self.current()?.kind == CoqTokenKind::Define {
            self.advance();
            Some(self.parse_term(|token| {
                token == &CoqTokenKind::SemiColon || token == &CoqTokenKind::BracketCurlyRight
            })?)
        } else {
            None
        };
        Ok(FieldSpec { binders, typ, term })
    }

    fn parse_record_field(&mut self) -> Result<RecordField> {
        let name = self.parse_name()?;
        self.advance();
        let spec = if self.current()?.kind != CoqTokenKind::SemiColon
            && self.current()?.kind != CoqTokenKind::BracketCurlyRight
        {
            Some(self.parse_field_spec()?)
        } else {
            None
        };
        Ok(RecordField { name, spec })
    }

    fn parse_record_body(&mut self) -> Result<RecordBody> {
        let name = self.parse_name().ok();
        if name.is_some() {
            self.advance();
        }
        if self.current()?.kind != CoqTokenKind::BracketCurlyLeft {
            bail!(ParserError::UnexpectedToken(self.current()?.clone()));
        }
        self.advance();

        let mut fields = Vec::new();
        while self.current()?.kind != CoqTokenKind::BracketCurlyRight {
            fields.push(self.parse_record_field()?);
            if self.current()?.kind == CoqTokenKind::SemiColon {
                self.advance();
            }
        }
        self.advance();

        let arg = if self.current()?.kind == CoqTokenKind::Word(AS.to_string()) {
            self.advance();
            let name = self.parse_name()?;
            self.advance();
            Some(name)
        } else {
            None
        };

        Ok(RecordBody { name, fields, arg })
    }

    fn parse_record(&mut self, token: String) -> Result<Record> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            if self.early {
                return Ok(Record {
                    token,
                    name,
                    binders: Vec::default(),
                    sort: None,
                    body: None,
                });
            }

            self.advance();
            let run = |token| {
                token != CoqTokenKind::Colon
                    && token != CoqTokenKind::Define
                    && token != CoqTokenKind::Dot
            };

            let mut binders = Vec::new();
            while run(self.current()?.kind.clone()) {
                binders.push(self.parse_binder()?);
            }

            let sort = if self.current()?.kind == CoqTokenKind::Colon {
                self.advance();
                Some(self.parse_term(|token| {
                    token == &CoqTokenKind::Define || token == &CoqTokenKind::Dot
                })?)
            } else {
                None
            };

            let body = if self.current()?.kind == CoqTokenKind::Define {
                self.advance();
                Some(self.parse_record_body()?)
            } else {
                None
            };

            return Ok(Record {
                token,
                name,
                binders,
                sort,
                body,
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

    fn parse_fixpoint(&mut self, stop: fn(&CoqTokenKind) -> bool) -> Result<Fixpoint> {
        self.advance();
        let kind = self.current()?.kind.clone();
        if let CoqTokenKind::Word(name) = kind {
            if self.early {
                return Ok(Fixpoint {
                    name,
                    binders: Vec::default(),
                    annotation: None,
                    typ: None,
                    term: Box::default(),
                });
            }

            self.advance();
            let mut binders = Vec::new();
            let mut annotation = None;
            let mut typ = None;

            loop {
                let mut stop = false;
                if self.current()?.kind == CoqTokenKind::BracketCurlyLeft
                    && self.peek(1)?.kind == CoqTokenKind::Word(STRUCT.to_string())
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
                term: self.parse_term(stop)?,
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
        let mut names = Vec::new();
        while let CoqTokenKind::Word(name) = &self.current()?.kind {
            names.push(name.clone());
            self.advance();
            if self.current()?.kind == CoqTokenKind::Comma {
                self.advance();
            }
        }
        self.advance();
        let typ = self.parse_term(|token| token == &CoqTokenKind::NewLine)?;
        self.advance();
        Ok(Hypothesis { names, typ })
    }

    fn stop_at_new_goal(token: &CoqTokenKind) -> bool {
        if let CoqTokenKind::Word(word) = token {
            if word.as_str() == "goal" {
                return true;
            }
        }
        token == &CoqTokenKind::NewLine
    }

    fn parse_goal(&mut self) -> Result<Goal> {
        self.skip_whitespace = false;
        let mut premise = Vec::new();
        while self.current()?.kind != CoqTokenKind::Eq {
            premise.push(self.parse_hypothesis()?);
        }
        self.skip_whitespace = true;
        self.skip_line();
        let conclusion = self.parse_term(Self::stop_at_new_goal)?;
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
            let conclusion = self.parse_term(Self::stop_at_new_goal)?;
            self.advance();
            goals.push(Goal {
                premise: Vec::new(),
                conclusion,
            });
        }

        Ok(goals)
    }

    fn parse_expression(&mut self) -> Result<CoqExpression> {
        println!("{}", self.slice);
        let token = self.current()?.clone();
        match token.kind {
            CoqTokenKind::Word(word) => {
                if let std::result::Result::Ok(number) = word.parse::<usize>() {
                    if let CoqTokenKind::Word(word) = &self.peek(1)?.kind {
                        if word.as_str() == "goal" || word.as_str() == "goals" {
                            return Ok(CoqExpression::Goal(self.parse_goals(number)?));
                        }
                    }
                    return Ok(CoqExpression::Tactic(self.slice.into()))
                }
                return match word.as_str() {
                    "Theorem" | "Lemma" | "Fact" | "Remark" | "Corollary" | "Proposition"
                    | "Property" => Ok(CoqExpression::Theorem(self.parse_theorem(word)?)),
                    "Axiom" | "Axioms" | "Conjecture" | "Conjectures" | "Parameter"
                    | "Parameters" | "Hypothesis" | "Hypotheses" | "Variable" | "Variables" => {
                        Ok(CoqExpression::Assumption(
                            self.parse_assumption(word, |token| token == &CoqTokenKind::Dot)?,
                        ))
                    }
                    "Inductive" => Ok(CoqExpression::Inductive(self.parse_inductive()?)),
                    "Definition" | "Example" => {
                        Ok(CoqExpression::Definition(self.parse_definition(word)?))
                    }
                    "Record" | "Structure" => Ok(CoqExpression::Record(self.parse_record(word)?)),
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
                    "From" => Ok(CoqExpression::From),
                    "Set" => Ok(CoqExpression::Set),
                    "Unset" => Ok(CoqExpression::Unset),
                    _ => {
                        if let std::result::Result::Ok(token) = self.peek(1) {
                            if token.kind == CoqTokenKind::Eq {
                                Ok(CoqExpression::PrintVariable(
                                    self.parse_print_variable(word)?,
                                ))
                            } else {
                                Ok(CoqExpression::Tactic(self.slice.into()))
                            }
                        } else {
                            Ok(CoqExpression::Tactic(self.slice.into()))
                        }
                    }
                };
            }
            CoqTokenKind::Star => {
                for _ in 0..3 {
                    if self.current()?.kind != CoqTokenKind::Star {
                        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                    }
                    self.advance();
                }
                if self.current()?.kind != CoqTokenKind::BracketSquareLeft {
                    bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                }
                self.advance();
                Ok(CoqExpression::Assumption(
                    self.parse_assumption("Axiom".to_string(), |token| {
                        token == &CoqTokenKind::BracketSquareRight
                    })?,
                ))
            }
            _ => bail!(ParserError::UnexpectedQuery),
        }
    }
}

#[derive(Clone, Copy)]
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

    fn get_open_binders_names(&mut self, binder: &OpenBinders) {
        match binder {
            OpenBinders::Binders(binders) => {
                for binder in binders {
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

    fn get_basic_term_names(&mut self, term: &BasicTerm) {
        match term {
            BasicTerm::Brackets(term) => self.get_term_names(term),
            BasicTerm::Custom(token) => {
                if let CoqTokenKind::Word(word) = &token.kind {
                    match self.mode {
                        NameCollectorMode::Seeing => self.see(word),
                        NameCollectorMode::Registering => self.register(word),
                    };
                }
            }
            BasicTerm::Match(mat) => {
                self.open();
                self.mode = NameCollectorMode::Registering;
                self.get_term_names(&mat.input);
                self.mode = NameCollectorMode::Seeing;

                for case in &mat.cases {
                    self.mode = NameCollectorMode::Registering;
                    self.get_term_names(&case.pattern);
                    self.mode = NameCollectorMode::Seeing;

                    self.get_term_names(&case.term);
                }
                self.close();
            }
        }
    }

    fn get_term_names(&mut self, term: &Term) {
        match term {
            Term::Quantifier(forall) => {
                self.open();
                self.get_open_binders_names(&forall.binder);
                self.get_term_names(&forall.has);
                self.close();
            }
            Term::If(term) => {
                self.get_term_names(&term.if_term);
                self.get_term_names(&term.then_term);
                self.get_term_names(&term.else_term);
            }
            Term::LetIn(LetIn::BasicLetIn(term)) => {
                self.open();
                self.register(&term.name);
                for binder in &term.binders {
                    self.get_binder_names(binder);
                }
                if let Some(typ) = &term.typ {
                    self.get_term_names(typ);
                }
                self.get_term_names(&term.def);
                self.get_term_names(&term.main);
                self.close();
            }
            Term::LetIn(LetIn::DestructLetIn(term)) => {
                self.open();
                for name in &term.names {
                    self.register(name);
                }
                self.get_term_names(&term.destruct);
                self.get_term_names(&term.main);
                self.close();
            }
            Term::Function(fun) => {
                self.open();
                self.get_open_binders_names(&fun.binder);
                self.get_term_names(&fun.term);
                self.close();
            }
            Term::Record(record) => {
                self.open();
                for field in &record.fields {
                    self.register(&field.name);
                    for binder in &field.binders {
                        self.get_binder_names(binder);
                    }
                    self.get_term_names(&field.term);
                }
            }
            Term::Application(app) => {
                let mode = self.mode;
                self.mode = NameCollectorMode::Seeing;
                self.get_basic_term_names(&app.fun);
                self.mode = mode;

                for arg in &app.args {
                    match arg {
                        ApplicationArgument::Simple(argument) => {
                            self.get_basic_term_names(&argument)
                        }
                        ApplicationArgument::Annotated(name, argument) => {
                            self.register(name);
                            self.get_term_names(argument);
                        }
                    }
                }
            }
            Term::BasicTerm(term) => self.get_basic_term_names(term),
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

    fn get_assumption_names(&mut self, assumption: &Assumption) {
        self.open();
        for name in &assumption.names {
            self.register(name);
        }
        self.get_term_names(&assumption.typ);
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
        self.register(&inductive.name);
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
        self.register(&definition.name);
        for binder in &definition.binders {
            self.get_binder_names(binder);
        }
        self.get_term_names(&definition.typ);
        self.close();
    }

    fn get_record_field_names(&mut self, field: &RecordField) {
        self.register(&field.name);
        if let Some(spec) = &field.spec {
            for binder in &spec.binders {
                self.get_binder_names(binder);
            }
            if let Some(typ) = &spec.typ {
                self.get_term_names(typ);
            }
            if let Some(term) = &spec.term {
                self.get_term_names(term);
            }
        }
    }

    fn get_record_names(&mut self, record: &Record) {
        self.open();
        self.register(&record.name);
        for binder in &record.binders {
            self.get_binder_names(binder);
        }
        if let Some(sort) = &record.sort {
            self.get_term_names(sort);
        }
        if let Some(body) = &record.body {
            for field in &body.fields {
                self.get_record_field_names(field);
            }
        }
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
            for name in &hypothesis.names {
                self.register(name);
            }
            self.get_term_names(&hypothesis.typ);
        }
        self.get_term_names(&goal.conclusion);
        self.close();
    }

    fn get_expression_names(&mut self, expression: &CoqExpression) {
        match expression {
            CoqExpression::Theorem(theorem) => self.get_theorem_names(theorem),
            CoqExpression::Assumption(assumption) => self.get_assumption_names(assumption),
            CoqExpression::Inductive(inductive) => self.get_inductive_names(inductive),
            CoqExpression::Definition(definition) => self.get_definition_names(definition),
            CoqExpression::Record(record) => self.get_record_names(record),
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
    let mut parser = CoqParser::new(query, false);
    parser.parse_expression()
}

pub fn parse_early(query: CoqTokenSlice) -> Result<CoqExpression> {
    let mut parser = CoqParser::new(query, true);
    parser.parse_expression()
}

pub fn get_names(expression: &CoqExpression) -> Vec<String> {
    let mut collector = NameCollector::new();
    collector.get_expression_names(expression);
    collector.collect()
}

#[cfg(test)]
mod tests {
    use crate::{
        lexer::{tokenize, CoqToken, CoqTokenKind, CoqTokenSlice},
        parser::{parse, NameCollector},
    };

    fn check_tokens(tokens: Vec<CoqToken>) {
        println!("{:?}", tokens);

        let expr = parse(CoqTokenSlice::from(tokens.as_slice())).unwrap();

        println!("{}", expr);
        println!("{:?}", expr);

        let mut collector = NameCollector::new();
        collector.get_expression_names(&expr);
        let names = collector.collect();

        println!("{:?}", names);
    }

    fn check(data: &str) {
        let mut tokens = tokenize(data).unwrap();
        tokens.push(CoqToken::new(CoqTokenKind::NewLine, 0, 0));
        check_tokens(tokens);
    }

    #[test]
    fn theorem_plus_n_sm() {
        check("Theorem plus_n_Sm : forall n m : nat, eq (S (Nat.add n m)) (Nat.add n (S m)).");
    }

    #[test]
    fn axiom() {
        check(
            "*** [ Extensionality_Ensembles : 
        forall (U : Type) (A B : Ensemble U) (_ : Same_set U A B), eq A B ]
        ",
        );
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
    fn definition_let() {
        check("Definition add_one (x : nat) : nat := let y := add x 1 in mut y y.");
    }

    #[test]
    fn definition_destruct_let() {
        check("Definition fst (p : pair nat nat) : nat := let (x, _) := p in x.");
    }

    #[test]
    fn fixpoint_example() {
        check(
            "Fixpoint example (n:nat) : nat :=
                    match n with
                    | O => O
                    | S n' => mult n (example n')
                    end.",
        );
    }

    #[test]
    fn fun_andb_definition() {
        check(
            "andb = 
            fun b1 b2 : bool => if b1 then b2 else false
                : bool -> bool -> bool
            
            Arguments andb (b1 b2)%bool_scope",
        );
    }

    #[test]
    fn fun_compact() {
        check(
            "compact = fun X : TopologicalSpace => forall ( C : Family X ) 
        ( _ : forall ( U : Ensemble X ) ( _ : In C U ) , open U ) 
        ( _ : eq ( FamilyUnion C ) Full_set ) , ex ( fun C' : Family X => and ( Finite C' ) 
        ( and ( Included C' C ) ( eq ( FamilyUnion C' ) Full_set ) ) ) 
        : forall _ : TopologicalSpace , Prop Arguments compact X ",
        );
    }

    #[test]
    fn fun_build_top() {
        check("Build_TopologicalSpace_from_open_basis = fun ( X : Type ) ( B : Family X ) 
        ( Hbasis : open_basis_cond B ) ( Hbasis_cover : open_basis_cover_cond B ) => 
        { | point_set := X ; 
            open := B_open B ; 
            open_family_union := fun ( F : Family X ) 
                ( H : forall ( S : Ensemble X ) ( _ : In F S ) , B_open B S ) => 
                OpenBases.Build_TopologicalSpace_from_open_basis_obligation_1 B F H ; 
            open_intersection2 := fun ( U V : Ensemble X ) ( H : B_open B U ) ( H0 : B_open B V ) => 
                OpenBases.Build_TopologicalSpace_from_open_basis_obligation_2 B Hbasis U V H H0 ; 
            open_full := OpenBases.Build_TopologicalSpace_from_open_basis_obligation_3 B Hbasis_cover | } : 
            forall ( X : Type ) ( B : Family X ) ( _ : open_basis_cond B ) 
                ( _ : open_basis_cover_cond B ) , TopologicalSpace");
    }

    #[test]
    fn fun_subspace() {
        check(
            "SubspaceTopology = fun ( X : TopologicalSpace ) ( A : Ensemble X ) => 
            WeakTopology.WeakTopology1 ( proj1_sig ( P := fun x : X => In A x ) ) : 
            forall ( X : TopologicalSpace ) ( _ : Ensemble X ) , TopologicalSpace",
        );
    }

    #[test]
    fn fixpoint_add_definition() {
        check(
            "Nat.add = k_whitespace
        fix add (n m : nat) {struct n} : nat :=
          match n with
          | 0 => m
          | S p => S (add p m)
          end
             : forall (_ : nat) (_ : nat), nat",
        );
    }

    #[test]
    fn record_top() {
        check("Record TopologicalSpace : Type := Build_TopologicalSpace { 
            point_set : Type ; open : forall _ : Ensemble point_set , Prop ; 
            open_family_union : forall ( F : Family point_set ) 
                ( _ : forall ( S : Ensemble point_set ) ( _ : In F S ) , open S ) , open ( FamilyUnion F ) ; 
            open_intersection2 : forall ( U V : Ensemble point_set ) ( _ : open U ) ( _ : open V ) , 
            open ( Intersection U V ) ; 
            open_full : open Full_set 
        } .");
    }

    #[test]
    fn record_filter() {
        check(
            "Record Filter ( X : Type ) : Type := Build_Filter { 
            filter_family : Family X ; 
            filter_intersection : forall ( S1 S2 : Ensemble X ) ( _ : In filter_family S1 ) 
                ( _ : In filter_family S2 ) , In filter_family ( Intersection S1 S2 ) ; 
            filter_upward_closed : forall ( S1 S2 : Ensemble X ) ( _ : In filter_family S1 ) 
                ( _ : Included S1 S2 ) , In filter_family S2 ; 
            filter_full : In filter_family Full_set ; 
            filter_empty : not ( In filter_family Empty_set ) 
        } .",
        )
    }

    #[test]
    fn goal() {
        check(
            "1 goal 
        X : TopologicalSpace 
        S : Ensemble X 
        = = = = = = = = = = = = = = = = = = = = = = = = = = = = 
        forall ( _ : compact X ) ( _ : closed S ) ( F : Family X ) 
        ( _ : forall ( U : Ensemble X ) ( _ : In F U ) , open U ) 
        ( _ : Included S ( FamilyUnion F ) ) , 
        ex 
        ( fun C : Ensemble ( Ensemble X ) => 
        and ( Finite C ) ( and ( Included C F ) ( Included S ( FamilyUnion C ) ) ) ) ",
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
