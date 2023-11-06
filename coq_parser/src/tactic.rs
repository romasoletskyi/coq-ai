use anyhow::{bail, Ok, Result};
use once_cell::sync::Lazy;

use crate::lexer::{CoqToken, CoqTokenKind, CoqTokenSlice};
use crate::parser::{BasicTerm, CoqParser, ParserError, Stopper, Term};
use crate::stop;

pub(crate) static AS: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("as")));
pub(crate) static BY: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("by")));
pub(crate) static ELSE: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("else")));
pub(crate) static END: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("end")));
pub(crate) static EQN: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("eqn")));
pub(crate) static IN: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("in")));
pub(crate) static PROOF: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("proof")));
pub(crate) static REC: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("rec")));
pub(crate) static REVERSE: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("reverse")));
pub(crate) static STRUCT: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("struct")));
pub(crate) static THEN: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("then")));
pub(crate) static TRYIF: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("tryif")));
pub(crate) static USING: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("using")));
pub(crate) static WITH: Lazy<CoqTokenKind> = Lazy::new(|| CoqTokenKind::Word(String::from("with")));

#[derive(Debug, PartialEq)]
struct Binding {
    name: String,
    term: Box<Term>,
}

#[derive(Debug, PartialEq)]
enum Bindings {
    Simple(Vec<Box<BasicTerm>>),
    Complex(Vec<Binding>),
}

#[derive(Debug, PartialEq)]
struct BasicTermWithBindings {
    term: Box<BasicTerm>,
    bindings: Option<Bindings>,
}

#[derive(Debug, PartialEq)]
struct AtomBinder {
    name: String,
}

#[derive(Debug, PartialEq)]
struct TypeBinder {
    names: Vec<String>,
    typ: Box<Term>,
}

#[derive(Debug, PartialEq)]
enum SimpleBinder {
    AtomBinder(AtomBinder),
    TypeBinder(TypeBinder),
}

#[derive(Debug, PartialEq)]
struct AliasDefinition {
    name: String,
    binders: Vec<SimpleBinder>,
    term: Box<Term>,
}

#[derive(Debug, PartialEq)]
struct ExactTactic {
    token: String,
    term: Box<BasicTerm>,
}

#[derive(Debug, PartialEq)]
struct HypIntroPattern {
    name: String,
    pattern: Option<IntroPattern>,
}

#[derive(Debug, PartialEq)]
struct ApplyTactic {
    token: String,
    terms: Vec<BasicTermWithBindings>,
    in_hyp: Option<Vec<HypIntroPattern>>,
}

#[derive(Debug, PartialEq)]
enum EqualityIntroPattern {
    Arrow,
    BackArrow,
    Equality(Vec<IntroPattern>),
}

#[derive(Debug, PartialEq)]
enum IntroPattern {
    Star,
    DoubleStar,
    Equality(EqualityIntroPattern),
    OrAnd(Vec<IntroPattern>),
    Named(String),
}

#[derive(Debug, PartialEq)]
struct IntrosTactic {
    token: String,
    patterns: Vec<IntroPattern>,
}

#[derive(Debug, PartialEq)]
struct ClearTactic {
    inverse: bool,
    names: Vec<String>,
}

#[derive(Debug, PartialEq)]
struct RememberTactic {
    token: String,
    term: Box<BasicTerm>,
    as_name: Option<String>,
    eqn: Option<String>,
}

#[derive(Debug, PartialEq)]
struct AssertTactic {
    token: String,
    name: String,
    typ: Box<Term>,
    by: Option<Box<HighTactic>>,
}

#[derive(Debug, PartialEq)]
struct PoseProofAssertTactic {
    token: String,
    name: String,
    term: Box<Term>,
}

#[derive(Debug, PartialEq)]
struct PoseProofExactTactic {
    token: String,
    term: Box<Term>,
    as_intro: Option<IntroPattern>,
}

#[derive(Debug, PartialEq)]
struct SpecializeTactic {
    term: BasicTermWithBindings,
    as_intro: Option<IntroPattern>,
}

#[derive(Debug, PartialEq)]
enum RewriterArrow {
    Arrow,
    BackArrow
}

#[derive(Debug, PartialEq)]
enum RewriterSelector {
    Question,
    Exclamation
}

#[derive(Debug, PartialEq)]
struct OrientedRewriter {
    arrow: Option<RewriterArrow>,
    natural: Option<usize>,
    selector: Option<RewriterSelector>,
    term: BasicTermWithBindings
}

#[derive(Debug, PartialEq)] 
struct RewriteTactic {
    rewriters: Vec<OrientedRewriter>,
    by: Option<Box<HighTactic>>
}

#[derive(Debug, PartialEq)]
struct ConstructorTactic {
    token: String,
    name: Option<String>,
    bindings: Option<Bindings>
}

#[derive(Debug, PartialEq)]
struct SplitTactic {
    token: String,
    bindings: Option<Bindings>
}

#[derive(Debug, PartialEq)]
struct ExistsTactic {
    token: String,
    bindings: Vec<Bindings>
}

#[derive(Debug, PartialEq)]
struct LeftRightTactic {
    token: String,
    bindings: Option<Bindings>
}

#[derive(Debug, PartialEq)]
struct InductionClause {
    arg: BasicTermWithBindings,
    as_intro: Option<IntroPattern>,
    eqn: Option<String>
}

#[derive(Debug, PartialEq)]
struct DestructInductionTactic {
    token: String,
    clauses: Vec<InductionClause>,
    principle: Option<BasicTermWithBindings>
}

#[derive(Debug, PartialEq)]
struct ElimTactic {
    token: String,
    term: BasicTermWithBindings,
    principle: Option<BasicTermWithBindings>
}

#[derive(Debug, PartialEq)]
struct DiscriminateTactic {
    token: String,
    arg: Option<BasicTermWithBindings>
}

#[derive(Debug, PartialEq)]
struct InjectionTactic {
    token: String,
    arg: Option<BasicTermWithBindings>,
    patterns: Option<Vec<IntroPattern>>
}

#[derive(Debug, PartialEq)]
struct InversionTactic {
    name: String,
    as_intro: Option<IntroPattern>,
    using_term: Option<Box<BasicTerm>>,
    in_names: Option<Vec<String>>
}

#[derive(Debug, PartialEq)]
enum SimpleTactic {
    Exact(ExactTactic),
    Assumption(String),
    Refine(Box<BasicTerm>),
    Apply(ApplyTactic),
    Intro(String),
    Intros(IntrosTactic),
    Clear(ClearTactic),
    Remember(RememberTactic),
    Assert(AssertTactic),
    Cut(Box<BasicTerm>),
    PoseProofAssert(PoseProofAssertTactic),
    PoseProofExact(PoseProofExactTactic),
    Specialize(SpecializeTactic),
    Generalize(Vec<Box<BasicTerm>>),
    Absurd(Box<BasicTerm>),
    Contradiction(Option<BasicTermWithBindings>),
    Contradict(String),
    Exfalso,
    Reflexivity,
    FEqual,
    Rewrite(RewriteTactic),
    Subst(Vec<String>),
    Unfold(Vec<String>),
    Fold(Vec<Box<BasicTerm>>),
    Constructor(ConstructorTactic),
    Split(SplitTactic),
    Exists(ExistsTactic),
    LeftRight(LeftRightTactic),
    DestructInduction(DestructInductionTactic),
    Elim(ElimTactic),
    Discriminate(DiscriminateTactic),
    Injection(InjectionTactic),
    Inversion(InversionTactic)
}

#[derive(Debug, PartialEq)]
enum MatchKey {
    Match,
    LazyMatch,
    MultiMatch,
}

#[derive(Debug, PartialEq)]
struct MatchTerm(Box<Term>);

#[derive(Debug, PartialEq)]
enum MatchPattern {
    Type(MatchTerm),
    Binder(MatchTerm),
    TypedBinder((MatchTerm, MatchTerm)),
    Bracket((MatchTerm, MatchTerm)),
}

#[derive(Debug, PartialEq)]
struct MatchHypothesis {
    name: String,
    pattern: MatchPattern,
}

#[derive(Debug, PartialEq)]
struct MatchGoalPattern {
    hyp: Vec<MatchHypothesis>,
    goal: MatchTerm,
}

#[derive(Debug, PartialEq)]
struct MatchCase {
    pattern: Option<MatchGoalPattern>,
    expr: Box<LtacExpression>,
}

#[derive(Debug, PartialEq)]
struct MatchGoal {
    key: MatchKey,
    reverse: bool,
    cases: Vec<MatchCase>,
}

#[derive(Debug, PartialEq)]
enum LowTactic {
    MatchGoal(MatchGoal),
    Term(Box<Term>),
    ForEach(Box<ForEachGoal>),
    Bracket(Box<LtacExpression>),
    SimpleTactic(Box<SimpleTactic>),
}

#[derive(Debug, PartialEq)]
struct TryIf {
    if_term: Box<LtacExpression>,
    then_term: Box<LtacExpression>,
    else_term: Box<LtacExpression>,
}

#[derive(Debug, PartialEq)]
enum MiddleTactic {
    Branch((Box<LowTactic>, Box<MiddleTactic>)),
    BranchBinder((Box<LowTactic>, Box<BinderTactic>)),
    First((Box<LowTactic>, Box<MiddleTactic>)),
    FirstBinder((Box<LowTactic>, Box<BinderTactic>)),
    TryIf(TryIf),
    Simple(Box<LowTactic>),
}

#[derive(Debug, PartialEq)]
struct Do {
    num: usize,
    term: Box<HighTactic>,
}

#[derive(Debug, PartialEq)]
enum HighTactic {
    Try(Box<HighTactic>),
    Do(Do),
    Repeat(Box<HighTactic>),
    Simple(Box<MiddleTactic>),
}

#[derive(Debug, PartialEq)]
struct ForEachGoal {
    tactics: Vec<Box<LtacExpression>>,
}

#[derive(Debug, PartialEq)]
enum MainTactic {
    Simple(Box<HighTactic>),
    ForEach((Box<HighTactic>, Box<ForEachGoal>)),
    ChainTactic((Box<HighTactic>, Box<HighTactic>)),
    ChainBinder((Box<HighTactic>, Box<BinderTactic>)),
}

#[derive(Debug, PartialEq)]
struct Fun {
    names: Vec<String>,
    value: Box<LtacExpression>,
}

#[derive(Debug, PartialEq)]
struct SimpleClause {
    name: String,
    expr: Box<LtacExpression>,
}

#[derive(Debug, PartialEq)]
struct LetClause {
    ident: String,
    names: Vec<String>,
    expr: Box<LtacExpression>,
}

#[derive(Debug, PartialEq)]
struct Let {
    rec: bool,
    clause: LetClause,
    with: Vec<LetClause>,
    expr: Box<LtacExpression>,
}

#[derive(Debug, PartialEq)]
enum BinderTactic {
    Fun(Fun),
    Let(Let),
}

#[derive(Debug, PartialEq)]
pub struct MainExpression {
    tactic: Box<MainTactic>,
}

#[derive(Debug, PartialEq)]
pub struct BinderExpression {
    binder: Box<BinderTactic>,
}

#[derive(Debug, PartialEq)]
pub enum LtacExpression {
    Simple(MainExpression),
    Binder(BinderExpression),
}

struct LtacParser<'a> {
    slice: CoqTokenSlice<'a>,
    index: usize,
    skip_whitespace: bool,
}

impl<'a> LtacParser<'a> {
    fn new(slice: CoqTokenSlice<'a>) -> Self {
        LtacParser {
            slice,
            index: 0,
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

    fn parse_coq<T, F>(&mut self, fun: F) -> T
    where
        F: FnOnce(&mut CoqParser) -> T,
    {
        let mut slice = self.slice;
        slice.cut(self.index);
        let mut parser = CoqParser::new(slice, false);
        let result = fun(&mut parser);
        self.index += parser.get_index();
        result
    }

    fn parse_coq_term(&mut self, stop: Stopper) -> Result<Box<Term>> {
        self.parse_coq(|parser| parser.parse_term(stop))
    }

    fn parse_coq_basic_term(&mut self) -> Result<Box<BasicTerm>> {
        self.parse_coq(|parser| parser.parse_basic_term())
    }

    fn parse_name(&mut self) -> Result<String> {
        let token = self.current()?.clone();
        let name = match token.kind {
            CoqTokenKind::Word(name) => Ok(name),
            CoqTokenKind::Underscore => Ok("_".to_string()),
            _ => bail!(ParserError::UnexpectedToken(token.clone())),
        };
        self.advance();
        name
    }

    fn parse_as_name(&mut self) -> Result<Option<String>> {
        if self.current()?.kind == *AS {
            self.advance();
            Ok(Some(self.parse_name()?))
        } else {
            Ok(None)
        }
    }

    fn check_binding(&mut self) -> Result<bool> {
        let bracket = self.current()?.kind == CoqTokenKind::BracketLeft;
        let name = match self.peek(1)?.kind {
            CoqTokenKind::Word(_) => true,
            CoqTokenKind::Underscore => true,
            _ => false,
        };
        let define = self.peek(2)?.kind == CoqTokenKind::Define;
        Ok(bracket && name && define)
    }

    fn parse_let_clause(&mut self, stop: Stopper) -> Result<LetClause> {
        let ident = self.parse_name()?;

        let mut names = Vec::new();
        while self.current()?.kind != CoqTokenKind::Define {
            names.push(self.parse_name()?);
        }

        self.advance();
        Ok(LetClause {
            ident,
            names,
            expr: self.parse_expression(stop)?,
        })
    }

    fn parse_let(&mut self, stop: Stopper) -> Result<Let> {
        self.advance();
        let rec = *REC == self.current()?.kind;
        if rec {
            self.advance();
        }
        let clause = self.parse_let_clause(stop!(
            *IN,
            *WITH
        ))?;
        let mut with = Vec::new();
        while self.current()?.kind != *IN {
            with.push(self.parse_let_clause(stop!(
                *IN,
                *WITH
            ))?);
        }
        Ok(Let {
            rec,
            clause,
            with,
            expr: self.parse_expression(stop)?,
        })
    }

    fn parse_fun(&mut self, stop: Stopper) -> Result<Fun> {
        self.advance();

        let mut names = Vec::new();
        while self.current()?.kind != CoqTokenKind::Case {
            names.push(self.parse_name()?);
        }

        self.advance();
        Ok(Fun {
            names,
            value: self.parse_expression(stop)?,
        })
    }

    fn parse_tryif(&mut self, stop: Stopper) -> Result<TryIf> {
        self.advance();
        let if_term = self.parse_expression(stop!(*THEN))?;
        self.advance();
        let then_term = self.parse_expression(stop!(*ELSE))?;
        Ok(TryIf {
            if_term,
            then_term,
            else_term: self.parse_expression(stop)?,
        })
    }

    fn parse_match_key(&mut self) -> Result<Option<MatchKey>> {
        if let CoqTokenKind::Word(word) = &self.current()?.kind {
            match word.as_str() {
                "match" => Ok(Some(MatchKey::Match)),
                "lazymatch" => Ok(Some(MatchKey::LazyMatch)),
                "multimatch" => Ok(Some(MatchKey::MultiMatch)),
                _ => Ok(None),
            }
        } else {
            Ok(None)
        }
    }

    fn parse_match_term(&mut self, stop: Stopper) -> Result<MatchTerm> {
        Ok(MatchTerm(self.parse_coq_term(stop)?))
    }

    fn parse_match_pattern(&mut self, stop: Stopper) -> Result<MatchPattern> {
        if self.current()?.kind == CoqTokenKind::Colon {
            self.advance();
            return Ok(MatchPattern::Type(self.parse_match_term(stop)?));
        }
        if self.current()?.kind == CoqTokenKind::Case {
            self.advance();
            if self.current()?.kind == CoqTokenKind::BracketSquareLeft {
                self.advance();
                let binder = self.parse_match_term(stop!(CoqTokenKind::BracketSquareRight))?;
                self.advance();
                self.advance();
                return Ok(MatchPattern::Bracket((
                    binder,
                    self.parse_match_term(stop)?,
                )));
            }
            let match_stop = stop.clone();
            let term = self.parse_match_term(match_stop.add(&CoqTokenKind::Colon))?;
            if self.current()?.kind == CoqTokenKind::Colon {
                return Ok(MatchPattern::TypedBinder((
                    term,
                    self.parse_match_term(stop)?,
                )));
            } else {
                return Ok(MatchPattern::Binder(term));
            }
        }
        bail!(ParserError::UnexpectedToken(self.current()?.clone()))
    }

    fn parse_match_hypothesis(&mut self, stop: Stopper) -> Result<MatchHypothesis> {
        Ok(MatchHypothesis {
            name: self.parse_name()?,
            pattern: self.parse_match_pattern(stop)?,
        })
    }

    fn parse_match_goal(&mut self, key: MatchKey) -> Result<MatchGoal> {
        self.advance();
        let reverse = if self.current()?.kind == *REVERSE {
            self.advance();
            true
        } else {
            false
        };
        self.advance();
        self.advance();

        let mut cases = Vec::new();
        while self.current()?.kind != *END {
            if self.current()?.kind == CoqTokenKind::Pipe {
                self.advance();
            }
            let pattern =
                if self.current()?.kind == CoqTokenKind::Underscore {
                    None
                } else {
                    if self.current()?.kind == CoqTokenKind::BracketSquareLeft {
                        self.advance();
                    }

                    let mut hyp = Vec::new();
                    while self.current()?.kind != CoqTokenKind::Pipe {
                        hyp.push(self.parse_match_hypothesis(stop!(
                            CoqTokenKind::Comma,
                            CoqTokenKind::Pipe
                        ))?);
                        if self.current()?.kind == CoqTokenKind::Comma {
                            self.advance();
                        }
                    }

                    self.advance();
                    self.advance();
                    let goal = self.parse_match_term(stop!(
                        CoqTokenKind::Case,
                        CoqTokenKind::BracketSquareRight
                    ))?;
                    Some(MatchGoalPattern { hyp, goal })
                };
            cases.push(MatchCase {
                pattern,
                expr: self.parse_expression(stop!(
                    *END,
                    CoqTokenKind::Pipe
                ))?,
            });
        }

        Ok(MatchGoal {
            key,
            reverse,
            cases,
        })
    }

    fn collect_intro_patterns(
        &mut self,
        skip: fn(&CoqTokenKind) -> bool,
        stop: fn(&CoqTokenKind) -> bool,
    ) -> Result<Vec<IntroPattern>> {
        let mut patterns = Vec::new();
        while !stop(&self.current()?.kind) {
            patterns.push(self.parse_intro_pattern()?);
            if skip(&self.current()?.kind) {
                self.advance();
            }
        }
        Ok(patterns)
    }

    fn parse_intro_pattern(&mut self) -> Result<IntroPattern> {
        match self.current()?.kind {
            CoqTokenKind::Star => {
                self.advance();
                if self.current()?.kind == CoqTokenKind::Star {
                    self.advance();
                    Ok(IntroPattern::DoubleStar)
                } else {
                    Ok(IntroPattern::Star)
                }
            }
            CoqTokenKind::BracketSquareLeft => {
                let stop = |token: &_| token == &CoqTokenKind::BracketSquareRight;
                self.advance();
                if self.current()?.kind == CoqTokenKind::Eq {
                    self.advance();
                    let patterns = self.collect_intro_patterns(|_| false, stop)?;
                    self.advance();
                    Ok(IntroPattern::Equality(EqualityIntroPattern::Equality(
                        patterns,
                    )))
                } else {
                    let patterns = self
                        .collect_intro_patterns(|token: &_| token == &CoqTokenKind::Pipe, stop)?;
                    self.advance();
                    Ok(IntroPattern::OrAnd(patterns))
                }
            }
            CoqTokenKind::BracketLeft => {
                self.advance();
                let patterns = self.collect_intro_patterns(
                    |token| token == &CoqTokenKind::Comma || token == &CoqTokenKind::Ampersand,
                    |token| token == &CoqTokenKind::BracketRight,
                )?;
                self.advance();
                Ok(IntroPattern::OrAnd(patterns))
            }
            CoqTokenKind::Arrow => Ok(IntroPattern::Equality(EqualityIntroPattern::Arrow)),
            CoqTokenKind::BackArrow => Ok(IntroPattern::Equality(EqualityIntroPattern::BackArrow)),
            _ => Ok(IntroPattern::Named(self.parse_name()?)),
        }
    }

    fn parse_as_intro_pattern(&mut self) -> Result<Option<IntroPattern>> {
        if self.current()?.kind == *AS {
            self.advance();
            Ok(Some(self.parse_intro_pattern()?))
        } else {
            Ok(None)
        }
    }

    fn parse_simple_binder(&mut self) -> Result<SimpleBinder> {
        if self.current()?.kind == CoqTokenKind::BracketLeft {
            self.advance();
            let mut names = Vec::new();
            while self.current()?.kind != CoqTokenKind::Colon {
                names.push(self.parse_name()?);
            }
            self.advance();
            let typ = self.parse_coq_term(stop!(CoqTokenKind::BracketRight))?;
            self.advance();
            Ok(SimpleBinder::TypeBinder(TypeBinder { names, typ }))
        } else {
            Ok(SimpleBinder::AtomBinder(AtomBinder {
                name: self.parse_name()?,
            }))
        }
    }

    fn parse_bindings(&mut self, stop: Stopper) -> Result<Bindings> {
        if self.check_binding()? {
            let mut bindings = Vec::new();
            while !stop.check(&self.current()?.kind) {
                self.advance();
                let name = self.parse_name()?;
                self.advance();
                let term = self.parse_coq_term(stop!(CoqTokenKind::BracketRight))?;
                self.advance();
                bindings.push(Binding { name, term })
            }
            Ok(Bindings::Complex(bindings))
        } else {
            let mut bindings = Vec::new();
            while !stop.check(&self.current()?.kind) {
                bindings.push(self.parse_coq_basic_term()?);
            }
            Ok(Bindings::Simple(bindings))
        }
    }

    fn parse_with_bindings(&mut self, stop: Stopper) -> Result<Option<Bindings>> {
        if self.current()?.kind == *WITH {
            self.advance();
            Ok(Some(self.parse_bindings(stop)?))
        } else {
            Ok(None)
        }
    }

    fn parse_basic_term_with_bindings(&mut self, stop: Stopper) -> Result<BasicTermWithBindings> {
        let term = self.parse_coq_basic_term()?;
        let bindings = if self.current()?.kind == *WITH {
            Some(self.parse_bindings(stop)?)
        } else {
            None
        };
        Ok(BasicTermWithBindings { term, bindings })
    }

    fn parse_alias_definition(&mut self) -> Result<AliasDefinition> {
        if self.current()?.kind != CoqTokenKind::BracketLeft {
            bail!(ParserError::UnexpectedToken(self.current()?.clone()))
        }
        self.advance();
        let name = self.parse_name()?;

        let mut binders = Vec::new();
        while self.current()?.kind != CoqTokenKind::Define {
            binders.push(self.parse_simple_binder()?)
        }

        self.advance();
        let term = self.parse_coq_term(stop!(CoqTokenKind::BracketRight))?;
        self.advance();
        Ok(AliasDefinition {
            name,
            binders,
            term,
        })
    }

    fn parse_rewriter(&mut self, stop: Stopper) -> Result<OrientedRewriter> {
        let arrow = match self.current()?.kind {
            CoqTokenKind::Arrow => {
                self.advance();
                Some(RewriterArrow::Arrow)
            }
            CoqTokenKind::BackArrow => {
                self.advance();
                Some(RewriterArrow::BackArrow)
            }
            _ => None
        };
        let natural = if let CoqTokenKind::Word(word) = &self.current()?.kind {
            if let std::result::Result::Ok(number) = word.parse::<usize>() {
                Some(number)
            } else {
                None
            }
        } else {
            None
        };
        let selector = match self.current()?.kind {
            CoqTokenKind::Question => {
                self.advance();
                Some(RewriterSelector::Question)
            }
            CoqTokenKind::Exclamation => {
                self.advance();
                Some(RewriterSelector::Exclamation)
            }
            _ => None
        };
        Ok(OrientedRewriter { arrow, natural, selector, term: self.parse_basic_term_with_bindings(stop)?})
    }

    fn parse_induction_clause(&mut self, stop: Stopper) -> Result<InductionClause> {
        let arg_stop = stop.clone();
        let arg = self.parse_basic_term_with_bindings(arg_stop.add(&AS).add(&EQN))?;
        let as_intro = self.parse_as_intro_pattern()?;
        let eqn = if self.current()?.kind == *EQN {
            self.advance();
            self.advance();
            Some(self.parse_name()?)
        } else {
            None
        };
        Ok(InductionClause { arg, as_intro, eqn })
    }

    fn parse_simple_tactic(&mut self, stop: Stopper) -> Result<Option<Box<SimpleTactic>>> {
        if let CoqTokenKind::Word(word) = &self.current()?.kind {
            match word.as_str() {
                "exact" | "eexact" => {
                    let token = word.clone();
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Exact(ExactTactic {
                        token,
                        term: self.parse_coq_basic_term()?,
                    }))))
                }
                "assumption" | "eassumption" => {
                    let token = word.clone();
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Assumption(token))))
                }
                "refine" => {
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Refine(
                        self.parse_coq_basic_term()?,
                    ))))
                }
                "apply" => {
                    let token = word.clone();
                    self.advance();
                    let mut in_stop = stop.clone();
                    in_stop = in_stop.add(&IN);

                    let mut terms = Vec::new();
                    while !in_stop.check(&self.current()?.kind) {
                        let term_stop = in_stop.clone();
                        terms.push(
                            self.parse_basic_term_with_bindings(
                                term_stop.add(&CoqTokenKind::Comma),
                            )?,
                        );
                        if self.current()?.kind == CoqTokenKind::Comma {
                            self.advance();
                        }
                    }

                    let in_hyp = if self.current()?.kind == *IN {
                        self.advance();
                        let mut patterns = Vec::new();
                        while !stop.check(&self.current()?.kind) {
                            patterns.push(HypIntroPattern {
                                name: self.parse_name()?,
                                pattern: self.parse_as_intro_pattern()?,
                            });
                        }
                        Some(patterns)
                    } else {
                        None
                    };

                    Ok(Some(Box::new(SimpleTactic::Apply(ApplyTactic {
                        token,
                        terms,
                        in_hyp,
                    }))))
                }
                "intro" => {
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Intro(self.parse_name()?))))
                }
                "intros" | "eintros" => {
                    let token = word.clone();
                    self.advance();
                    let mut patterns = Vec::new();
                    while !stop.check(&self.current()?.kind) {
                        patterns.push(self.parse_intro_pattern()?);
                    }
                    Ok(Some(Box::new(SimpleTactic::Intros(IntrosTactic {
                        token,
                        patterns,
                    }))))
                }
                "clear" => {
                    self.advance();
                    let inverse = if self.current()?.kind == CoqTokenKind::Dash {
                        self.advance();
                        true
                    } else {
                        false
                    };
                    let mut names = Vec::new();
                    while !stop.check(&self.current()?.kind) {
                        names.push(self.parse_name()?);
                    }
                    Ok(Some(Box::new(SimpleTactic::Clear(ClearTactic {
                        inverse,
                        names,
                    }))))
                }
                "remember" | "eremember" => {
                    let token = word.clone();
                    self.advance();
                    let term = self.parse_coq_basic_term()?;
                    let as_name = self.parse_as_name()?;
                    let eqn = if self.current()?.kind == *EQN {
                        self.advance();
                        self.advance();
                        Some(self.parse_name()?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Remember(RememberTactic {
                        token,
                        term,
                        as_name,
                        eqn,
                    }))))
                }
                "assert" | "eassert" | "enough" | "eenough" => {
                    let token = word.clone();
                    self.advance();
                    if self.current()?.kind != CoqTokenKind::BracketLeft {
                        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                    }
                    self.advance();
                    let name = self.parse_name()?;
                    self.advance();
                    let typ = self.parse_coq_term(stop!(CoqTokenKind::BracketRight))?;
                    self.advance();
                    let by = if self.current()?.kind == *BY {
                        self.advance();
                        Some(self.parse_high_tactic(stop)?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Assert(AssertTactic {
                        token,
                        name,
                        typ,
                        by,
                    }))))
                }
                "cut" => {
                    self.advance();
                    let typ = self.parse_coq_basic_term()?;
                    Ok(Some(Box::new(SimpleTactic::Cut(typ))))
                }
                "pose" | "epose" => {
                    let token = word.clone();
                    self.advance();
                    if self.current()?.kind == *PROOF {
                        self.advance();
                        let tactic = if self.current()?.kind == CoqTokenKind::BracketLeft {
                            self.advance();
                            let name = self.parse_name()?;
                            self.advance();
                            let term = self.parse_coq_term(stop!(CoqTokenKind::BracketRight))?;
                            SimpleTactic::PoseProofAssert(PoseProofAssertTactic {
                                token,
                                name,
                                term,
                            })
                        } else {
                            let term_stop = stop.clone();
                            let term = self.parse_coq_term(
                                term_stop.add(&AS),
                            )?;
                            let as_intro = self.parse_as_intro_pattern()?;
                            SimpleTactic::PoseProofExact(PoseProofExactTactic {
                                token,
                                term,
                                as_intro,
                            })
                        };
                        Ok(Some(Box::new(tactic)))
                    } else {
                        bail!(ParserError::UnexpectedToken(self.current()?.clone()))
                    }
                }
                "specialize" => {
                    self.advance();
                    let term_stop = stop.clone();
                    let term = self.parse_basic_term_with_bindings(
                        term_stop.add(&AS),
                    )?;
                    let as_intro = self.parse_as_intro_pattern()?;
                    Ok(Some(Box::new(SimpleTactic::Specialize(SpecializeTactic {
                        term,
                        as_intro,
                    }))))
                }
                "generalize" => {
                    self.advance();
                    let mut terms = Vec::new();
                    while !stop.check(&self.current()?.kind) {
                        terms.push(self.parse_coq_basic_term()?);
                    }
                    Ok(Some(Box::new(SimpleTactic::Generalize(terms))))
                }
                "absurd" => {
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Absurd(
                        self.parse_coq_basic_term()?,
                    ))))
                }
                "contradiction" => {
                    self.advance();
                    let term = if stop.check(&self.current()?.kind) {
                        None
                    } else {
                        Some(self.parse_basic_term_with_bindings(stop)?)
                    };
                    Ok(Some(Box::new(SimpleTactic::Contradiction(term))))
                }
                "contradict" => {
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Contradict(self.parse_name()?))))
                }
                "exfalso" => {
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Exfalso)))
                }
                "reflexivity" => {
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Reflexivity)))
                }
                "f_equal" => {
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::FEqual)))
                }
                "rewrite" => {
                    self.advance();
                    let mut by_stop = stop.clone();
                    by_stop = by_stop.add(&BY);
                    let mut rewriters = Vec::new();
                    while !by_stop.check(&self.current()?.kind) {
                        let term_stop = by_stop.clone();
                        rewriters.push(self.parse_rewriter(term_stop.add(&CoqTokenKind::Comma))?);
                    }
                    let by = if self.current()?.kind == *BY {
                        self.advance();
                        Some(self.parse_high_tactic(stop)?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Rewrite(RewriteTactic { rewriters, by }))))
                }
                "subst" => {
                    self.advance();
                    let mut names = Vec::new();
                    while !stop.check(&self.current()?.kind) {
                        names.push(self.parse_name()?);
                    }
                    Ok(Some(Box::new(SimpleTactic::Subst(names))))
                }
                "unfold" => {
                    self.advance();
                    let mut names = Vec::new();
                    while !stop.check(&self.current()?.kind) {
                        names.push(self.parse_name()?);
                    }
                    Ok(Some(Box::new(SimpleTactic::Unfold(names))))
                }
                "fold" => {
                    self.advance();
                    let mut terms = Vec::new();
                    while !stop.check(&self.current()?.kind) {
                        terms.push(self.parse_coq_basic_term()?);
                    }
                    Ok(Some(Box::new(SimpleTactic::Fold(terms))))
                }
                "constructor" | "econstructor" => {
                    let token = word.clone();
                    self.advance();
                    let name = if !stop.check(&self.current()?.kind) && self.current()?.kind != *WITH {
                        Some(self.parse_name()?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Constructor(ConstructorTactic{ token, name, bindings: self.parse_with_bindings(stop)? }))))
                }
                "split" | "esplit" => {
                    let token = word.clone();
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::Split(SplitTactic { token, bindings: self.parse_with_bindings(stop)? }))))
                }
                "exists" | "eexists" => {
                    let token = word.clone();
                    self.advance();
                    let mut bindings = Vec::new();
                    while stop.check(&self.current()?.kind) {
                        let bind_stop = stop.clone();
                        bindings.push(self.parse_bindings(bind_stop.add(&CoqTokenKind::Comma))?);
                        if self.current()?.kind == CoqTokenKind::Comma {
                            self.advance();
                        }
                    }
                    Ok(Some(Box::new(SimpleTactic::Exists(ExistsTactic { token, bindings }))))
                }
                "left" | "right" | "eleft" | "eright" => {
                    let token = word.clone();
                    self.advance();
                    Ok(Some(Box::new(SimpleTactic::LeftRight(LeftRightTactic { token, bindings: self.parse_with_bindings(stop)? }))))
                }
                "destruct" | "edestruct" | "induction" | "einduction" => {
                    let token = word.clone();
                    self.advance();
                    let mut using_stop = stop.clone();
                    using_stop = using_stop.add(&USING);
                    let mut clauses = Vec::new();
                    while !using_stop.check(&self.current()?.kind) {
                        let clause_stop = using_stop.clone();
                        clauses.push(self.parse_induction_clause(clause_stop.add(&CoqTokenKind::Comma))?)
                    }
                    let principle = if self.current()?.kind == *USING {
                        self.advance();
                        Some(self.parse_basic_term_with_bindings(stop)?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::DestructInduction(DestructInductionTactic { token, clauses, principle }))))
                }
                "elim" | "eelim" => {
                    let token = word.clone();
                    self.advance();
                    let using_stop = stop.clone();
                    let term = self.parse_basic_term_with_bindings(using_stop.add(&USING))?;
                    let principle = if self.current()?.kind == *USING {
                        self.advance();
                        Some(self.parse_basic_term_with_bindings(stop)?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Elim(ElimTactic{ token, term, principle }))))
                }
                "discriminate" | "ediscriminate" => {
                    let token = word.clone();
                    self.advance();
                    let arg = if !stop.check(&self.current()?.kind) {
                        Some(self.parse_basic_term_with_bindings(stop)?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Discriminate(DiscriminateTactic{ token, arg }))))
                }
                "injection" | "einjection" => {
                    let token = word.clone();
                    self.advance();
                    let mut as_stop = stop.clone();
                    as_stop = as_stop.add(&AS);
                    let arg = if !as_stop.check(&self.current()?.kind) {
                        Some(self.parse_basic_term_with_bindings(as_stop)?)
                    } else {
                        None
                    };
                    let patterns = if self.current()?.kind == *AS {
                        self.advance();
                        let mut patterns = Vec::new();
                        while !stop.check(&self.current()?.kind) {
                            patterns.push(self.parse_intro_pattern()?);
                        }
                        Some(patterns)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Injection(InjectionTactic { token, arg, patterns }))))
                }
                "inversion" => {
                    self.advance();
                    let name = self.parse_name()?;
                    let (as_intro, using_term) = if self.current()?.kind == *USING {
                        self.advance();
                        (None, Some(self.parse_coq_basic_term()?))
                    } else {
                        (self.parse_as_intro_pattern()?, None)
                    };
                    let in_names = if self.current()?.kind == *IN {
                        let mut names = Vec::new();
                        while !stop.check(&self.current()?.kind) {
                            names.push(self.parse_name()?);
                        }
                        Some(names)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Inversion(InversionTactic { name, as_intro, using_term, in_names }))))
                }
                _ => Ok(None),
            }
        } else {
            Ok(None)
        }
    }

    fn parse_low_tactic(&mut self, stop: Stopper) -> Result<Box<LowTactic>> {
        if self.current()?.kind == CoqTokenKind::BracketLeft {
            let expr = self.parse_expression(stop!(CoqTokenKind::BracketRight))?;
            self.advance();
            return Ok(Box::new(LowTactic::Bracket(expr)));
        }
        if self.current()?.kind == CoqTokenKind::BracketSquareLeft {
            return Ok(Box::new(LowTactic::ForEach(self.parse_for_each_goal()?)));
        }
        if let Some(key) = self.parse_match_key()? {
            return Ok(Box::new(LowTactic::MatchGoal(self.parse_match_goal(key)?)));
        }
        if let Some(tactic) = self.parse_simple_tactic(stop.clone())? {
            return Ok(Box::new(LowTactic::SimpleTactic(tactic)));
        }
        Ok(Box::new(LowTactic::Term(self.parse_coq_term(stop)?)))
    }

    fn parse_middle_tactic(&mut self, stop: Stopper) -> Result<Box<MiddleTactic>> {
        if self.current()?.kind == *TRYIF {
            return Ok(Box::new(MiddleTactic::TryIf(self.parse_tryif(stop)?)));
        }
        let tactic_stop = stop.clone();
        let tactic =
            self.parse_low_tactic(tactic_stop.add(&CoqTokenKind::Pipe).add(&CoqTokenKind::Plus))?;
        if self.current()?.kind == CoqTokenKind::Pipe {
            self.advance();
            self.advance();
            if let Some(binder) = self.parse_binder(stop.clone())? {
                return Ok(Box::new(MiddleTactic::FirstBinder((tactic, binder))));
            }
            return Ok(Box::new(MiddleTactic::First((
                tactic,
                self.parse_middle_tactic(stop)?,
            ))));
        }
        if self.current()?.kind == CoqTokenKind::Plus {
            self.advance();
            if let Some(binder) = self.parse_binder(stop.clone())? {
                return Ok(Box::new(MiddleTactic::BranchBinder((tactic, binder))));
            }
            return Ok(Box::new(MiddleTactic::Branch((
                tactic,
                self.parse_middle_tactic(stop)?,
            ))));
        }
        Ok(Box::new(MiddleTactic::Simple(tactic)))
    }

    fn parse_high_tactic(&mut self, stop: Stopper) -> Result<Box<HighTactic>> {
        if let CoqTokenKind::Word(word) = &self.current()?.kind {
            match word.as_str() {
                "try" => {
                    self.advance();
                    return Ok(Box::new(HighTactic::Try(self.parse_high_tactic(stop)?)));
                }
                "do" => {
                    self.advance();
                    if let std::result::Result::Ok(num) = self.parse_name()?.parse::<usize>() {
                        return Ok(Box::new(HighTactic::Do(Do {
                            num,
                            term: self.parse_high_tactic(stop)?,
                        })));
                    } else {
                        bail!(ParserError::UnexpectedToken(self.current()?.clone()));
                    }
                }
                "repeat" => {
                    self.advance();
                    return Ok(Box::new(HighTactic::Repeat(self.parse_high_tactic(stop)?)));
                }
                _ => {}
            }
        }
        Ok(Box::new(HighTactic::Simple(
            self.parse_middle_tactic(stop)?,
        )))
    }

    fn parse_for_each_goal(&mut self) -> Result<Box<ForEachGoal>> {
        self.advance();
        if self.current()?.kind == CoqTokenKind::Greater {
            self.advance();
        }
        let mut tactics = Vec::new();
        while self.current()?.kind != CoqTokenKind::BracketSquareRight {
            if self.current()?.kind == CoqTokenKind::Dot {
                self.advance();
                self.advance();
            } else {
                tactics.push(self.parse_expression(stop!(
                    CoqTokenKind::BracketSquareRight,
                    CoqTokenKind::Pipe
                ))?);
            }
            if self.current()?.kind == CoqTokenKind::Pipe {
                self.advance();
            }
        }
        self.advance();
        Ok(Box::new(ForEachGoal { tactics }))
    }

    fn parse_main_tactic(&mut self, stop: Stopper) -> Result<Box<MainTactic>> {
        let high_stop = stop.clone();
        let tactic = self.parse_high_tactic(high_stop.add(&CoqTokenKind::SemiColon))?;
        if self.current()?.kind == CoqTokenKind::SemiColon {
            self.advance();
            if self.current()?.kind == CoqTokenKind::BracketSquareLeft {
                return Ok(Box::new(MainTactic::ForEach((
                    tactic,
                    self.parse_for_each_goal()?,
                ))));
            }
            if let Some(binder) = self.parse_binder(stop.clone())? {
                return Ok(Box::new(MainTactic::ChainBinder((tactic, binder))));
            }
            return Ok(Box::new(MainTactic::ChainTactic((
                tactic,
                self.parse_high_tactic(stop)?,
            ))));
        }
        Ok(Box::new(MainTactic::Simple(tactic)))
    }

    fn parse_binder(&mut self, stop: Stopper) -> Result<Option<Box<BinderTactic>>> {
        if let CoqTokenKind::Word(word) = &self.current()?.kind {
            match word.as_str() {
                "let" => Ok(Some(Box::new(BinderTactic::Let(self.parse_let(stop)?)))),
                "fun" => Ok(Some(Box::new(BinderTactic::Fun(self.parse_fun(stop)?)))),
                _ => Ok(None),
            }
        } else {
            Ok(None)
        }
    }

    fn parse_expression(&mut self, stop: Stopper) -> Result<Box<LtacExpression>> {
        if let Some(binder) = self.parse_binder(stop.clone())? {
            Ok(Box::new(LtacExpression::Binder(BinderExpression {
                binder,
            })))
        } else {
            Ok(Box::new(LtacExpression::Simple(MainExpression {
                tactic: self.parse_main_tactic(stop)?,
            })))
        }
    }
}

pub fn parse(query: CoqTokenSlice) -> Result<Box<LtacExpression>> {
    let mut parser = LtacParser::new(query);
    parser.parse_expression(stop!(CoqTokenKind::Dot))
}

#[cfg(test)]
mod tests {
    use crate::lexer::{tokenize, CoqTokenSlice};
    use crate::tactic::parse;

    fn check(data: &str) {
        let tokens = tokenize(data).unwrap();
        let expr = parse(CoqTokenSlice::from(tokens.as_slice())).unwrap();

        //println!("{}", expr);
        println!("{:?}", expr);
    }

    #[test]
    fn intros() {
        check("intros * [a | (_,c)] f.");
    }
}
