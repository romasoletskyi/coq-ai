use anyhow::{bail, Ok, Result};

use crate::stop;
use crate::lexer::{CoqToken, CoqTokenKind, CoqTokenSlice};
use crate::parser::{Stopper, CoqParser, ParserError, Term, BasicTerm};

#[derive(Debug, PartialEq)]
struct AtomBinder {
    name: String
}

#[derive(Debug, PartialEq)]
struct TypeBinder {
    names: Vec<String>,
    typ: Box<Term>
}

#[derive(Debug, PartialEq)]
enum SimpleBinder {
    AtomBinder(AtomBinder),
    TypeBinder(TypeBinder)
}

#[derive(Debug, PartialEq)]
struct AliasDefinition {
    name: String,
    binders: Vec<SimpleBinder>,
    term: Box<Term>
}

#[derive(Debug, PartialEq)]
enum EqualityIntroPattern {
    Arrow,
    BackArrow,
    Equality(Vec<IntroPattern>)
}

#[derive(Debug, PartialEq)]
enum IntroPattern {
    Star,
    DoubleStar,
    Equality(EqualityIntroPattern),
    OrAnd(Vec<IntroPattern>),
    Named(String)
}

#[derive(Debug, PartialEq)]
struct IntrosTactic {
    token: String,
    patterns: Vec<IntroPattern>
}

#[derive(Debug, PartialEq)]
struct ClearTactic {
    inverse: bool,
    names: Vec<String>
}

#[derive(Debug, PartialEq)]
struct RememberTactic {
    token: String,
    term: Box<BasicTerm>,
    as_name: Option<String>,
    eqn: Option<String>
}

#[derive(Debug, PartialEq)]
struct AssertTactic {
    token: String,
    name: String,
    typ: Box<Term>,
    by: Option<Box<HighTactic>>
}

#[derive(Debug, PartialEq)]
struct PoseProofAssertTactic {
    name: String,
    term: Box<Term>
}

#[derive(Debug, PartialEq)]
struct PoseProofExactTactic {
    term: Box<Term>,
    as_intro: Option<IntroPattern>
}

#[derive(Debug, PartialEq)]
enum SimpleTactic {
    Intro(String),
    Intros(IntrosTactic),
    Clear(ClearTactic),
    Remember(RememberTactic),
    Assert(AssertTactic),
    Cut(Box<BasicTerm>),
    PoseProofAssert(PoseProofAssertTactic),
    PoseProofExact(PoseProofExactTactic)
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

static THEN: &str = "then";

static ELSE: &str = "else";

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

static REC: &str = "rec";

static WITH: &str = "with";

static IN: &str = "in";

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
    tactic: Box<MainTactic>
}

#[derive(Debug, PartialEq)]
pub struct BinderExpression {
    binder: Box<BinderTactic>
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
        F: FnOnce(&mut CoqParser) -> T
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
        if self.current()?.kind == CoqTokenKind::Word("as".to_string()) {
            self.advance();
            Ok(Some(self.parse_name()?))
        } else {
            Ok(None)
        }
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
        let rec = CoqTokenKind::Word(REC.to_string()) == self.current()?.kind;
        if rec {
            self.advance();
        }
        let clause = self.parse_let_clause(stop!(CoqTokenKind::Word(IN.to_string()), CoqTokenKind::Word(WITH.to_string())))?;
        let mut with = Vec::new();
        while self.current()?.kind != CoqTokenKind::Word(IN.to_string()) {
            with.push(self.parse_let_clause(stop!(CoqTokenKind::Word(IN.to_string()), CoqTokenKind::Word(WITH.to_string())))?);
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
        let if_term = self.parse_expression(stop!(CoqTokenKind::Word(THEN.to_string())))?;
        self.advance();
        let then_term = self.parse_expression(stop!(CoqTokenKind::Word(ELSE.to_string())))?;
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

    fn parse_match_pattern(
        &mut self,
        stop: Stopper,
    ) -> Result<MatchPattern> {
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
            let term = self.parse_match_term(match_stop.add(CoqTokenKind::Colon))?;
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

    fn parse_match_hypothesis(
        &mut self,
        stop: Stopper,
    ) -> Result<MatchHypothesis> {
        Ok(MatchHypothesis {
            name: self.parse_name()?,
            pattern: self.parse_match_pattern(stop)?,
        })
    }

    fn parse_match_goal(&mut self, key: MatchKey) -> Result<MatchGoal> {
        self.advance();
        let reverse = if self.current()?.kind == CoqTokenKind::Word("reverse".to_string()) {
            self.advance();
            true
        } else {
            false
        };
        self.advance();
        self.advance();

        let mut cases = Vec::new();
        while self.current()?.kind != CoqTokenKind::Word("end".to_string()) {
            if self.current()?.kind == CoqTokenKind::Pipe {
                self.advance();
            }
            let pattern = if self.current()?.kind == CoqTokenKind::Underscore {
                None
            } else {
                if self.current()?.kind == CoqTokenKind::BracketSquareLeft {
                    self.advance();
                }

                let mut hyp = Vec::new();
                while self.current()?.kind != CoqTokenKind::Pipe {
                    hyp.push(self.parse_match_hypothesis(stop!(CoqTokenKind::Comma, CoqTokenKind::Pipe))?);
                    if self.current()?.kind == CoqTokenKind::Comma {
                        self.advance();
                    }
                }

                self.advance();
                self.advance();
                let goal = self.parse_match_term(stop!(CoqTokenKind::Case, CoqTokenKind::BracketSquareRight))?;
                Some(MatchGoalPattern { hyp, goal })
            };
            cases.push(MatchCase {
                pattern,
                expr: self.parse_expression(stop!(CoqTokenKind::Word("end".to_string()), CoqTokenKind::Pipe))?
            });
        }

        Ok(MatchGoal {
            key,
            reverse,
            cases,
        })
    }

    fn collect_intro_patterns(&mut self, skip: fn(&CoqTokenKind) -> bool, stop: fn(&CoqTokenKind) -> bool) -> Result<Vec<IntroPattern>> {
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
                    Ok(IntroPattern::Equality(EqualityIntroPattern::Equality(patterns)))
                } else {
                    let patterns = self.collect_intro_patterns(|token: &_| token == &CoqTokenKind::Pipe, stop)?;
                    self.advance();
                    Ok(IntroPattern::OrAnd(patterns))
                }
            }
            CoqTokenKind::BracketLeft => {
                self.advance();
                let patterns = self.collect_intro_patterns(|token| token == &CoqTokenKind::Comma || token == &CoqTokenKind::Ampersand, |token| token == &CoqTokenKind::BracketRight)?;
                self.advance();
                Ok(IntroPattern::OrAnd(patterns))
            }
            CoqTokenKind::Arrow => Ok(IntroPattern::Equality(EqualityIntroPattern::Arrow)),
            CoqTokenKind::BackArrow => Ok(IntroPattern::Equality(EqualityIntroPattern::BackArrow)),
            _ => {
                Ok(IntroPattern::Named(self.parse_name()?))
            }
        }
    }

    fn parse_as_intro_pattern(&mut self) -> Result<Option<IntroPattern>> {
        if self.current()?.kind == CoqTokenKind::Word("as".to_string()) {
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
            Ok(SimpleBinder::AtomBinder(AtomBinder { name: self.parse_name()? }))
        }
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
        Ok(AliasDefinition { name, binders, term })
    }

    fn parse_simple_tactic(&mut self, stop: Stopper) -> Result<Option<Box<SimpleTactic>>> {
        if let CoqTokenKind::Word(word) = &self.current()?.kind {
            match word.as_str() {
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
                    Ok(Some(Box::new(SimpleTactic::Intros(IntrosTactic { token, patterns} ))))                    
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
                    Ok(Some(Box::new(SimpleTactic::Clear(ClearTactic {inverse, names }))))
                }
                "remember" | "eremember" => {
                    let token = word.clone();
                    self.advance();
                    let term = self.parse_coq_basic_term()?;
                    let as_name = self.parse_as_name()?;                    
                    let eqn = if self.current()?.kind == CoqTokenKind::Word("eqn".to_string()) {
                        self.advance();
                        self.advance();
                        Some(self.parse_name()?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Remember(RememberTactic {token, term, as_name, eqn }))))
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
                    let by = if self.current()?.kind == CoqTokenKind::Word("by".to_string()) {
                        self.advance();
                        Some(self.parse_high_tactic(stop)?)
                    } else {
                        None
                    };
                    Ok(Some(Box::new(SimpleTactic::Assert(AssertTactic { token, name, typ, by }))))
                }
                "cut" => {
                    self.advance();
                    let typ = self.parse_coq_basic_term()?;
                    Ok(Some(Box::new(SimpleTactic::Cut(typ))))
                }
                "pose" | "epose" => {
                    let token = word.clone();
                    self.advance();
                    if self.current()?.kind == CoqTokenKind::Word("proof".to_string()) {
                        self.advance();
                        let tactic = if self.current()?.kind == CoqTokenKind::BracketLeft {
                            self.advance();
                            let name = self.parse_name()?;
                            self.advance();
                            let term = self.parse_coq_term(stop!(CoqTokenKind::BracketRight))?;
                            SimpleTactic::PoseProofAssert(PoseProofAssertTactic { name, term })                            
                        } else {
                            let term_stop = stop.clone();
                            let term = self.parse_coq_term(term_stop.add(CoqTokenKind::Word("as".to_string())))?;
                            let as_intro = self.parse_as_intro_pattern()?;
                            SimpleTactic::PoseProofExact(PoseProofExactTactic { term, as_intro })
                        };
                        Ok(Some(Box::new(tactic)))
                    } else {
                        bail!(ParserError::UnexpectedToken(self.current()?.clone()))
                    }
                }
                _ => Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    fn parse_low_tactic(
        &mut self,
        stop: Stopper,
    ) -> Result<Box<LowTactic>> {
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

    fn parse_middle_tactic(
        &mut self,
        stop: Stopper,
    ) -> Result<Box<MiddleTactic>> {
        if self.current()?.kind == CoqTokenKind::Word("tryif".to_string()) {
            return Ok(Box::new(MiddleTactic::TryIf(self.parse_tryif(stop)?)));
        }
        let tactic_stop = stop.clone();
        let tactic = self.parse_low_tactic(tactic_stop.add(CoqTokenKind::Pipe).add(CoqTokenKind::Plus))?;
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

    fn parse_high_tactic(
        &mut self,
        stop: Stopper,
    ) -> Result<Box<HighTactic>> {
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
                tactics.push(self.parse_expression(stop!(CoqTokenKind::BracketSquareRight, CoqTokenKind::Pipe))?);
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
        let tactic = self.parse_high_tactic(high_stop.add(CoqTokenKind::SemiColon))?;
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
            Ok(Box::new(LtacExpression::Binder(BinderExpression { binder })))
        } else {
            Ok(Box::new(LtacExpression::Simple(
                MainExpression { tactic: self.parse_main_tactic(stop)? },
            )))
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