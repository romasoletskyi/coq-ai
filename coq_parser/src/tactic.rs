use anyhow::{bail, Ok, Result};

use crate::lexer::{CoqToken, CoqTokenKind, CoqTokenSlice};
use crate::parser::{CoqParser, ParserError, Term};

pub(crate) trait FnClone: Fn(&CoqTokenKind) -> bool + CloneBox {}

impl<T> FnClone for T 
where 
    T: 'static + Fn(&CoqTokenKind) -> bool + Clone
{

}

pub(crate) trait CloneBox {
    fn clone_box(&self) -> Box<dyn FnClone>;
}

impl Clone for Box<dyn FnClone> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

impl<T> CloneBox for T
where 
    T: 'static + Fn(&CoqTokenKind) -> bool + Clone
{
    fn clone_box(&self) -> Box<dyn FnClone> {
        Box::new(self.clone())
    }
}

enum SimpleTactic {}

enum MatchKey {
    Match,
    LazyMatch,
    MultiMatch,
}

struct MatchTerm(Box<Term>);

enum MatchPattern {
    Type(MatchTerm),
    Binder(MatchTerm),
    TypedBinder((MatchTerm, MatchTerm)),
    Bracket((MatchTerm, MatchTerm)),
}

struct MatchHypothesis {
    name: String,
    pattern: MatchPattern,
}

struct MatchGoalPattern {
    hyp: Vec<MatchHypothesis>,
    goal: MatchTerm,
}

struct MatchCase {
    pattern: Option<MatchGoalPattern>,
    expr: Box<LtacExpression>,
}

struct MatchGoal {
    key: MatchKey,
    reverse: bool,
    cases: Vec<MatchCase>,
}

enum LowTactic {
    MatchGoal(MatchGoal),
    Term(Box<Term>),
    ForEach(Box<ForEachGoal>),
    Bracket(Box<LtacExpression>),
    SimpleTactic(Box<SimpleTactic>),
}

static THEN: &str = "then";

static ELSE: &str = "else";

struct TryIf {
    if_term: Box<LtacExpression>,
    then_term: Box<LtacExpression>,
    else_term: Box<LtacExpression>,
}

enum MiddleTactic {
    Branch((Box<LowTactic>, Box<MiddleTactic>)),
    BranchBinder((Box<LowTactic>, Box<BinderTactic>)),
    First((Box<LowTactic>, Box<MiddleTactic>)),
    FirstBinder((Box<LowTactic>, Box<BinderTactic>)),
    TryIf(TryIf),
    Simple(Box<LowTactic>),
}

struct Do {
    num: usize,
    term: Box<HighTactic>,
}

enum HighTactic {
    Try(Box<HighTactic>),
    Do(Do),
    Repeat(Box<HighTactic>),
    Simple(Box<MiddleTactic>),
}

struct ForEachGoal {
    tactics: Vec<Box<LtacExpression>>,
}

enum MainTactic {
    Simple(Box<HighTactic>),
    ForEach((Box<HighTactic>, Box<ForEachGoal>)),
    ChainTactic((Box<HighTactic>, Box<HighTactic>)),
    ChainBinder((Box<HighTactic>, Box<BinderTactic>)),
}

struct Fun {
    names: Vec<String>,
    value: Box<LtacExpression>,
}

struct SimpleClause {
    name: String,
    expr: Box<LtacExpression>,
}

struct LetClause {
    ident: String,
    names: Vec<String>,
    expr: Box<LtacExpression>,
}

static REC: &str = "rec";

static WITH: &str = "with";

static IN: &str = "in";

struct Let {
    rec: bool,
    clause: LetClause,
    with: Vec<LetClause>,
    expr: Box<LtacExpression>,
}

enum BinderTactic {
    Fun(Fun),
    Let(Let),
}

enum LtacExpression {
    Simple(Box<MainTactic>),
    Binder(Box<BinderTactic>),
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

    fn parse_coq_term(&self, stop: Box<dyn FnClone>) -> Result<Box<Term>> {
        let mut slice = self.slice;
        slice.cut(self.index);
        CoqParser::new(slice, false).parse_term(stop)
    }

    fn parse_name(&mut self) -> Result<String> {
        let token = self.current()?.clone();
        match token.kind {
            CoqTokenKind::Word(name) => Ok(name),
            CoqTokenKind::Underscore => Ok("_".to_string()),
            _ => bail!(ParserError::UnexpectedToken(token.clone())),
        }
    }

    fn parse_let_clause(&mut self, stop: Box<dyn FnClone>) -> Result<LetClause> {
        let ident = self.parse_name()?;
        self.advance();

        let mut names = Vec::new();
        while self.current()?.kind != CoqTokenKind::Define {
            names.push(self.parse_name()?);
            self.advance();
        }

        self.advance();
        Ok(LetClause {
            ident,
            names,
            expr: self.parse_expression(stop)?,
        })
    }

    fn parse_let(&mut self, stop: Box<dyn FnClone>) -> Result<Let> {
        self.advance();
        let rec = CoqTokenKind::Word(REC.to_string()) == self.current()?.kind;
        if rec {
            self.advance();
        }

        let until = |token: &_| {
            token == &CoqTokenKind::Word(IN.to_string())
                || token == &CoqTokenKind::Word(WITH.to_string())
        };
        let clause = self.parse_let_clause(Box::new(until))?;

        let mut with = Vec::new();
        while self.current()?.kind != CoqTokenKind::Word(IN.to_string()) {
            with.push(self.parse_let_clause(Box::new(until))?);
        }

        Ok(Let {
            rec,
            clause,
            with,
            expr: self.parse_expression(stop)?,
        })
    }

    fn parse_fun(&mut self, stop: Box<dyn FnClone>) -> Result<Fun> {
        self.advance();

        let mut names = Vec::new();
        while self.current()?.kind != CoqTokenKind::Case {
            names.push(self.parse_name()?);
            self.advance();
        }

        self.advance();
        Ok(Fun {
            names,
            value: self.parse_expression(stop)?,
        })
    }

    fn parse_tryif(&mut self, stop: Box<dyn FnClone>) -> Result<TryIf> {
        self.advance();
        let if_term = self.parse_expression(Box::new(|token| {
            token == &CoqTokenKind::Word(THEN.to_string())
        }))?;
        self.advance();
        let then_term = self.parse_expression(Box::new(|token| {
            token == &CoqTokenKind::Word(ELSE.to_string())
        }))?;
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

    fn parse_match_term(&mut self, stop: Box<dyn FnClone>) -> Result<MatchTerm> {
        Ok(MatchTerm(self.parse_coq_term(stop)?))
    }

    fn parse_match_pattern(
        &mut self,
        stop: Box<dyn FnClone>,
    ) -> Result<MatchPattern> {
        if self.current()?.kind == CoqTokenKind::Colon {
            self.advance();
            return Ok(MatchPattern::Type(self.parse_match_term(stop)?));
        }
        if self.current()?.kind == CoqTokenKind::Case {
            self.advance();
            if self.current()?.kind == CoqTokenKind::BracketSquareLeft {
                self.advance();
                let binder = self.parse_match_term(Box::new(|token| {
                    token == &CoqTokenKind::BracketSquareRight
                }))?;
                self.advance();
                self.advance();
                return Ok(MatchPattern::Bracket((
                    binder,
                    self.parse_match_term(stop)?,
                )));
            }
            let term = self.parse_match_term(Box::new({
                let stop = stop.clone(); 
                move |token| stop(token) || token == &CoqTokenKind::Colon
            }))?;
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
        stop: Box<dyn FnClone>,
    ) -> Result<MatchHypothesis> {
        let name = self.parse_name()?;
        self.advance();
        Ok(MatchHypothesis {
            name,
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
                    hyp.push(self.parse_match_hypothesis(Box::new(|token| {
                        token == &CoqTokenKind::Comma || token == &CoqTokenKind::Pipe
                    }))?);
                    if self.current()?.kind == CoqTokenKind::Comma {
                        self.advance();
                    }
                }

                self.advance();
                self.advance();
                let goal = self.parse_match_term(Box::new(|token| {
                    token == &CoqTokenKind::Case || token == &CoqTokenKind::BracketSquareRight
                }))?;
                Some(MatchGoalPattern { hyp, goal })
            };
            cases.push(MatchCase {
                pattern,
                expr: self.parse_expression(Box::new(|token| {
                    token == &CoqTokenKind::Word("end".to_string()) || token == &CoqTokenKind::Pipe
                }))?,
            });
        }

        Ok(MatchGoal {
            key,
            reverse,
            cases,
        })
    }

    fn parse_simple_tactic(&mut self) -> Result<Option<Box<SimpleTactic>>> {
        
    }

    fn parse_low_tactic(
        &mut self,
        stop: Box<dyn FnClone>,
    ) -> Result<Box<LowTactic>> {
        if self.current()?.kind == CoqTokenKind::BracketLeft {
            let expr =
                self.parse_expression(Box::new(|token| token == &CoqTokenKind::BracketRight))?;
            self.advance();
            return Ok(Box::new(LowTactic::Bracket(expr)));
        }
        if self.current()?.kind == CoqTokenKind::BracketSquareLeft {
            return Ok(Box::new(LowTactic::ForEach(self.parse_for_each_goal()?)));
        }
        if let Some(key) = self.parse_match_key()? {
            return Ok(Box::new(LowTactic::MatchGoal(self.parse_match_goal(key)?)));
        }
        if let Some(tactic) = self.parse_simple_tactic()? {
            return Ok(Box::new(LowTactic::SimpleTactic(tactic)));
        }
        Ok(Box::new(LowTactic::Term(self.parse_coq_term(stop)?)))
    }

    fn parse_middle_tactic(
        &mut self,
        stop: Box<dyn FnClone>,
    ) -> Result<Box<MiddleTactic>> {
        if self.current()?.kind == CoqTokenKind::Word("tryif".to_string()) {
            return Ok(Box::new(MiddleTactic::TryIf(self.parse_tryif(stop)?)));
        }
        let tactic = self.parse_low_tactic(Box::new({
            let stop = stop.clone();
            move |token|
            stop(token) || token == &CoqTokenKind::Pipe || token == &CoqTokenKind::Plus
        }))?;
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
        Ok(Box::new(MiddleTactic::Simple(self.parse_low_tactic(stop)?)))
    }

    fn parse_high_tactic(
        &mut self,
        stop: Box<dyn FnClone>,
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
                        self.advance();
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
        let stop = Box::new(|token: &_| {
            token == &CoqTokenKind::BracketSquareRight || token == &CoqTokenKind::Pipe
        });
        let mut tactics = Vec::new();
        while self.current()?.kind != CoqTokenKind::BracketSquareRight {
            if self.current()?.kind == CoqTokenKind::Dot {
                self.advance();
                self.advance();
            } else {
                tactics.push(self.parse_expression(stop.clone())?);
            }
            if self.current()?.kind == CoqTokenKind::Pipe {
                self.advance();
            }
        }
        self.advance();
        Ok(Box::new(ForEachGoal { tactics }))
    }

    fn parse_main_tactic(
        &mut self,
        stop: Box<dyn FnClone>,
    ) -> Result<Box<MainTactic>> {
        let tactic = self.parse_high_tactic(Box::new({
            let stop = stop.clone();
            move |token|
            stop(token) || token == &CoqTokenKind::SemiColon
        }))?;
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

    fn parse_binder(
        &mut self,
        stop: Box<dyn FnClone>,
    ) -> Result<Option<Box<BinderTactic>>> {
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

    fn parse_expression(
        &mut self,
        stop: Box<dyn FnClone>,
    ) -> Result<Box<LtacExpression>> {
        if let Some(binder) = self.parse_binder(stop.clone())? {
            Ok(Box::new(LtacExpression::Binder(binder)))
        } else {
            Ok(Box::new(LtacExpression::Simple(
                self.parse_main_tactic(stop)?,
            )))
        }
    }
}
