use anyhow::{bail, Result};
use std::{fmt::Display, str::Chars, sync::Arc};

#[derive(Debug, Clone, Copy, PartialEq)]
enum TokenKind {
    Symbol(char),
    Arrow,
    LeftBracket,
    RightBracket,
}

pub struct Token {
    kind: TokenKind,
    start: usize,
    end: usize,
}

struct Lexer<'a> {
    data: &'a str,
    index: usize,
}

#[derive(Debug)]
enum LexerError {
    Eof,
    UnexpectedSymbol(char),
}

impl Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexerError::Eof => write!(f, "EOF"),
            LexerError::UnexpectedSymbol(c) => write!(f, "Unexpected symbol {}", c),
        }
    }
}

fn get_next_char(it: &mut Chars<'_>) -> Result<char> {
    match it.next() {
        Some(c) => Ok(c),
        None => bail!(LexerError::Eof),
    }
}

fn get_next_token(data: &str) -> Result<(TokenKind, usize)> {
    let mut it = data.chars();
    match get_next_char(&mut it)? {
        '-' => {
            let c = get_next_char(&mut it)?;
            if c == '>' {
                Ok((TokenKind::Arrow, 2))
            } else {
                bail!(LexerError::UnexpectedSymbol(c));
            }
        }
        '(' => Ok((TokenKind::LeftBracket, 1)),
        ')' => Ok((TokenKind::RightBracket, 1)),
        c => Ok((TokenKind::Symbol(c), 1)),
    }
}

impl<'a> Lexer<'a> {
    fn new(data: &'a str) -> Self {
        Lexer { data, index: 0 }
    }

    fn chomp(&mut self, size: usize) {
        self.index += size;
        self.data = &self.data[size..];
    }

    fn skip_whitespace(&mut self) {
        let mut size: usize = 0;
        for c in self.data.chars() {
            if c.is_whitespace() {
                size += c.len_utf8();
            } else {
                break;
            }
        }
        self.chomp(size);
    }

    fn next(&mut self) -> Result<Option<Token>> {
        self.skip_whitespace();
        if self.data.is_empty() {
            Ok(None)
        } else {
            let (kind, size) = get_next_token(self.data)?;
            self.chomp(size);
            Ok(Some(Token {
                kind,
                start: self.index - size,
                end: self.index,
            }))
        }
    }
}

pub fn tokenize(data: &str) -> Result<Vec<Token>> {
    let mut lexer = Lexer::new(data);
    let mut tokens = Vec::new();
    while let Some(token) = lexer.next()? {
        tokens.push(token);
    }
    Ok(tokens)
}

/*
    Grammar rules are
    expr = basic | basic -> expr
    basic = char | ( expr )
*/

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Implication {
    pub left: Arc<Expression>,
    pub right: Arc<Expression>,
}

impl Display for Implication {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &*self.left {
            Expression::Basic(c) => write!(f, "{}", c),
            Expression::Implication(implication) => write!(f, "({})", implication),
        }?;
        write!(f, " -> {}", self.right)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Expression {
    Implication(Implication),
    Basic(char),
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Implication(implication) => write!(f, "{}", implication),
            Expression::Basic(c) => write!(f, "{}", c),
        }
    }
}

impl From<Box<UniqueExpression>> for Arc<Expression> {
    fn from(value: Box<UniqueExpression>) -> Self {
        Arc::new(match *value {
            UniqueExpression::Basic(char) => Expression::Basic(char),
            UniqueExpression::Implication(imp) => Expression::Implication(Implication {
                left: imp.left.into(),
                right: imp.right.into(),
            }),
        })
    }
}

pub struct UniqueImplication {
    left: Box<UniqueExpression>,
    right: Box<UniqueExpression>,
}

pub enum UniqueExpression {
    Implication(UniqueImplication),
    Basic(char),
}

impl From<Arc<Expression>> for Box<UniqueExpression> {
    fn from(value: Arc<Expression>) -> Self {
        Box::new(match &*value {
            Expression::Basic(char) => UniqueExpression::Basic(*char),
            Expression::Implication(imp) => UniqueExpression::Implication(UniqueImplication {
                left: imp.left.clone().into(),
                right: imp.right.clone().into(),
            }),
        })
    }
}

struct Parser<'a> {
    tokens: &'a [Token],
    index: usize,
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token]) -> Self {
        Parser { tokens, index: 0 }
    }

    fn current(&self) -> Result<TokenKind> {
        if self.index < self.tokens.len() {
            Ok(self.tokens[self.index].kind)
        } else {
            bail!(LexerError::Eof)
        }
    }

    fn advance(&mut self) {
        self.index += 1;
    }

    fn parse_basic(&mut self) -> Result<Arc<Expression>> {
        match self.current()? {
            TokenKind::LeftBracket => {
                self.advance();
                let expr = self.parse()?;
                self.advance();
                Ok(expr)
            }
            TokenKind::Symbol(c) => {
                self.advance();
                Ok(Arc::new(Expression::Basic(c)))
            }
            TokenKind::RightBracket => bail!(LexerError::UnexpectedSymbol(')')),
            TokenKind::Arrow => bail!(LexerError::UnexpectedSymbol('-')),
        }
    }

    fn parse(&mut self) -> Result<Arc<Expression>> {
        let left = self.parse_basic()?;
        if let Ok(TokenKind::Arrow) = self.current() {
            self.advance();
            Ok(Arc::new(Expression::Implication(Implication {
                left,
                right: self.parse()?,
            })))
        } else {
            Ok(left)
        }
    }
}

pub fn parse(tokens: &[Token]) -> Result<Arc<Expression>> {
    Parser::new(tokens).parse()
}

#[cfg(test)]
mod tests {
    use super::{parse, tokenize};

    fn check(data: &str) {
        let tokens = tokenize(data).unwrap();
        let expr = parse(tokens.as_slice()).unwrap();
        println!("{:?}", expr);
        println!("{}", expr);
    }

    #[test]
    fn simple() {
        check("P -> Q");
    }

    #[test]
    fn complex() {
        check(
            "(P -> Q) -> (P -> R) -> (T -> R) ->
            (S -> T ->  U) -> ((P -> Q) -> (P -> S)) ->
            T -> P",
        );
    }
}
