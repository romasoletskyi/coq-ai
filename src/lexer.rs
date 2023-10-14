use anyhow::{Result, bail};
use std::str::Chars;
use std::ops::Index;

#[derive(Debug, PartialEq)]
pub enum CoqTokenKind {
    Dot, Comma, SemiColon, 
    Colon, DoubleColon, Define, 
    Dash, Arrow,
    Less, LessEq, BackArrow, Equiv,
    Greater, GreaterEq,
    Eq, Case, NotEq,
    BracketLeft, BracketRight, 
    BracketSquareLeft, BracketSquareRight,
    BracketCurlyLeft, BracketCurlyRight,
    Plus, Star,
    And, Or, Not,
    Pipe, Question,
    Word(String)
}

impl std::fmt::Display for CoqTokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text = match self {
            Self::Dot => ".",
            Self::Comma => ",",
            Self::SemiColon => ";",
            Self::Colon => ":",
            Self::DoubleColon => "::",
            Self::Define => ":=",
            Self::Dash => "-",
            Self::Arrow => "->",
            Self::Less => "<",
            Self::LessEq => "<=",
            Self::BackArrow => "<-",
            Self::Equiv => "<->",
            Self::Greater => ">",
            Self::GreaterEq => ">=",
            Self::Eq => "=",
            Self::Case => "=>",
            Self::NotEq => "<>",
            Self::BracketLeft => "(",
            Self::BracketRight => ")",
            Self::BracketSquareLeft => "[",
            Self::BracketSquareRight => "]",
            Self::BracketCurlyLeft => "{",
            Self::BracketCurlyRight => "}",
            Self::Plus => "+",
            Self::Star => "*",
            Self::And => "/\\",
            Self::Or => "\\/",
            Self::Not => "~",
            Self::Pipe => "|",
            Self::Question => "?",
            Self::Word(s) => &s
        };
        write!(f, "{}", text)
    }
}

#[derive(Debug)]
enum TokenError {
    EOF,
    NoMatch,
    UnexpectedSymbol
}

impl std::fmt::Display for TokenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EOF => write!(f, "unexpected EOF"),
            Self::NoMatch => write!(f, "no match with predicate"),
            Self::UnexpectedSymbol => write!(f, "unexpected symbol")
        }
    }
}

fn take_while<F>(data: &str, mut pred: F) -> Result<(&str, usize)>
where F: FnMut(char) -> bool 
{
    let mut length: usize = 0;
    for c in data.chars() {
        if pred(c) {
            length += c.len_utf8();
        } else {
            break;
        }
    }
    if length == 0 {
        bail!(TokenError::NoMatch);
    } 
    Ok((&data[..length], length))
}

fn skip_whitespace(data: &str) -> usize {
    match take_while(data, |c| c.is_whitespace()) {
        Ok((_, size)) => size,
        _ => 0
    }
}

fn skip_comments(data: &str) -> usize {
    let mut copy = data;
    let mut length = 0;
    if copy.starts_with("(*") {
        while !copy.is_empty() && !copy.starts_with("*)") {
            let chunk = copy.chars().next().unwrap().len_utf8();
            copy = &copy[chunk..];
            length += chunk;
        }
    }
    length
}

fn get_next_char(it: &mut Chars<'_>) -> Result<char> {
    match it.next() {
        Some(c) => Ok(c),
        None => bail!(TokenError::EOF)
    }
}

fn tokenize_word(data: &str) -> Result<(CoqTokenKind, usize)> {
    let mut first = true;
    let (word, size) = take_while(data, |c| {
        let start = if first {
            first = false;
            c == '?' || c == '@'
        } else {
            false
        };
        c.is_alphanumeric() || c == '_' || c == '\''  || start
    })?;
    Ok((CoqTokenKind::Word(word.to_owned()), size))
}

fn get_next_token(data: &str) -> Result<(CoqTokenKind, usize)> {
    let mut it = data.chars();
    let next = match it.next() {
        Some(c) => c,
        None => bail!(TokenError::EOF)
    };
    let result = match next {
        ':' => 
            match get_next_char(&mut it)? {
                '=' => (CoqTokenKind::Define, 2),
                ':' => (CoqTokenKind::DoubleColon, 2),
                _ => (CoqTokenKind::Colon, 1)
            }
        '-' => 
            match get_next_char(&mut it)? {
                '>' => (CoqTokenKind::Arrow, 2),
                _ => (CoqTokenKind::Dash, 1)
            }
        '<' => 
            match get_next_char(&mut it)? {
                '-' => 
                    match get_next_char(&mut it)? {
                        '>' => (CoqTokenKind::Equiv, 3),
                        _ => (CoqTokenKind::BackArrow, 2)
                    }
                '>' => (CoqTokenKind::NotEq, 2),
                '=' => (CoqTokenKind::LessEq, 2),
                _ => (CoqTokenKind::Less, 1)
            }
        '>' => 
            match get_next_char(&mut it)? {
                '=' => (CoqTokenKind::GreaterEq, 2),
                _ => (CoqTokenKind::Greater, 1)
            }
        '=' => 
            match get_next_char(&mut it)? {
                '>' => (CoqTokenKind::Case, 2),
                _ => (CoqTokenKind::Eq, 1)
            }
        '/' => 
            match get_next_char(&mut it)? {
                '\\' => (CoqTokenKind::And, 2),
                _ => bail!(TokenError::UnexpectedSymbol)
            }
        '\\' => 
            match get_next_char(&mut it)? {
                '/' => (CoqTokenKind::Or, 2),
                _ => bail!(TokenError::UnexpectedSymbol)
            }
        '?' =>             
            if get_next_char(&mut it)?.is_whitespace() {
                (CoqTokenKind::Question, 1)
            } else {
                tokenize_word(data)?
            }
        '.' => (CoqTokenKind::Dot, 1),
        ',' => (CoqTokenKind::Comma, 1),
        ';' => (CoqTokenKind::SemiColon, 1),
        '(' => (CoqTokenKind::BracketLeft, 1),
        ')' => (CoqTokenKind::BracketRight, 1),
        '[' => (CoqTokenKind::BracketSquareLeft, 1),
        ']' => (CoqTokenKind::BracketSquareRight, 1),
        '{' => (CoqTokenKind::BracketCurlyLeft, 1),
        '}' => (CoqTokenKind::BracketCurlyRight, 1),
        '+' => (CoqTokenKind::Plus, 1),
        '*' => (CoqTokenKind::Star, 1),
        '~' => (CoqTokenKind::Not, 1),
        '|' => (CoqTokenKind::Pipe, 1),
        _ => tokenize_word(data)?
    };
    Ok(result)
}

#[derive(Debug)]
pub struct CoqToken {
    pub kind: CoqTokenKind,
    start: usize,
    end: usize 
}

impl std::fmt::Display for CoqToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {}, {})", self.kind, self.start, self.end)
    }
}

pub struct CoqTokenSlice<'a>(&'a [CoqToken]);

impl<'a> CoqTokenSlice<'a> {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn cut (&mut self, index: usize) -> CoqTokenSlice<'a> {
        let part = CoqTokenSlice(&self.0[..index]);
        self.0 = &self.0[index..];
        part
    }
}

impl<'a> Index<usize> for CoqTokenSlice<'a> {
    type Output = CoqToken;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<'a> From<&'a [CoqToken]> for CoqTokenSlice<'a> {
    fn from(value: &'a [CoqToken]) -> Self {
        CoqTokenSlice(value)
    }
}

impl<'a> std::fmt::Display for CoqTokenSlice<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let length = self.0.len();
        for i in 0..length - 1{
            write!(f, "{} ", self.0[i].kind)?;
        }
        write!(f, "{}", self.0[length - 1].kind)
    }
}

pub struct CoqTokenizer<'a> {
    index: usize,
    text: &'a str
}

impl<'a> CoqTokenizer<'a> {
    pub fn new(data: &'a str) -> Self {
        CoqTokenizer { index: 0, text: data}
    }

    pub fn next(&mut self) -> Result<Option<CoqToken>> {
        self.skip();
        if self.text.is_empty() {
            Ok(None)
        } else {
            let (kind, size) = get_next_token(self.text)?;
            self.chomp(size);
            Ok(Some(CoqToken{kind, start: self.index - size, end: self.index}))
        }
    }

    fn chomp(&mut self, amount: usize) {
        self.index += amount;
        self.text = &self.text[amount..];
    }

    fn skip(&mut self) {
        let mut remainder = self.text;
        loop {
            let whitespace = skip_whitespace(remainder);
            remainder = &remainder[whitespace..];

            let comments = skip_comments(remainder);
            remainder = &remainder[comments..];

            if whitespace + comments == 0 {
                break;
            }
        }
        self.text = remainder;
    }
}