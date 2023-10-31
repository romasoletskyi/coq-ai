use anyhow::{bail, Result};
use std::ops::Index;
use std::str::Chars;

#[derive(Debug, Clone, PartialEq)]
pub enum CoqTokenKind {
    Dot,
    Comma,
    SemiColon,
    Colon,
    DoubleColon,
    Define,
    Dash,
    Arrow,
    Less,
    LessEq,
    BackArrow,
    Equiv,
    Greater,
    GreaterEq,
    Eq,
    Case,
    NotEq,
    BracketLeft,
    BracketRight,
    BracketSquareLeft,
    BracketSquareRight,
    BracketCurlyLeft,
    BracketCurlyRight,
    Plus,
    Star,
    And,
    Or,
    Not,
    Pipe,
    Question,
    Underscore,
    Percent,
    NewLine,
    Word(String),
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
            Self::Underscore => "_",
            Self::Percent => "%",
            Self::NewLine => "",
            Self::Word(s) => s,
        };
        write!(f, "{}", text)
    }
}

#[derive(Debug)]
enum LexerError {
    Eof,
    NoMatch,
    UnexpectedSymbol,
}

impl std::fmt::Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Eof => write!(f, "LexerError: EOF"),
            Self::NoMatch => write!(f, "LexerError: no match with predicate"),
            Self::UnexpectedSymbol => write!(f, "LexerError: unexpected symbol"),
        }
    }
}

struct CharPeeker<'a> {
    chars: Chars<'a>,
    next: Option<char>,
}

impl<'a> CharPeeker<'a> {
    fn new(mut chars: Chars<'a>) -> Self {
        let next = chars.next();
        CharPeeker { chars, next }
    }
}

impl<'a> Iterator for CharPeeker<'a> {
    type Item = (char, Option<char>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(current) = self.next {
            self.next = self.chars.next();
            Some((current, self.next))
        } else {
            None
        }
    }
}

fn take_while<F>(data: &str, mut pred: F) -> Result<(&str, usize)>
where
    F: FnMut(char, Option<char>) -> bool,
{
    let mut length: usize = 0;
    for (c, next) in CharPeeker::new(data.chars()) {
        if pred(c, next) {
            length += c.len_utf8();
        } else {
            break;
        }
    }
    if length == 0 {
        bail!(LexerError::NoMatch);
    }
    Ok((&data[..length], length))
}

fn skip_whitespace(data: &str) -> (usize, bool) {
    match take_while(data, |c, _| c.is_whitespace()) {
        Ok((space, size)) => (size, space.contains('\n')),
        _ => (0, false),
    }
}

fn skip_comments(data: &str) -> usize {
    let mut copy = data;
    let mut length = 0;
    if copy.starts_with("(*") {
        while !copy.is_empty() && !copy.starts_with("*)") {
            let chunk = if copy.starts_with("(*") && length > 0 {
                skip_comments(copy)
            } else {
                copy.chars().next().unwrap().len_utf8()
            };
            copy = &copy[chunk..];
            length += chunk;
        }
        if copy.starts_with("*)") {
            length += 2;
        }
    }
    length
}

fn get_next_char(it: &mut Chars<'_>) -> Result<char> {
    match it.next() {
        Some(c) => Ok(c),
        None => bail!(LexerError::Eof),
    }
}

fn tokenize_word(data: &str) -> Result<(CoqTokenKind, usize)> {
    let mut first = true;
    let (word, size) = take_while(data, |c, next| {
        if first {
            first = false;
            c.is_alphanumeric() || c == '_' || c == '?' || c == '@'
        } else {
            let allow_dot = c == '.'
                && if let Some(next) = next {
                    next.is_alphabetic() || next == '_'
                } else {
                    false
                };
            c.is_alphanumeric() || c == '_' || c == '\'' || allow_dot
        }
    })?;
    Ok((CoqTokenKind::Word(word.to_owned()), size))
}

fn get_next_token(data: &str) -> Result<(CoqTokenKind, usize)> {
    let mut it = data.chars();
    let next = match it.next() {
        Some(c) => c,
        None => bail!(LexerError::Eof),
    };
    let result = match next {
        ':' => match get_next_char(&mut it)? {
            '=' => (CoqTokenKind::Define, 2),
            ':' => (CoqTokenKind::DoubleColon, 2),
            _ => (CoqTokenKind::Colon, 1),
        },
        '-' => match get_next_char(&mut it)? {
            '>' => (CoqTokenKind::Arrow, 2),
            _ => (CoqTokenKind::Dash, 1),
        },
        '<' => match get_next_char(&mut it)? {
            '-' => match get_next_char(&mut it)? {
                '>' => (CoqTokenKind::Equiv, 3),
                _ => (CoqTokenKind::BackArrow, 2),
            },
            '>' => (CoqTokenKind::NotEq, 2),
            '=' => (CoqTokenKind::LessEq, 2),
            _ => (CoqTokenKind::Less, 1),
        },
        '>' => match get_next_char(&mut it)? {
            '=' => (CoqTokenKind::GreaterEq, 2),
            _ => (CoqTokenKind::Greater, 1),
        },
        '=' => match get_next_char(&mut it)? {
            '>' => (CoqTokenKind::Case, 2),
            _ => (CoqTokenKind::Eq, 1),
        },
        '/' => match get_next_char(&mut it)? {
            '\\' => (CoqTokenKind::And, 2),
            _ => bail!(LexerError::UnexpectedSymbol),
        },
        '\\' => match get_next_char(&mut it)? {
            '/' => (CoqTokenKind::Or, 2),
            _ => bail!(LexerError::UnexpectedSymbol),
        },
        '?' => {
            let c = get_next_char(&mut it)?;
            if c.is_alphanumeric() || c == '_' {
                tokenize_word(data)?
            } else {
                (CoqTokenKind::Question, 1)
            }
        }
        '_' => match get_next_char(&mut it) {
            Ok(c) => {
                if c.is_alphanumeric() || c == '_' || c == '\'' {
                    tokenize_word(data)?
                } else {
                    (CoqTokenKind::Underscore, 1)
                }
            }
            _ => (CoqTokenKind::Underscore, 1),
        },
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
        '%' => (CoqTokenKind::Percent, 1),
        _ => tokenize_word(data)?,
    };
    Ok(result)
}

#[derive(Debug, Clone, PartialEq)]
pub struct CoqToken {
    pub kind: CoqTokenKind,
    start: usize,
    end: usize,
}

impl CoqToken {
    pub fn new(kind: CoqTokenKind, start: usize, end: usize) -> Self {
        CoqToken { kind, start, end }
    }
}

impl std::fmt::Display for CoqToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {}, {})", self.kind, self.start, self.end)
    }
}

impl Default for CoqToken {
    fn default() -> Self {
        CoqToken {
            kind: CoqTokenKind::Underscore,
            start: 0,
            end: 0,
        }
    }
}

#[derive(Clone, Copy)]
pub struct CoqTokenSlice<'a>(&'a [CoqToken]);

impl<'a> CoqTokenSlice<'a> {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn cut(&mut self, index: usize) -> CoqTokenSlice<'a> {
        let part = CoqTokenSlice(&self.0[..index]);
        self.0 = &self.0[index..];
        part
    }
}

impl<'a> From<&'a [CoqToken]> for CoqTokenSlice<'a> {
    fn from(value: &'a [CoqToken]) -> Self {
        CoqTokenSlice(value)
    }
}

impl<'a> From<CoqTokenSlice<'a>> for Vec<CoqToken> {
    fn from(value: CoqTokenSlice<'a>) -> Self {
        value.0.to_vec()
    }
}

impl<'a> Index<usize> for CoqTokenSlice<'a> {
    type Output = CoqToken;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<'a> std::fmt::Display for CoqTokenSlice<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let length = self.0.len();
        for i in 0..length - 1 {
            write!(f, "{} ", self.0[i].kind)?;
        }
        write!(f, "{}", self.0[length - 1].kind)
    }
}

pub struct CoqTokenizer<'a> {
    index: usize,
    text: &'a str,
}

impl<'a> CoqTokenizer<'a> {
    fn new(data: &'a str) -> Self {
        CoqTokenizer {
            index: 0,
            text: data,
        }
    }

    fn next(&mut self) -> Result<Option<CoqToken>> {
        let (size, new_line) = self.skip();
        if new_line {
            return Ok(Some(CoqToken {
                kind: CoqTokenKind::NewLine,
                start: self.index - size,
                end: self.index,
            }));
        }
        if self.text.is_empty() {
            Ok(None)
        } else {
            let (kind, size) = get_next_token(self.text)?;
            self.chomp(size);
            Ok(Some(CoqToken {
                kind,
                start: self.index - size,
                end: self.index,
            }))
        }
    }

    fn chomp(&mut self, amount: usize) {
        self.index += amount;
        self.text = &self.text[amount..];
    }

    fn skip(&mut self) -> (usize, bool) {
        let mut remainder = self.text;
        let mut new_line = false;
        let mut size = 0;
        loop {
            let (whitespace, delimiter) = skip_whitespace(remainder);
            remainder = &remainder[whitespace..];
            if delimiter {
                new_line = true;
            }

            let comments = skip_comments(remainder);
            remainder = &remainder[comments..];

            size += whitespace + comments;
            if whitespace + comments == 0 {
                break;
            }
        }
        self.index += size;
        self.text = remainder;
        (size, new_line)
    }

    fn tokenize(&mut self) -> Result<Vec<CoqToken>> {
        let mut tokens = Vec::new();
        while let Some(token) = self.next()? {
            println!("{}", token);
            tokens.push(token);
        }
        Ok(tokens)
    }
}

pub fn tokenize(data: &str) -> Result<Vec<CoqToken>> {
    let mut tokenizer = CoqTokenizer::new(data);
    tokenizer.tokenize()
}

mod tests {
    use crate::lexer::tokenize;

    #[test]
    fn compact() {
        let tokens = tokenize(
            "Definition compact (X:TopologicalSpace) :=
        forall C:Family X,
          (forall U:Ensemble X, In C U -> open U) ->
          FamilyUnion C = Full_set ->
          exists C':Family X,
            Finite C' /\\ Included C' C /\\
            FamilyUnion C' = Full_set. ",
        );
        println!("{:?}", tokens);
    }

    #[test]
    fn comments() {
        let tokens = tokenize(
            "
        (* Every closed subset of a compact space is compact, but avoid
            mentioning the subspace topology. *)
        (* these comments (* are nested *) and can be non-trivial *)
         Lemma closed_compact_ens (X : TopologicalSpace) (S : Ensemble X) :
           compact X -> closed S ->
           forall F : Family X,
             (forall U, In F U -> open U) ->
             Included S (FamilyUnion F) ->
             exists C,
               Finite C /\\ Included C F /\\
                 Included S (FamilyUnion C).",
        );
        println!("{:?}", tokens);
    }
}
