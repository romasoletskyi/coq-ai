use anyhow::{Result, bail};
use std::str::Chars;

#[derive(Debug)]
enum TokenKind {
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

impl std::fmt::Display for TokenKind {
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

fn tokenize_word(data: &str) -> Result<(TokenKind, usize)> {
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
    Ok((TokenKind::Word(word.to_owned()), size))
}

fn get_next_token(data: &str) -> Result<(TokenKind, usize)> {
    let mut it = data.chars();
    let next = match it.next() {
        Some(c) => c,
        None => bail!(TokenError::EOF)
    };
    let result = match next {
        ':' => 
            match get_next_char(&mut it)? {
                '=' => (TokenKind::Define, 2),
                ':' => (TokenKind::DoubleColon, 2),
                _ => (TokenKind::Colon, 1)
            }
        '-' => 
            match get_next_char(&mut it)? {
                '>' => (TokenKind::Arrow, 2),
                _ => (TokenKind::Dash, 1)
            }
        '<' => 
            match get_next_char(&mut it)? {
                '-' => 
                    match get_next_char(&mut it)? {
                        '>' => (TokenKind::Equiv, 3),
                        _ => (TokenKind::BackArrow, 2)
                    }
                '>' => (TokenKind::NotEq, 2),
                '=' => (TokenKind::LessEq, 2),
                _ => (TokenKind::Less, 1)
            }
        '>' => 
            match get_next_char(&mut it)? {
                '=' => (TokenKind::GreaterEq, 2),
                _ => (TokenKind::Greater, 1)
            }
        '=' => 
            match get_next_char(&mut it)? {
                '>' => (TokenKind::Case, 2),
                _ => (TokenKind::Eq, 1)
            }
        '/' => 
            match get_next_char(&mut it)? {
                '\\' => (TokenKind::And, 2),
                _ => bail!(TokenError::UnexpectedSymbol)
            }
        '\\' => 
            match get_next_char(&mut it)? {
                '/' => (TokenKind::Or, 2),
                _ => bail!(TokenError::UnexpectedSymbol)
            }
        '?' =>             
            if get_next_char(&mut it)?.is_whitespace() {
                (TokenKind::Question, 1)
            } else {
                tokenize_word(data)?
            }
        '.' => (TokenKind::Dot, 1),
        ',' => (TokenKind::Comma, 1),
        ';' => (TokenKind::SemiColon, 1),
        '(' => (TokenKind::BracketLeft, 1),
        ')' => (TokenKind::BracketRight, 1),
        '[' => (TokenKind::BracketSquareLeft, 1),
        ']' => (TokenKind::BracketSquareRight, 1),
        '{' => (TokenKind::BracketCurlyLeft, 1),
        '}' => (TokenKind::BracketCurlyRight, 1),
        '+' => (TokenKind::Plus, 1),
        '*' => (TokenKind::Star, 1),
        '~' => (TokenKind::Not, 1),
        '|' => (TokenKind::Pipe, 1),
        _ => tokenize_word(data)?
    };
    Ok(result)
}

#[derive(Debug)]
pub struct Token {
    kind: TokenKind,
    start: usize,
    end: usize 
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {}, {})", self.kind, self.start, self.end)
    }
}

pub struct Tokenizer<'a> {
    index: usize,
    text: &'a str
}

impl<'a> Tokenizer<'a> {
    pub fn new(data: &'a str) -> Self {
        Tokenizer { index: 0, text: data}
    }

    pub fn next(&mut self) -> Result<Option<Token>> {
        self.skip();
        if self.text.is_empty() {
            Ok(None)
        } else {
            let (kind, size) = get_next_token(self.text)?;
            self.chomp(size);
            Ok(Some(Token{kind, start: self.index - size, end: self.index}))
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