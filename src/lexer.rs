//! Significant indentation overview:
//! There are three tokens we can emit when we see a line break: INDENT, DEDENT, and NEWLINE.
//! If the next non-empty line is indented more than the previous, we emit an INDENT token (and no NEWLINE).
//! If it's the same indentation, we emit one NEWLINE token. We don't emit NEWLINEs for blank lines, but we do for semicolons.
//!   (so a semicolon is like a line break + the same indentation as the current line.)
//! If it's a lower indentation level, we emit the appropriate number of DEDENTs and then a NEWLINE.

use crate::common::*;
use std::collections::VecDeque;
use std::fmt;
use std::iter::Peekable;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    DefKw,
    LetKw,
    ImplKw,
    DoKw,
    StructKw,
    SigKw,
    TypeKw,
    CaseKw,
    OfKw,
    TypeTypeKw,
    WithKw,
    PureKw,
    WhereKw,
    CatchKw,
    AndKw,
    OrKw,
    IfKw,
    ThenKw,
    ElseKw,
    EffKw,
    BoxKw,
    UnboxKw,
    MutKw,
    ImmKw,
    OwnKw,
    RefKw,
    TraitKw,
    AsKw,
    IsKw,
    ModKw,
    Colon,
    Equals,
    Arrow,
    WideArrow,
    WavyArrow,
    SingleQuote,
    Plus,
    Minus,
    Times,
    Div,
    Mod,
    Bar,
    Dot,
    Comma,
    Xor,
    LShift,
    RShift,
    BitAnd,
    Gt,
    GtE,
    Lt,
    LtE,
    Eq,
    NEq,
    LPipe,
    RPipe,
    FloatLit,
    IntLit,
    Name,
    StringLit,
    At,
    POpen,
    PClose,
    SOpen,
    SClose,
    COpen,
    CClose,
    Indent,
    Dedent,
    Newline,
    Backslash,
    Error,
    Whitespace,
    Comment,
    Eof,
}

type STok = (Tok, u32);
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexResult {
    pub kind: Vec<Tok>,
    pub start: Vec<u32>,
    pub errors: Vec<S<LexError>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexError {
    InvalidToken(char),
    UnclosedString,
    /// This is used for specific errors that occur in one place, in the parser or lexer.
    Other(String),
}

pub struct Lexer {
    chars: Peekable<im_rope::Chars<im_rope::accessor::OwningAccessor>>,
    input: Rope,
    tok_start: u32,
    pos: u32,

    indent_stack: Vec<usize>,
    pending_toks: VecDeque<STok>,
    errors: Vec<S<LexError>>,
}

impl Lexer {
    pub fn new(input: Rope) -> Self {
        Lexer {
            chars: input.clone().into_chars().peekable(),
            input,
            tok_start: 0,
            pos: 0,
            indent_stack: Vec::new(),
            pending_toks: VecDeque::new(),
            errors: Vec::new(),
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn next(&mut self) -> Option<char> {
        self.pos += self.chars.peek().map_or(0, |x| x.len_utf8() as u32);
        self.chars.next()
    }

    pub fn span(&self) -> Span {
        Span(self.tok_start, self.pos)
    }
    fn slice(&self) -> Rope {
        self.input
            .subrope(self.tok_start as usize..self.pos as usize)
    }

    // TODO should we include trivia in the token stream? in the parse tree?
    fn process_trivia(&mut self) {
        #[derive(PartialEq)]
        enum Mode {
            None,
            Comment,
            Space,
        }
        let mut mode = Mode::None;
        while let Some(next) = self.peek() {
            // Process line comments, but don't consume the newline
            if next == '#' {
                if mode == Mode::Space {
                    self.pending_toks.push_back(self.tok_in_place(Tok::Comment));
                    self.tok_start = self.pos;
                }
                mode = Mode::Comment;
                while self.peek().map_or(false, |x| x != '\n') {
                    self.next();
                }
            } else if next.is_whitespace() && next != '\n' {
                if mode == Mode::Comment {
                    self.pending_toks
                        .push_back(self.tok_in_place(Tok::Whitespace));
                    self.tok_start = self.pos;
                }
                mode = Mode::Space;
                self.next();
            } else {
                if mode != Mode::None {
                    self.pending_toks
                        .push_back(self.tok_in_place(Tok::Whitespace));
                    self.tok_start = self.pos;
                }
                break;
            }
        }
    }

    fn tok(&mut self, tok: Tok) -> STok {
        self.next();
        (tok, self.tok_start)
    }

    fn tok_in_place(&self, tok: Tok) -> STok {
        (tok, self.tok_start)
    }

    fn lex_number(&mut self) -> STok {
        // No error checking, that all happens in the typechecker
        // So this is just a regex `-?[A-Za-z0-9_]*(.[A-Za-z0-9_]*)?`
        // and it's only called when the input starts with `-?[0-9]`
        if self.peek() == Some('-') {
            self.next();
        }
        while self
            .peek()
            .map_or(false, |x| x.is_alphanumeric() || x == '_')
        {
            self.next();
        }
        if self.peek() == Some('.') {
            self.next();
            while self
                .peek()
                .map_or(false, |x| x.is_alphanumeric() || x == '_')
            {
                self.next();
            }
            return self.tok_in_place(Tok::FloatLit);
        } else {
            return self.tok_in_place(Tok::IntLit);
        }
    }

    fn lex_name(&mut self) -> STok {
        while let Some(next) = self.peek() {
            if name_char(next) {
                self.next();
            } else {
                break;
            }
        }
        let tok = match &*self.slice().to_string() {
            "def" => Tok::DefKw,
            "let" => Tok::LetKw,
            "impl" => Tok::ImplKw,
            "type" => Tok::TypeKw,
            "Type" => Tok::TypeTypeKw,
            "case" => Tok::CaseKw,
            "with" => Tok::WithKw,
            "pure" => Tok::PureKw,
            "catch" => Tok::CatchKw,
            "and" => Tok::AndKw,
            "or" => Tok::OrKw,
            "if" => Tok::IfKw,
            "then" => Tok::ThenKw,
            "else" => Tok::ElseKw,
            "box" => Tok::BoxKw,
            "unbox" => Tok::UnboxKw,
            "where" => Tok::WhereKw,
            "eff" => Tok::EffKw,
            "do" => Tok::DoKw,
            "struct" => Tok::StructKw,
            "sig" => Tok::SigKw,
            "of" => Tok::OfKw,
            "mut" => Tok::MutKw,
            "imm" => Tok::ImmKw,
            "own" => Tok::OwnKw,
            "ref" => Tok::RefKw,
            "trait" => Tok::TraitKw,
            "as" => Tok::AsKw,
            "is" => Tok::IsKw,
            "mod" => Tok::ModKw,
            _ => Tok::Name,
        };
        self.tok_in_place(tok)
    }

    fn try_lex_binop(&mut self) -> Option<STok> {
        match self.peek()? {
            ':' => Some(self.tok(Tok::Colon)),
            '.' => Some(self.tok(Tok::Dot)),
            ',' => Some(self.tok(Tok::Comma)),
            '|' => {
                self.next();
                if self.peek() == Some('>') {
                    Some(self.tok(Tok::RPipe))
                } else {
                    Some(self.tok_in_place(Tok::Bar))
                }
            }

            '+' => Some(self.tok(Tok::Plus)),
            '*' => {
                self.next();
                Some(self.tok_in_place(Tok::Times))
            }
            '/' => Some(self.tok(Tok::Div)),
            '%' => Some(self.tok(Tok::Mod)),

            '^' => {
                self.next();
                if self.peek() == Some('^') {
                    Some(self.tok(Tok::Xor))
                } else {
                    self.errors.push(S(LexError::Other("Ambiguous operator '^': use '**' for exponentiation, and '^^' for bitwise xor".into()), self.span()));
                    Some(self.tok_in_place(Tok::Error))
                }
            }
            '<' => {
                self.next();
                Some(match self.peek() {
                    Some('<') => self.tok(Tok::LShift),
                    Some('=') => self.tok(Tok::LtE),
                    Some('|') => self.tok(Tok::LPipe),
                    _ => self.tok_in_place(Tok::Lt),
                })
            }
            '>' => {
                self.next();
                Some(match self.peek() {
                    Some('>') => self.tok(Tok::RShift),
                    Some('=') => self.tok(Tok::GtE),
                    _ => self.tok_in_place(Tok::Gt),
                })
            }
            '&' => {
                self.next();
                Some(self.tok_in_place(Tok::BitAnd))
            }

            '!' => {
                self.next();
                if self.peek() == Some('=') {
                    Some(self.tok(Tok::NEq))
                } else {
                    None
                }
            }
            '=' => {
                self.next();
                Some(match self.peek() {
                    Some('>') => self.tok(Tok::WideArrow),
                    Some('=') => self.tok(Tok::Eq),
                    _ => self.tok_in_place(Tok::Equals),
                })
            }
            '~' => {
                self.next();
                if self.peek() == Some('>') {
                    Some(self.tok(Tok::WavyArrow))
                } else {
                    None
                }
            }
            // '-' could be the start of a negative number
            // This seems to be the best way to access the next character
            '-' if self
                .input
                .subrope(self.pos as usize + 1..)
                .chars()
                .next()
                .map_or(true, |x| !x.is_ascii_digit()) =>
            {
                self.next();
                if self.peek() == Some('>') {
                    Some(self.tok(Tok::Arrow))
                } else {
                    Some(self.tok_in_place(Tok::Minus))
                }
            }
            _ => None,
        }
    }

    fn lex_other(&mut self) -> STok {
        match self.peek().unwrap() {
            '(' => self.tok(Tok::POpen),
            ')' => self.tok(Tok::PClose),
            '[' => self.tok(Tok::SOpen),
            ']' => self.tok(Tok::SClose),
            '{' => self.tok(Tok::COpen),
            '}' => self.tok(Tok::CClose),

            '@' => self.tok(Tok::At),
            '\\' => self.tok(Tok::Backslash),
            ';' => self.tok(Tok::Newline),
            '\'' => self.tok(Tok::SingleQuote),

            '\n' => {
                // We're going to emit one or more tokens which might include newline, indent, and dedent
                // First find the next non-empty line and record its starting position
                let mut start_pos = 0;
                while let Some(c) = self.peek() {
                    match c {
                        '\n' => start_pos = 0,
                        ' ' => start_pos += 1,
                        x if x.is_whitespace() => {
                            self.next();
                            self.errors.push(S(
                                LexError::Other("Only spaces are supported for indentation".into()),
                                self.span(),
                            ));
                            return self.tok_in_place(Tok::Error);
                        }
                        '#' => {
                            self.process_trivia();
                            continue;
                        }
                        _ => break,
                    }
                    self.next();
                }
                let mut i = 0;
                while i < self.indent_stack.len() {
                    if start_pos >= self.indent_stack[i] {
                        start_pos -= self.indent_stack[i];
                        i += 1;
                    } else if start_pos == 0 {
                        self.pending_toks.push_back(self.tok_in_place(Tok::Dedent));
                        self.indent_stack.remove(i);
                    } else {
                        self.errors.push(S(LexError::Other("Inconsistent indentation: dedent doesn't match any previous indentation level".into()), self.span()));
                        return self.tok_in_place(Tok::Error);
                    }
                }
                if start_pos > 0 {
                    self.indent_stack.push(start_pos);
                    self.pending_toks.push_back(self.tok_in_place(Tok::Indent));
                } else {
                    self.pending_toks.push_back(self.tok_in_place(Tok::Newline));
                }

                self.pending_toks.pop_front().unwrap()
            }

            '"' => {
                self.next();
                let mut buf = String::new();
                loop {
                    match self.next() {
                        Some('"') => break self.tok_in_place(Tok::StringLit),
                        Some('\\') => {
                            // Escape sequence, which will be processed during elaboration
                            self.next();
                        }
                        Some(c) => buf.push(c),
                        None => {
                            self.errors.push(S(
                                LexError::UnclosedString,
                                Span(self.tok_start, self.pos - 1),
                            ));
                            break self.tok_in_place(Tok::Error);
                        }
                    }
                }
            }

            // This is called after `try_lex_binop()`, so if we get a '-' it must be a number
            x if x.is_numeric() || x == '-' => self.lex_number(),
            x if name_start_char(x) => self.lex_name(),
            x => {
                self.next();
                self.errors.push(S(LexError::InvalidToken(x), self.span()));
                self.tok_in_place(Tok::Error)
            }
        }
    }

    fn next_tok(&mut self) -> Option<STok> {
        if let Some(tok) = self.pending_toks.pop_front() {
            return Some(tok);
        }

        self.tok_start = self.pos;
        self.process_trivia();

        if let Some(tok) = self.pending_toks.pop_front() {
            return Some(tok);
        }

        if let Some(binop) = self.try_lex_binop() {
            return Some(binop);
        }

        if self.peek().is_some() {
            let other = self.lex_other();
            Some(other)
        } else {
            for _ in 0..self.indent_stack.len() {
                self.pending_toks.push_back(self.tok_in_place(Tok::Dedent));
            }
            self.indent_stack.clear();
            self.pending_toks.pop_front()
        }
    }

    pub fn lex(&mut self) -> LexResult {
        let mut kind = Vec::new();
        let mut start = Vec::new();
        while let Some((tok, pos)) = self.next_tok() {
            kind.push(tok);
            start.push(pos);
        }
        LexResult {
            kind,
            start,
            errors: self.errors.split_off(0),
        }
    }
}

fn name_char(c: char) -> bool {
    match c {
        _ if c.is_alphanumeric() => true,
        '_' | '?' | '\'' => true,
        _ => false,
    }
}
fn name_start_char(c: char) -> bool {
    match c {
        _ if c.is_alphabetic() => true,
        '_' | '?' => true,
        _ => false,
    }
}

pub fn lexerror_to_error(lex: LexError, span: Span) -> Error {
    let message = match lex {
        LexError::InvalidToken(c) => Doc::start("Invalid token: '")
            .add(c, Doc::COLOR1)
            .add("'", ()),
        LexError::UnclosedString => Doc::start("Unclosed ")
            .add("string literal", Doc::COLOR1)
            .add(": expected a terminator '", ())
            .add('"', Doc::COLOR2)
            .add("' here", ()),
        LexError::Other(s) => Doc::start(s),
    };
    Error {
        severity: Severity::Error,
        message: message.clone(),
        message_lsp: None,
        primary: Label {
            span,
            message,
            color: Some(Doc::COLOR1),
        },
        secondary: Vec::new(),
        note: None,
    }
}

impl<'i> fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Tok::DefKw => "'def'",
            Tok::LetKw => "'let'",
            Tok::ImplKw => "'impl'",
            Tok::DoKw => "'do'",
            Tok::StructKw => "'struct'",
            Tok::SigKw => "'sig'",
            Tok::TypeKw => "'type'",
            Tok::CaseKw => "'case'",
            Tok::OfKw => "'of'",
            Tok::TypeTypeKw => "'Type'",
            Tok::WithKw => "'with'",
            Tok::PureKw => "'pure'",
            Tok::WhereKw => "'where'",
            Tok::CatchKw => "'catch'",
            Tok::AndKw => "'and'",
            Tok::OrKw => "'or'",
            Tok::IfKw => "'if'",
            Tok::ThenKw => "'then'",
            Tok::ElseKw => "'else'",
            Tok::EffKw => "'eff'",
            Tok::BoxKw => "'box'",
            Tok::UnboxKw => "'unbox'",
            Tok::MutKw => "'mut'",
            Tok::ImmKw => "'imm'",
            Tok::OwnKw => "'own'",
            Tok::RefKw => "'ref'",
            Tok::TraitKw => "'trait'",
            Tok::AsKw => "'as'",
            Tok::IsKw => "'is'",
            Tok::ModKw => "'mod'",
            Tok::Colon => "':'",
            Tok::Equals => "'='",
            Tok::Arrow => "'->'",
            Tok::WideArrow => "'=>'",
            Tok::WavyArrow => "'~>'",
            Tok::SingleQuote => "region '_",
            Tok::Plus => "'+'",
            Tok::Minus => "'-'",
            Tok::Times => "'*'",
            Tok::Div => "'/'",
            Tok::Mod => "'%'",
            Tok::Bar => "'|'",
            Tok::Dot => "'.'",
            Tok::Comma => "','",
            Tok::Xor => "'^^'",
            Tok::LShift => "'<<'",
            Tok::RShift => "'>>'",
            Tok::BitAnd => "'&'",
            Tok::Gt => "'>'",
            Tok::GtE => "'>='",
            Tok::Lt => "'<'",
            Tok::LtE => "'<='",
            Tok::Eq => "'=='",
            Tok::NEq => "'!='",
            Tok::LPipe => "'<|'",
            Tok::RPipe => "'|>'",
            Tok::FloatLit => "float literal",
            Tok::IntLit => "int literal",
            Tok::Name => "name",
            Tok::StringLit => "string literal",
            Tok::At => "'@'",
            Tok::POpen => "'('",
            Tok::PClose => "')'",
            Tok::SOpen => "'['",
            Tok::SClose => "']'",
            Tok::COpen => "'{'",
            Tok::CClose => "'}'",
            Tok::Indent => "indent",
            Tok::Dedent => "dedent",
            Tok::Newline => "newline",
            Tok::Backslash => "'\\'",
            Tok::Error => "<error>",

            Tok::Whitespace => "whitespace",
            Tok::Comment => "comment",

            Tok::Eof => "end of file",
        })
    }
}
