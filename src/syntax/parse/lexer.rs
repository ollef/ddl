use codespan::{ByteSpan, FileMap};
use codespan_reporting::{Diagnostic, Label};
use num_bigint::BigInt;
use num_traits::Num;
use std::fmt;
use std::str::{CharIndices, FromStr};

use codespan::{ByteIndex, ByteOffset, RawOffset};
use unicode_xid::UnicodeXID;

fn is_symbol(ch: char) -> bool {
    match ch {
        '&' | '!' | ':' | ',' | '.' | '=' | '/' | '>' | '<' | '-' | '|' | '+' | ';' | '*' => true,
        _ => false,
    }
}

fn is_ident_start(ch: char) -> bool {
    UnicodeXID::is_xid_start(ch) || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    UnicodeXID::is_xid_continue(ch) || ch == '_'
}

fn is_bin_digit(ch: char) -> bool {
    ch.is_digit(2)
}

fn is_oct_digit(ch: char) -> bool {
    ch.is_digit(8)
}

fn is_dec_digit(ch: char) -> bool {
    ch.is_digit(10)
}

fn is_hex_digit(ch: char) -> bool {
    ch.is_digit(16)
}

/// An error that occurred while lexing the source file
#[derive(Fail, Debug, Clone, PartialEq, Eq)]
pub enum LexerError {
    #[fail(display = "An unexpected character {:?} was found.", found)]
    UnexpectedCharacter { start: ByteIndex, found: char },
    #[fail(display = "Unexpected end of file.")]
    UnexpectedE { end: ByteIndex },
    #[fail(display = "Unterminated string literal.")]
    UnterminatedStringLiteral { span: ByteSpan },
    #[fail(display = "Unterminated character literal.")]
    UnterminatedCharLiteral { span: ByteSpan },
    #[fail(display = "Unterminated a binary literal.")]
    UnterminatedBinLiteral { span: ByteSpan },
    #[fail(display = "Unterminated a octal literal.")]
    UnterminatedOctLiteral { span: ByteSpan },
    #[fail(display = "Unterminated a hexidecimal literal.")]
    UnterminatedHexLiteral { span: ByteSpan },
    #[fail(display = "Empty character literal.")]
    EmptyCharLiteral { span: ByteSpan },
    #[fail(display = "An unknown escape code \\{} was found.", found)]
    UnknownEscapeCode { start: ByteIndex, found: char },
}

impl LexerError {
    /// Return the span of source code that this error originated from
    pub fn span(&self) -> ByteSpan {
        match *self {
            LexerError::UnexpectedCharacter { start, found }
            | LexerError::UnknownEscapeCode { start, found } => {
                ByteSpan::from_offset(start, ByteOffset::from_char_utf8(found))
            },
            LexerError::UnexpectedE { end } => ByteSpan::new(end, end),
            LexerError::UnterminatedStringLiteral { span }
            | LexerError::UnterminatedCharLiteral { span }
            | LexerError::UnterminatedBinLiteral { span }
            | LexerError::UnterminatedOctLiteral { span }
            | LexerError::UnterminatedHexLiteral { span }
            | LexerError::EmptyCharLiteral { span } => span,
        }
    }

    pub fn to_diagnostic(&self) -> Diagnostic {
        match *self {
            LexerError::UnexpectedCharacter { start, found } => {
                let char_span = ByteSpan::from_offset(start, ByteOffset::from_char_utf8(found));
                Diagnostic::new_error(format!("unexpected character {:?}", found))
                    .with_label(Label::new_primary(char_span))
            },
            LexerError::UnexpectedE { end } => Diagnostic::new_error("unexpected end of file")
                .with_label(Label::new_primary(ByteSpan::new(end, end))),
            LexerError::UnterminatedStringLiteral { span } => {
                Diagnostic::new_error("unterminated string literal")
                    .with_label(Label::new_primary(span))
            },
            LexerError::UnterminatedCharLiteral { span } => {
                Diagnostic::new_error("unterminated character literal")
                    .with_label(Label::new_primary(span))
            },
            LexerError::UnterminatedBinLiteral { span } => {
                Diagnostic::new_error("unterminated binary literal")
                    .with_label(Label::new_primary(span))
            },
            LexerError::UnterminatedOctLiteral { span } => {
                Diagnostic::new_error("unterminated octal literal")
                    .with_label(Label::new_primary(span))
            },
            LexerError::UnterminatedHexLiteral { span } => {
                Diagnostic::new_error("unterminated hexadecimal literal")
                    .with_label(Label::new_primary(span))
            },
            LexerError::EmptyCharLiteral { span } => {
                Diagnostic::new_error("empty character literal")
                    .with_label(Label::new_primary(span))
            },
            LexerError::UnknownEscapeCode { start, found } => {
                let char_span = ByteSpan::from_offset(start, ByteOffset::from_char_utf8(found));
                Diagnostic::new_error(format!("unknown escape code \\{}", found))
                    .with_label(Label::new_primary(char_span))
            },
        }
    }
}

/// A token in the source file, to be emitted by the `Lexer`
#[derive(Clone, Debug, PartialEq)]
pub enum Token<S> {
    // Data
    Ident(S),
    DocComment(S),
    ReplCommand(S),
    StringLiteral(String),
    CharLiteral(char),
    BinIntLiteral(BigInt),
    OctIntLiteral(BigInt),
    DecIntLiteral(BigInt),
    HexIntLiteral(BigInt),
    DecFloatLiteral(f64),

    // Keywords
    As,     // as
    Match,  // match
    Else,   // else
    Extern, // extern
    If,     // if
    Import, // import
    In,     // in
    Int,    // int
    Let,    // let
    Module, // module
    Struct, // struct
    Type,   // Type

    // Symbols
    Amp,           // &
    AmpAmp,        // &&
    Bang,          // !
    BangEqual,     // !=
    Asterisk,      // *
    BSlash,        // \
    Colon,         // :
    Comma,         // ,
    Dot,           // .
    DotDot,        // ..
    Equal,         // =
    EqualEqual,    // ==
    EqualGreater,  // =>
    FSlash,        // /
    Greater,       // >
    GreaterEqual,  // >=
    Hyphen,        // -
    HyphenGreater, // ->
    Less,          // <
    LessEqual,     // <=
    Pipe,          // |
    PipePipe,      // ||
    Plus,          // +
    Semi,          // ;

    // Delimiters
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]
}

impl<S: fmt::Display> fmt::Display for Token<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Token::Ident(ref name) => write!(f, "{}", name),
            Token::DocComment(ref comment) => write!(f, "/// {}", comment),
            Token::ReplCommand(ref command) => write!(f, ":{}", command),
            Token::StringLiteral(ref value) => write!(f, "{:?}", value),
            Token::CharLiteral(ref value) => write!(f, "'{:?}'", value),
            Token::BinIntLiteral(ref value) => write!(f, "{:b}", value),
            Token::OctIntLiteral(ref value) => write!(f, "{:o}", value),
            Token::DecIntLiteral(ref value) => write!(f, "{}", value),
            Token::HexIntLiteral(ref value) => write!(f, "{:x}", value),
            Token::DecFloatLiteral(ref value) => write!(f, "{}", value),

            Token::As => write!(f, "as"),
            Token::Match => write!(f, "match"),
            Token::Else => write!(f, "else"),
            Token::Extern => write!(f, "extern"),
            Token::If => write!(f, "if"),
            Token::Import => write!(f, "import"),
            Token::In => write!(f, "in"),
            Token::Int => write!(f, "int"),
            Token::Let => write!(f, "let"),
            Token::Module => write!(f, "module"),
            Token::Struct => write!(f, "struct"),
            Token::Type => write!(f, "Type"),

            Token::Amp => write!(f, "&"),
            Token::AmpAmp => write!(f, "&&"),
            Token::Asterisk => write!(f, "*"),
            Token::Bang => write!(f, "!"),
            Token::BangEqual => write!(f, "!="),
            Token::BSlash => write!(f, "\\"),
            Token::Colon => write!(f, ":"),
            Token::Comma => write!(f, ","),
            Token::Dot => write!(f, "."),
            Token::DotDot => write!(f, ".."),
            Token::Equal => write!(f, "="),
            Token::EqualEqual => write!(f, "=="),
            Token::EqualGreater => write!(f, "=>"),
            Token::FSlash => write!(f, "/"),
            Token::Greater => write!(f, ">"),
            Token::GreaterEqual => write!(f, ">="),
            Token::Hyphen => write!(f, "-"),
            Token::HyphenGreater => write!(f, "->"),
            Token::Less => write!(f, "<"),
            Token::LessEqual => write!(f, "<="),
            Token::Pipe => write!(f, "|"),
            Token::PipePipe => write!(f, "||"),
            Token::Plus => write!(f, "+"),
            Token::Semi => write!(f, ";"),

            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
        }
    }
}

impl<'input> From<Token<&'input str>> for Token<String> {
    fn from(src: Token<&'input str>) -> Token<String> {
        match src {
            Token::Ident(name) => Token::Ident(name.to_owned()),
            Token::DocComment(comment) => Token::DocComment(comment.to_owned()),
            Token::ReplCommand(command) => Token::ReplCommand(command.to_owned()),
            Token::StringLiteral(value) => Token::StringLiteral(value),
            Token::CharLiteral(value) => Token::CharLiteral(value),
            Token::BinIntLiteral(value) => Token::BinIntLiteral(value),
            Token::OctIntLiteral(value) => Token::OctIntLiteral(value),
            Token::DecIntLiteral(value) => Token::DecIntLiteral(value),
            Token::HexIntLiteral(value) => Token::HexIntLiteral(value),
            Token::DecFloatLiteral(value) => Token::DecFloatLiteral(value),

            Token::As => Token::As,
            Token::Match => Token::Match,
            Token::Else => Token::Else,
            Token::Extern => Token::Extern,
            Token::If => Token::If,
            Token::Import => Token::Import,
            Token::In => Token::In,
            Token::Int => Token::Int,
            Token::Let => Token::Let,
            Token::Module => Token::Module,
            Token::Struct => Token::Struct,
            Token::Type => Token::Type,

            Token::Amp => Token::Amp,
            Token::AmpAmp => Token::AmpAmp,
            Token::Asterisk => Token::Asterisk,
            Token::Bang => Token::Bang,
            Token::BangEqual => Token::BangEqual,
            Token::BSlash => Token::BSlash,
            Token::Colon => Token::Colon,
            Token::Comma => Token::Comma,
            Token::Dot => Token::Dot,
            Token::DotDot => Token::DotDot,
            Token::Equal => Token::Equal,
            Token::EqualEqual => Token::EqualEqual,
            Token::EqualGreater => Token::EqualGreater,
            Token::FSlash => Token::FSlash,
            Token::Greater => Token::Greater,
            Token::GreaterEqual => Token::GreaterEqual,
            Token::Hyphen => Token::Hyphen,
            Token::HyphenGreater => Token::HyphenGreater,
            Token::Less => Token::Less,
            Token::LessEqual => Token::LessEqual,
            Token::Pipe => Token::Pipe,
            Token::PipePipe => Token::PipePipe,
            Token::Plus => Token::Plus,
            Token::Semi => Token::Semi,

            Token::LParen => Token::LParen,
            Token::RParen => Token::RParen,
            Token::LBrace => Token::LBrace,
            Token::RBrace => Token::RBrace,
            Token::LBracket => Token::LBracket,
            Token::RBracket => Token::RBracket,
        }
    }
}

/// An iterator over a source string that yields `Token`s for subsequent use by
/// the parser
pub struct Lexer<'input> {
    filemap: &'input FileMap,
    chars: CharIndices<'input>,
    lookahead: Option<(usize, char)>,
}

impl<'input> Lexer<'input> {
    /// Create a new lexer from the source string
    pub fn new(filemap: &'input FileMap) -> Self {
        let mut chars = filemap.src().char_indices();

        Lexer {
            filemap,
            lookahead: chars.next(),
            chars,
        }
    }

    /// Returns the index of the end of the file
    fn eof(&self) -> ByteIndex {
        self.filemap.span().end()
    }

    /// Return the next character in the source string
    fn lookahead(&self) -> Option<(ByteIndex, char)> {
        self.lookahead.map(|(index, ch)| {
            let off = ByteOffset(index as RawOffset);
            let index = self.filemap.span().start() + off;
            (index, ch)
        })
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position.
    fn bump(&mut self) -> Option<(ByteIndex, char)> {
        let current = self.lookahead();
        self.lookahead = self.chars.next();
        current
    }

    /// Return a slice of the source string
    fn slice(&self, start: ByteIndex, end: ByteIndex) -> &'input str {
        &self.filemap.src_slice(ByteSpan::new(start, end)).unwrap()
    }

    /// Test a predicate against the next character in the source
    fn test_lookahead<F>(&self, mut pred: F) -> bool
    where
        F: FnMut(char) -> bool,
    {
        self.lookahead.map_or(false, |(_, ch)| pred(ch))
    }

    /// Consume characters while the predicate matches for the current
    /// character, then return the consumed slice and the end byte
    /// position.
    fn take_while<F>(&mut self, start: ByteIndex, mut keep_going: F) -> (ByteIndex, &'input str)
    where
        F: FnMut(char) -> bool,
    {
        self.take_until(start, |ch| !keep_going(ch))
    }

    /// Consume characters until the predicate matches for the next character
    /// in the lookahead, then return the consumed slice and the end byte
    /// position.
    fn take_until<F>(&mut self, start: ByteIndex, mut terminate: F) -> (ByteIndex, &'input str)
    where
        F: FnMut(char) -> bool,
    {
        while let Some((end, ch)) = self.lookahead() {
            if terminate(ch) {
                return (end, self.slice(start, end));
            } else {
                self.bump();
            }
        }

        let eof = self.eof();
        (eof, self.slice(start, eof))
    }

    /// Consume a REPL command
    fn repl_command(&mut self, start: ByteIndex) -> SpannedToken<'input> {
        let (end, command) = self.take_while(start + ByteOffset::from_str(":"), |ch| {
            is_ident_continue(ch) || ch == '?'
        });

        if command.is_empty() {
            (start, Token::Colon, end)
        } else {
            (start, Token::ReplCommand(command), end)
        }
    }

    /// Consume a doc comment
    fn doc_comment(&mut self, start: ByteIndex) -> SpannedToken<'input> {
        let (end, mut comment) =
            self.take_until(start + ByteOffset::from_str("///"), |ch| ch == '\n');

        // Skip preceding space
        if comment.starts_with(' ') {
            comment = &comment[1..];
        }

        (start, Token::DocComment(comment), end)
    }

    /// Consume an identifier
    fn ident(&mut self, start: ByteIndex) -> SpannedToken<'input> {
        let (end, ident) = self.take_while(start, is_ident_continue);

        let token = match ident {
            "as" => Token::As,
            "match" => Token::Match,
            "else" => Token::Else,
            "extern" => Token::Extern,
            "if" => Token::If,
            "import" => Token::Import,
            "in" => Token::In,
            "int" => Token::Int,
            "let" => Token::Let,
            "module" => Token::Module,
            "struct" => Token::Struct,
            "Type" => Token::Type,
            ident => Token::Ident(ident),
        };

        (start, token, end)
    }

    /// Consume an escape code
    fn escape_code(&mut self, start: ByteIndex) -> Result<char, LexerError> {
        match self.bump() {
            Some((_, '\'')) => Ok('\''),
            Some((_, '"')) => Ok('"'),
            Some((_, '\\')) => Ok('\\'),
            Some((_, '/')) => Ok('/'),
            Some((_, 'n')) => Ok('\n'),
            Some((_, 'r')) => Ok('\r'),
            Some((_, 't')) => Ok('\t'),
            // TODO: Unicode escape codes
            Some((start, ch)) => Err(LexerError::UnknownEscapeCode { start, found: ch }),
            None => Err(LexerError::UnexpectedE { end: start }),
        }
    }

    /// Consume a string literal
    fn string_literal(&mut self, start: ByteIndex) -> Result<SpannedToken<'input>, LexerError> {
        let mut string = String::new();
        let mut end = start;

        while let Some((next, ch)) = self.bump() {
            end = next + ByteOffset::from_char_utf8(ch);
            match ch {
                '\\' => string.push(self.escape_code(next)?),
                '"' => return Ok((start, Token::StringLiteral(string), end)),
                ch => string.push(ch),
            }
        }

        Err(LexerError::UnterminatedStringLiteral {
            span: ByteSpan::new(start, end),
        })
    }

    /// Consume a character literal
    fn char_literal(&mut self, start: ByteIndex) -> Result<SpannedToken<'input>, LexerError> {
        let ch = match self.bump() {
            Some((next, '\\')) => self.escape_code(next)?,
            Some((next, '\'')) => {
                return Err(LexerError::EmptyCharLiteral {
                    span: ByteSpan::new(start, next + ByteOffset::from_char_utf8('\'')),
                })
            },
            Some((_, ch)) => ch,
            None => return Err(LexerError::UnexpectedE { end: start }),
        };

        match self.bump() {
            Some((end, '\'')) => Ok((
                start,
                Token::CharLiteral(ch),
                end + ByteOffset::from_char_utf8('\''),
            )),
            Some((next, ch)) => Err(LexerError::UnterminatedCharLiteral {
                span: ByteSpan::new(start, next + ByteOffset::from_char_utf8(ch)),
            }),
            None => Err(LexerError::UnexpectedE { end: start }),
        }
    }

    /// Consume a binary literal token
    fn bin_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<(ByteIndex, Token<&'input str>, ByteIndex), LexerError> {
        self.bump(); // skip 'b'
        let (end, src) = self.take_while(start + ByteOffset(2), is_bin_digit);
        if src.is_empty() {
            Err(LexerError::UnterminatedBinLiteral {
                span: ByteSpan::new(start, end),
            })
        } else {
            let int = BigInt::from_str_radix(src, 2).unwrap();
            Ok((start, Token::BinIntLiteral(int), end))
        }
    }

    /// Consume a octal literal token
    fn oct_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<(ByteIndex, Token<&'input str>, ByteIndex), LexerError> {
        self.bump(); // skip 'o'
        let (end, src) = self.take_while(start + ByteOffset(2), is_oct_digit);
        if src.is_empty() {
            Err(LexerError::UnterminatedOctLiteral {
                span: ByteSpan::new(start, end),
            })
        } else {
            let int = BigInt::from_str_radix(src, 8).unwrap();
            Ok((start, Token::OctIntLiteral(int), end))
        }
    }

    /// Consume a decimal literal
    fn dec_literal(&mut self, start: ByteIndex) -> Result<SpannedToken<'input>, LexerError> {
        let (end, src) = self.take_while(start, is_dec_digit);

        if let Some((_, '.')) = self.lookahead() {
            self.bump(); // skip '.'
            let (end, src) = self.take_while(start, is_dec_digit);

            match f64::from_str(src) {
                Ok(value) => Ok((start, Token::DecFloatLiteral(value), end)),
                Err(_) => unimplemented!(),
            }
        } else {
            let value = BigInt::from_str_radix(src, 10).unwrap();
            Ok((start, Token::DecIntLiteral(value), end))
        }
    }

    /// Consume a hexadecimal literal token
    fn hex_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<(ByteIndex, Token<&'input str>, ByteIndex), LexerError> {
        self.bump(); // skip 'x'
        let (end, src) = self.take_while(start + ByteOffset(2), is_hex_digit);
        if src.is_empty() {
            Err(LexerError::UnterminatedHexLiteral {
                span: ByteSpan::new(start, end),
            })
        } else {
            let int = BigInt::from_str_radix(src, 16).unwrap();
            Ok((start, Token::HexIntLiteral(int), end))
        }
    }
}

pub type SpannedToken<'input> = (ByteIndex, Token<&'input str>, ByteIndex);

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<(ByteIndex, Token<&'input str>, ByteIndex), LexerError>;

    #[cfg_attr(feature = "cargo-clippy", allow(cyclomatic_complexity))]
    fn next(&mut self) -> Option<Result<SpannedToken<'input>, LexerError>> {
        while let Some((start, ch)) = self.bump() {
            let end = start + ByteOffset::from_char_utf8(ch);

            return Some(match ch {
                ch if is_symbol(ch) => {
                    let (end, symbol) = self.take_while(start, is_symbol);

                    match symbol {
                        "&" => Ok((start, Token::Amp, end)),
                        "&&" => Ok((start, Token::AmpAmp, end)),
                        "*" => Ok((start, Token::Asterisk, end)),
                        "!" => Ok((start, Token::Bang, end)),
                        "!=" => Ok((start, Token::BangEqual, end)),
                        // "\\" => Ok((start, Token::BSlash, end)),
                        ":" => Ok(self.repl_command(start)),
                        "," => Ok((start, Token::Comma, end)),
                        "." => Ok((start, Token::Dot, end)),
                        ".." => Ok((start, Token::DotDot, end)),
                        "=" => Ok((start, Token::Equal, end)),
                        "==" => Ok((start, Token::EqualEqual, end)),
                        "=>" => Ok((start, Token::EqualGreater, end)),
                        "/" => Ok((start, Token::FSlash, end)),
                        ">" => Ok((start, Token::Greater, end)),
                        ">=" => Ok((start, Token::GreaterEqual, end)),
                        "-" => Ok((start, Token::Hyphen, end)),
                        "->" => Ok((start, Token::HyphenGreater, end)),
                        "<" => Ok((start, Token::Less, end)),
                        "<=" => Ok((start, Token::LessEqual, end)),
                        "|" => Ok((start, Token::Pipe, end)),
                        "||" => Ok((start, Token::PipePipe, end)),
                        "+" => Ok((start, Token::Plus, end)),
                        ";" => Ok((start, Token::Semi, end)),

                        symbol if symbol.starts_with("///") => Ok(self.doc_comment(start)),
                        symbol if symbol.starts_with("//") => {
                            self.take_until(start, |ch| ch == '\n');
                            continue;
                        },
                        _ => Err(LexerError::UnexpectedCharacter { start, found: ch }),
                    }
                },
                '\\' => Ok((start, Token::BSlash, end)),
                '(' => Ok((start, Token::LParen, end)),
                ')' => Ok((start, Token::RParen, end)),
                '{' => Ok((start, Token::LBrace, end)),
                '}' => Ok((start, Token::RBrace, end)),
                '[' => Ok((start, Token::LBracket, end)),
                ']' => Ok((start, Token::RBracket, end)),
                '"' => self.string_literal(start),
                '\'' => self.char_literal(start),
                '0' if self.test_lookahead(|x| x == 'b') => self.bin_literal(start),
                '0' if self.test_lookahead(|x| x == 'o') => self.oct_literal(start),
                '0' if self.test_lookahead(|x| x == 'x') => self.hex_literal(start),
                ch if is_ident_start(ch) => Ok(self.ident(start)),
                ch if is_dec_digit(ch) => self.dec_literal(start),
                ch if ch.is_whitespace() => continue,
                _ => Err(LexerError::UnexpectedCharacter { start, found: ch }),
            });
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use codespan::RawIndex;
    use codespan::{CodeMap, FileName};

    use super::*;

    /// A handy macro to give us a nice syntax for declaring test matchs
    ///
    /// This was inspired by the tests in the LALRPOP lexer
    macro_rules! test {
        ($src:expr, $($span:expr => $token:expr,)*) => {{
            let mut codemap = CodeMap::new();
            let filemap = codemap.add_filemap(FileName::virtual_("test"), $src.into());

            let lexed_tokens: Vec<_> = Lexer::new(&filemap).collect();
            let expected_tokens = vec![$({
                let start = ByteIndex($span.find("~").unwrap() as RawIndex + 1);
                let end = ByteIndex($span.rfind("~").unwrap() as RawIndex + 2);
                Ok((start, $token, end))
            }),*];

            assert_eq!(lexed_tokens, expected_tokens);
        }};
    }

    #[test]
    fn data() {
        test! {
            "  hello_hahaha8ABC  ",
            "  ~~~~~~~~~~~~~~~~  " => Token::Ident("hello_hahaha8ABC"),
        };
    }

    #[test]
    fn comment() {
        test! {
            "       // hello this is dog\n  ",
        };
    }

    #[test]
    fn doc_comment() {
        test! {
            "       /// hello this is dog",
            "       ~~~~~~~~~~~~~~~~~~~~~" => Token::DocComment("hello this is dog"),
        };
    }

    #[test]
    fn string_literal() {
        test! {
            r#"  "a" "\t"  "#,
            r#"  ~~~       "# => Token::StringLiteral("a".to_owned()),
            r#"      ~~~~  "# => Token::StringLiteral("\t".to_owned()),
        };
    }

    #[test]
    fn char_literal() {
        test! {
            r"  'a' '\t'  ",
            r"  ~~~       " => Token::CharLiteral('a'),
            r"      ~~~~  " => Token::CharLiteral('\t'),
        };
    }

    #[test]
    fn bin_literal() {
        test! {
            "  0b010110  ",
            "  ~~~~~~~~  " => Token::BinIntLiteral(BigInt::from(0b010110)),
        };
    }

    #[test]
    fn oct_literal() {
        test! {
            "  0o12371  ",
            "  ~~~~~~~  " => Token::OctIntLiteral(BigInt::from(0o12371)),
        };
    }

    #[test]
    fn dec_literal() {
        test! {
            "  123  ",
            "  ~~~  " => Token::DecIntLiteral(BigInt::from(123)),
        };
    }

    #[test]
    fn hex_literal() {
        test! {
            "  0x123AF  ",
            "  ~~~~~~~  " => Token::HexIntLiteral(BigInt::from(0x123AF)),
        };
    }

    #[test]
    fn float_literal() {
        test! {
            "  122.345  ",
            "  ~~~~~~~  " => Token::DecFloatLiteral(122.345),
        };
    }

    #[test]
    fn keywords() {
        test! {
            "  as else extern if import in int let match module struct Type  ",
            "  ~~                                                            " => Token::As,
            "     ~~~~                                                       " => Token::Else,
            "          ~~~~~~                                                " => Token::Extern,
            "                 ~~                                             " => Token::If,
            "                    ~~~~~~                                      " => Token::Import,
            "                           ~~                                   " => Token::In,
            "                              ~~~                               " => Token::Int,
            "                                  ~~~                           " => Token::Let,
            "                                      ~~~~~                     " => Token::Match,
            "                                            ~~~~~~              " => Token::Module,
            "                                                   ~~~~~~       " => Token::Struct,
            "                                                          ~~~~  " => Token::Type,
        };
    }

    #[test]
    fn symbols() {
        test! {
            r" & && * ! != \ : , .. = == => / > >= - -> < <= | || + ; ",
            r" ~                                                      " => Token::Amp,
            r"   ~~                                                   " => Token::AmpAmp,
            r"      ~                                                 " => Token::Asterisk,
            r"        ~                                               " => Token::Bang,
            r"          ~~                                            " => Token::BangEqual,
            r"             ~                                          " => Token::BSlash,
            r"               ~                                        " => Token::Colon,
            r"                 ~                                      " => Token::Comma,
            r"                   ~~                                   " => Token::DotDot,
            r"                      ~                                 " => Token::Equal,
            r"                        ~~                              " => Token::EqualEqual,
            r"                           ~~                           " => Token::EqualGreater,
            r"                              ~                         " => Token::FSlash,
            r"                                ~                       " => Token::Greater,
            r"                                  ~~                    " => Token::GreaterEqual,
            r"                                     ~                  " => Token::Hyphen,
            r"                                       ~~               " => Token::HyphenGreater,
            r"                                          ~             " => Token::Less,
            r"                                            ~~          " => Token::LessEqual,
            r"                                               ~        " => Token::Pipe,
            r"                                                 ~~     " => Token::PipePipe,
            r"                                                    ~   " => Token::Plus,
            r"                                                      ~ " => Token::Semi,
        }
    }

    #[test]
    fn delimiters() {
        test! {
            " ( ) { } [ ] ",
            " ~           " => Token::LParen,
            "   ~         " => Token::RParen,
            "     ~       " => Token::LBrace,
            "       ~     " => Token::RBrace,
            "         ~   " => Token::LBracket,
            "           ~ " => Token::RBracket,
        }
    }
}
