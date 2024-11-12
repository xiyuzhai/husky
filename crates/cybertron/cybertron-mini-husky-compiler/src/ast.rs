mod alloc;
pub mod call;
pub mod defn;
pub mod delimited;
pub mod helpers;
pub mod opr;
pub mod reduce;
pub mod stmt;
mod utils;

use self::{alloc::*, reduce::*, utils::*};
use crate::{
    token::{ident::Ident, keyword::Keyword, literal::Literal, opr::Opr, Token},
    *,
};
use cybertron::seq::idx::Option2;
use cybertron::{
    prelude::*,
    seq::{idx::Idx, Seq},
};
use std::fmt::Pointer;
use token::{
    delimiter::{Delimiter, LeftDelimiter, RightDelimiter},
    keyword::DefnKeyword,
    opr::{BinaryOpr, PrefixOpr, SuffixOpr},
    separator::Separator,
    tokenize,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ast {
    pub parent: Option<Idx>,
    pub data: AstData,
}

/// Enumeration representing different types of Abstract Syntax Tree (AST) nodes
#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstData {
    /// Represents a literal value (e.g., integer, string)
    Literal(Literal),
    /// Represents an identifier (e.g., variable name)
    Ident(Ident),
    /// Represents a prefix expression (e.g., `!x`, `-x`)
    ///
    /// # exprs
    Prefix {
        /// Operator in the prefix expression (e.g., `!`, `-`)
        opr: PrefixOpr,
        /// Operand index of the expression
        opd: Idx,
    },
    /// Represents a binary expression (e.g., `x + y`, `a * b`)
    Binary {
        /// Index of the left operand
        lopd: Idx,
        lopd_ident: Option<Ident>,
        /// Operator in the binary expression (e.g., `+`, `*`)
        opr: BinaryOpr,
        /// Index of the right operand
        ropd: Idx,
    },
    /// Represents a suffix expression (e.g., `x++`, `y--`)
    Suffix {
        /// Index of the operand
        opd: Idx,
        /// Operator in the suffix expression (e.g., `++`, `--`)
        opr: SuffixOpr,
    },
    /// Represents a delimited expression (e.g., `(x + y)`, `{a, b, c}`)
    Delimited {
        /// Index of the left delimiter in the expression
        left_delimiter_idx: Idx,
        /// The left delimiter (e.g., `(`, `{`)
        left_delimiter: LeftDelimiter,
        /// The right delimiter (e.g., `)`, `}`)
        right_delimiter: RightDelimiter,
    },
    /// Represents an item separated by a separator (e.g., elements in an array or list)
    SeparatedItem {
        /// Index of the content, if any
        content: Option<Idx>,
        /// The separator (e.g., `,`, `;`)
        separator: Separator,
    },
    /// Represents a function call or array access (e.g., `f(...)`, `a[...]`)
    ///
    /// things like `f(...)` or `a[...]`
    Call {
        /// Index of the caller (e.g., function or array)
        caller: Idx,
        caller_ident: Option<Ident>,
        /// The left delimiter of the call (e.g., `(`, `[`)
        left_delimiter: LeftDelimiter,
        /// The right delimiter of the call (e.g., `)`, `]`)
        right_delimiter: RightDelimiter,
        /// Index of the delimited arguments in the call
        delimited_arguments: Idx,
    },
    /// Represents a `let` statement with an initialization (e.g., `let x = 5;`)
    ///
    /// # stmts
    LetInit {
        /// Index of the expression in the initialization
        expr: Idx,
        /// Index of the pattern being initialized
        pattern: Idx,
        /// Optional index of the initial value
        initial_value: Option<Idx>,
    },
    Return {
        result: Idx,
    },
    Assert {
        condition: Idx,
    },
    /// Represents an `if` statement
    If {
        /// Index of the condition in the `if` statement
        condition: Idx,
        /// Index of the body of the `if` statement
        body: Idx,
    },
    /// Represents an `else` statement
    Else {
        /// Index of the associated `if` statement
        if_stmt: Idx,
        /// Index of the body of the `else` statement
        body: Idx,
    },
    /// Represents a function or variable definition
    ///
    /// # defn
    Defn {
        /// The keyword in the definition (e.g., `fn`, `enum`)
        keyword: DefnKeyword,
        /// Index of the identifier in the definition
        ident_idx: Idx,
        /// The identifier being defined (e.g., function name, variable name)
        ident: Ident,
        /// Index of the content or body of the definition
        content: Idx,
    },
}

impl Into<Option<Ast>> for Token {
    fn into(self) -> Option<Ast> {
        let data = match self {
            Token::Literal(lit) => Some(AstData::Literal(lit)),
            Token::Keyword(_) => None,
            Token::Ident(ident) => Some(AstData::Ident(ident)),
            Token::Opr(_) => None,
            Token::LeftDelimiter(_) => None,
            Token::RightDelimiter(_) => None,
            Token::Separator(_) => None,
        }?;
        Some(Ast { parent: None, data })
    }
}

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstError {
    Opr,
}

/// The `PreAst` enum represents the intermediate forms of tokens and ASTs that are
/// encountered during the parsing phase, before the final AST is constructed.
/// Each variant corresponds to a specific type of token or partial
/// AST node that contributes to the construction of the final AST.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PreAst {
    /// A reserved keyword in the language, such as `if`, `else`, `while`, etc.
    Keyword(Keyword),
    /// An operator, such as `+`, `-`, `*`, `==`, etc., representing mathematical
    /// or logical operations.
    Opr(Opr),
    /// A left delimiter, such as `(`, `{`, `[`, used to denote the beginning of
    /// a block, list, or expression.
    LeftDelimiter(LeftDelimiter),
    /// A right delimiter, such as `)`, `}`, `]`, used to denote the end of a
    /// block, list, or expression.
    RightDelimiter(RightDelimiter),
    /// A partially constructed AST node, representing a more complex structure
    /// that will be further processed to build the final AST.
    Ast(AstData),
    /// A separator, such as `,` or `;`, used to separate elements in a list or
    /// statements in a block.
    Separator(Separator),
}

impl std::fmt::Debug for PreAst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PreAst::Keyword(slf) => slf.fmt(f),
            PreAst::Opr(slf) => slf.fmt(f),
            PreAst::LeftDelimiter(slf) => slf.fmt(f),
            PreAst::RightDelimiter(slf) => slf.fmt(f),
            PreAst::Ast(slf) => slf.fmt(f),
            PreAst::Separator(slf) => slf.fmt(f),
        }
    }
}

impl From<Token> for PreAst {
    fn from(token: Token) -> Self {
        match token {
            Token::Keyword(kw) => PreAst::Keyword(kw),
            Token::Ident(ident) => PreAst::Ast(AstData::Ident(ident)),
            Token::Opr(opr) => PreAst::Opr(opr),
            Token::Literal(lit) => PreAst::Ast(AstData::Literal(lit)),
            Token::LeftDelimiter(delimiter) => PreAst::LeftDelimiter(delimiter),
            Token::RightDelimiter(delimiter) => PreAst::RightDelimiter(delimiter),
            Token::Separator(separator) => PreAst::Separator(separator),
        }
    }
}

pub fn calc_pre_ast_initial_seq(tokens: Seq<Token>) -> Seq<Option<PreAst>> {
    tokens.map(|token| Some(token.into()))
}

#[test]
fn calc_pre_ast_initial_seq_works() {
    fn t(input: &str, expect: Expect) {
        expect.assert_debug_eq(&calc_pre_ast_initial_seq(tokenize(input)))
    }
    t(
        "hello",
        expect![[r#"
            [Some(Ident(`hello`))]
        "#]],
    );
    t(
        "let hello = world + humans",
        expect![[r#"
            [
                Some(`let`),
                Some(Ident(`hello`)),
                Some(`=`),
                Some(Ident(`world`)),
                Some(`+(add)`),
                Some(Ident(`humans`)),
            ]
        "#]],
    );
}

pub fn calc_asts_from_input(input: &str, n: usize) -> Seq<Option<Ast>> {
    calc_asts_from_input_together_with_tokens_and_pre_asts(input, n).2
}

pub fn calc_asts_from_input_together_with_tokens_and_pre_asts(
    input: &str,
    n: usize,
) -> (Seq<Token>, Seq<Option<PreAst>>, Seq<Option<Ast>>) {
    let tokens = tokenize(input);
    let pre_asts = calc_pre_ast_initial_seq(tokens);
    let allocated_asts: Seq<Option<Ast>> = tokens.map(|token| token.into());
    let (pre_asts, asts) = reduce_n_times(pre_asts, allocated_asts, n);
    (tokens, pre_asts, asts)
}
