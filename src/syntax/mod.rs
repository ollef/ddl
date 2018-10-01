//! The syntax of the language

use moniker::{Binder, BoundPattern, BoundTerm, ScopeState, Var};
use std::fmt;

pub mod concrete;
pub mod core;
pub mod parse;
pub mod pretty;
pub mod raw;
pub mod translation;

/// A universe level
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, BoundTerm)]
pub struct Level(pub u32);

impl Level {
    pub fn succ(self) -> Level {
        Level(self.0 + 1)
    }
}

impl From<u32> for Level {
    fn from(src: u32) -> Level {
        Level(src)
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An unary operator
#[derive(Debug, Copy, Clone, PartialEq, Eq, BoundTerm)]
pub enum Unop {
    /// Negation: eg. `-x`
    Neg,
    /// Not: eg. `!x`
    Not,
}

impl Unop {
    pub fn symbol(&self) -> &'static str {
        match *self {
            Unop::Neg => "-",
            Unop::Not => "!",
        }
    }
}

/// A binary operator
#[derive(Debug, Copy, Clone, PartialEq, Eq, BoundTerm)]
pub enum Binop {
    /// Disjunction: eg. `x | y`
    Or,
    /// Conjunction: eg. `x & y`
    And,
    /// Equality: eg. `x == y`
    Eq,
    /// Inequality: eg. `x != y`
    Ne,
    /// Less than or equal: eg. `x <= y`
    Le,
    /// Less than: eg. `x < y`
    Lt,
    /// Greater than: eg. `x > y`
    Gt,
    /// Greater than or equal: eg. `x >= y`
    Ge,
    /// Addition: eg. `x + y`
    Add,
    /// Subtraction: eg. `x - y`
    Sub,
    /// Multiplication: eg. `x * y`
    Mul,
    /// Division: eg. `x / y`
    Div,
}

impl Binop {
    pub fn symbol(&self) -> &'static str {
        match *self {
            Binop::Or => "|",
            Binop::And => "&",
            Binop::Eq => "==",
            Binop::Ne => "!=",
            Binop::Le => "<=",
            Binop::Lt => "<",
            Binop::Gt => ">",
            Binop::Ge => ">=",
            Binop::Add => "+",
            Binop::Sub => "-",
            Binop::Mul => "*",
            Binop::Div => "/",
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntFormat {
    Bin,
    Oct,
    Dec,
    Hex,
}

impl<N> BoundTerm<N> for IntFormat {
    fn term_eq(&self, _: &IntFormat) -> bool {
        true
    }

    fn close_term(&mut self, _: ScopeState, _: &[Binder<N>]) {}
    fn open_term(&mut self, _: ScopeState, _: &[Binder<N>]) {}
    fn visit_vars(&self, _: &mut impl FnMut(&Var<N>)) {}
    fn visit_mut_vars(&mut self, _: &mut impl FnMut(&mut Var<N>)) {}
}

impl<N> BoundPattern<N> for IntFormat {
    fn pattern_eq(&self, _: &IntFormat) -> bool {
        true
    }

    fn close_pattern(&mut self, _: ScopeState, _: &[Binder<N>]) {}
    fn open_pattern(&mut self, _: ScopeState, _: &[Binder<N>]) {}
    fn visit_binders(&self, _: &mut impl FnMut(&Binder<N>)) {}
    fn visit_mut_binders(&mut self, _: &mut impl FnMut(&mut Binder<N>)) {}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloatFormat {
    Dec,
    // TODO: Binary and Hex floats?
}

impl<N> BoundTerm<N> for FloatFormat {
    fn term_eq(&self, _: &FloatFormat) -> bool {
        true
    }

    fn close_term(&mut self, _: ScopeState, _: &[Binder<N>]) {}
    fn open_term(&mut self, _: ScopeState, _: &[Binder<N>]) {}
    fn visit_vars(&self, _: &mut impl FnMut(&Var<N>)) {}
    fn visit_mut_vars(&mut self, _: &mut impl FnMut(&mut Var<N>)) {}
}

impl<N> BoundPattern<N> for FloatFormat {
    fn pattern_eq(&self, _: &FloatFormat) -> bool {
        true
    }

    fn close_pattern(&mut self, _: ScopeState, _: &[Binder<N>]) {}
    fn open_pattern(&mut self, _: ScopeState, _: &[Binder<N>]) {}
    fn visit_binders(&self, _: &mut impl FnMut(&Binder<N>)) {}
    fn visit_mut_binders(&mut self, _: &mut impl FnMut(&mut Binder<N>)) {}
}

/// A label that describes the name of a field in a record
///
/// Labels are significant when comparing for alpha-equality
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, BoundPattern, BoundTerm)]
pub struct Label(pub String);

impl From<String> for Label {
    fn from(src: String) -> Label {
        Label(src)
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
