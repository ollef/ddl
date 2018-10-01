//! Pretty printing for the concrete syntax

use pretty::Doc;

use syntax::concrete::{
    Definition, Exposing, Item, LamParamGroup, Literal, Module, Pattern, PiParamGroup, Term,
};
use syntax::{FloatFormat, IntFormat};

use super::{StaticDoc, ToDoc};

const INDENT_WIDTH: usize = 4;

impl ToDoc for Module {
    fn to_doc(&self) -> StaticDoc {
        match *self {
            Module::Valid {
                ref name,
                ref items,
            } => Doc::group(
                Doc::text("module")
                    .append(Doc::space())
                    .append(Doc::as_string(&name.1))
                    .append(Doc::text(";")),
            ).append(Doc::newline())
            .append(Doc::newline())
            .append(Doc::intersperse(
                items.iter().map(|item| item.to_doc()),
                Doc::newline().append(Doc::newline()),
            )),
            Module::Error(_) => Doc::text("<error>"),
        }
    }
}

impl ToDoc for Item {
    fn to_doc(&self) -> StaticDoc {
        match *self {
            Item::Import {
                name: (_, ref name),
                ref rename,
                ref exposing,
                ..
            } => Doc::text("module")
                .append(Doc::space())
                .append(Doc::as_string(name))
                .append(rename.as_ref().map_or(Doc::nil(), |&(_, ref rename)| {
                    Doc::space()
                        .append(Doc::text("as"))
                        .append(Doc::space())
                        .append(Doc::as_string(rename))
                })).append(exposing.as_ref().map_or(Doc::nil(), |exposing| {
                    Doc::space().append(exposing.to_doc())
                })),
            Item::Declaration {
                name: (_, ref name),
                ref ann,
            } => Doc::as_string(name)
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(ann.to_doc()),
            Item::Definition(ref definition) => definition.to_doc(),
            Item::Error(_) => Doc::text("<error>"),
        }.append(";")
    }
}

impl ToDoc for Definition {
    fn to_doc(&self) -> StaticDoc {
        match *self {
            Definition::Alias {
                name: (_, ref name),
                ref params,
                ref return_ann,
                ref term,
            } => Doc::as_string(name)
                .append(Doc::space())
                .append(match params[..] {
                    [] => Doc::nil(),
                    _ => pretty_lam_params(params).append(Doc::space()),
                }).append(return_ann.as_ref().map_or(Doc::nil(), |return_ann| {
                    Doc::text(":")
                        .append(return_ann.to_doc())
                        .append(Doc::space())
                })).append("=")
                .append(Doc::space())
                .append(term.to_doc().nest(INDENT_WIDTH)),
            Definition::StructType {
                name: (_, ref name),
                ref fields,
                ..
            }
                if fields.is_empty() =>
            {
                Doc::text("struct")
                    .append(Doc::space())
                    .append(Doc::as_string(name))
                    .append(Doc::space())
                    .append("{}")
            },
            Definition::StructType {
                name: (_, ref name),
                ref fields,
                ..
            } => Doc::text("struct")
                .append(Doc::space())
                .append(Doc::as_string(name))
                .append(Doc::space())
                .append("{")
                .append(Doc::space())
                .append(
                    Doc::intersperse(
                        fields.iter().map(|field| {
                            Doc::as_string(&field.label.1)
                                .append(match field.binder {
                                    Some((_, ref binder)) => Doc::space()
                                        .append("as")
                                        .append(Doc::space())
                                        .append(Doc::as_string(binder)),
                                    None => Doc::nil(),
                                }).append(Doc::space())
                                .append(":")
                                .append(Doc::space())
                                .append(field.ann.to_doc())
                        }),
                        Doc::text(",").append(Doc::space()),
                    ).nest(INDENT_WIDTH),
                ).append(Doc::space())
                .append("}"),
        }
    }
}

impl ToDoc for Exposing {
    fn to_doc(&self) -> StaticDoc {
        match *self {
            Exposing::All(_) => Doc::text("(..)"),
            Exposing::Exact(_, ref imports) => Doc::intersperse(
                imports.iter().map(|&((_, ref name), ref rename)| {
                    Doc::as_string(name).append(rename.as_ref().map_or(
                        Doc::nil(),
                        |&(_, ref rename)| {
                            Doc::space()
                                .append(Doc::text("as"))
                                .append(Doc::space())
                                .append(Doc::as_string(rename))
                        },
                    ))
                }),
                Doc::text(",").append(Doc::space()),
            ),
            Exposing::Error(_) => Doc::text("<error>"),
        }
    }
}

impl ToDoc for Literal {
    fn to_doc(&self) -> StaticDoc {
        match *self {
            Literal::String(_, ref value) => Doc::text(format!("{:?}", value)),
            Literal::Char(_, value) => Doc::text(format!("{:?}", value)),
            Literal::Int(_, ref value, IntFormat::Bin) => Doc::text(format!("0b{:b}", value)),
            Literal::Int(_, ref value, IntFormat::Oct) => Doc::text(format!("0o{:o}", value)),
            Literal::Int(_, ref value, IntFormat::Dec) => Doc::text(format!("{}", value)),
            Literal::Int(_, ref value, IntFormat::Hex) => Doc::text(format!("0x{:x}", value)),
            Literal::Float(_, value, FloatFormat::Dec) => Doc::text(format!("{}", value)),
        }
    }
}

impl ToDoc for Pattern {
    fn to_doc(&self) -> StaticDoc {
        match *self {
            Pattern::Parens(_, ref term) => Doc::text("(").append(term.to_doc()).append(")"),
            Pattern::Ann(ref term, ref ty) => term
                .to_doc()
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(ty.to_doc()),
            Pattern::Name(_, ref name) => Doc::as_string(name),
            Pattern::Literal(ref literal) => literal.to_doc(),
            Pattern::Error(_) => Doc::text("<error>"),
        }
    }
}

impl ToDoc for Term {
    fn to_doc(&self) -> StaticDoc {
        match *self {
            Term::Parens(_, ref term) => Doc::text("(").append(term.to_doc()).append(")"),
            Term::Ann(ref term, ref ty) => term
                .to_doc()
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(ty.to_doc()),
            Term::Universe(_, level) => {
                Doc::text("Type").append(level.map_or(Doc::nil(), |level| {
                    Doc::space().append(Doc::as_string(&level))
                }))
            },
            Term::IntTypeSingleton(_, ref value) => Doc::text("{=")
                .append(Doc::space())
                .append(value.to_doc())
                .append(Doc::text("}")),
            Term::IntType(_, ref min, ref max) => Doc::text("int")
                .append(Doc::space())
                .append(Doc::text("{"))
                .append(
                    min.as_ref()
                        .map_or(Doc::nil(), |x| x.to_doc().append(Doc::space())),
                ).append(Doc::text(".."))
                .append(
                    max.as_ref()
                        .map_or(Doc::nil(), |x| Doc::space().append(x.to_doc())),
                ).append(Doc::text("}")),
            Term::Literal(ref literal) => literal.to_doc(),
            Term::Array(_, ref elems) => Doc::text("[")
                .append(Doc::intersperse(
                    elems.iter().map(Term::to_doc),
                    Doc::text(",").append(Doc::space()),
                )).append("]"),
            Term::Hole(_) => Doc::text("_"),
            Term::Name(_, ref name) => Doc::as_string(name),
            Term::Extern(_, _, ref name) => Doc::text("extern")
                .append(Doc::space())
                .append(format!("{:?}", name)),
            Term::Lam(_, ref params, ref body) => Doc::text("\\")
                .append(pretty_lam_params(params))
                .append(Doc::space())
                .append("=>")
                .append(Doc::space())
                .append(body.to_doc()),
            Term::Pi(_, ref params, ref body) => pretty_pi_params(params)
                .append(Doc::space())
                .append("->")
                .append(Doc::space())
                .append(body.to_doc()),
            Term::Arrow(ref ann, ref body) => ann
                .to_doc()
                .append(Doc::space())
                .append("->")
                .append(Doc::space())
                .append(body.to_doc()),
            Term::App(ref head, ref args) => head.to_doc().append(Doc::space()).append(
                Doc::intersperse(args.iter().map(|arg| arg.to_doc()), Doc::space()),
            ),
            Term::Unop(_, op, ref term) => Doc::text(op.symbol()).append(term.to_doc()),
            Term::Binop(ref lhs, op, ref rhs) => lhs
                .to_doc()
                .append(Doc::space())
                .append(op.symbol())
                .append(Doc::space())
                .append(rhs.to_doc()),
            Term::Let(_, ref decls, ref body) => {
                Doc::text("let")
                    .append(Doc::space())
                    .append(Doc::intersperse(
                        // FIXME: Indentation
                        decls.iter().map(|decl| decl.to_doc()),
                        Doc::newline(),
                    )).append("in")
                    .append(body.to_doc())
            },
            Term::If(_, ref cond, ref if_true, ref if_false) => Doc::text("if")
                .append(Doc::space())
                .append(cond.to_doc())
                .append(Doc::space())
                .append("then")
                .append(Doc::space())
                .append(if_true.to_doc())
                .append(Doc::space())
                .append("else")
                .append(Doc::space())
                .append(if_false.to_doc()),
            Term::Match(_, ref head, ref clauses) => Doc::text("match")
                .append(Doc::space())
                .append(head.to_doc())
                .append(Doc::space())
                .append("{")
                .append(Doc::newline())
                .append(
                    Doc::concat(clauses.iter().map(|&(ref pattern, ref body)| {
                        pattern
                            .to_doc()
                            .append(Doc::space())
                            .append("=>")
                            .append(Doc::space())
                            .append(body.to_doc())
                            .append(";")
                            .append(Doc::newline())
                    })).nest(INDENT_WIDTH),
                ).append("}"),
            Term::Struct(_, ref fields) if fields.is_empty() => Doc::text("struct {}"),
            Term::Struct(_, ref fields) => Doc::text("struct {")
                .append(Doc::space())
                .append(
                    Doc::intersperse(
                        fields.iter().map(|field| {
                            Doc::as_string(&field.label.1)
                                .append(Doc::space())
                                .append("=")
                                .append(Doc::space())
                                .append(field.term.to_doc())
                        }),
                        Doc::text(",").append(Doc::space()),
                    ).nest(INDENT_WIDTH),
                ).append(Doc::space())
                .append("}"),
            Term::Proj(ref expr, _, ref label) => {
                expr.to_doc().append(".").append(Doc::as_string(label))
            },
            Term::Error(_) => Doc::text("<error>"),
        }
    }
}

fn pretty_lam_params(params: &[LamParamGroup]) -> StaticDoc {
    Doc::intersperse(
        params.iter().map(|&(ref names, ref ann)| match *ann {
            None if names.len() == 1 => Doc::as_string(&names[0].1),
            None => unreachable!(), // FIXME - shouldn't be possible in AST
            Some(ref ann) => Doc::text("(")
                .append(Doc::intersperse(
                    names.iter().map(|name| Doc::as_string(&name.1)),
                    Doc::space(),
                )).append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(ann.to_doc())
                .append(")"),
        }),
        Doc::space(),
    )
}

fn pretty_pi_params(params: &[PiParamGroup]) -> StaticDoc {
    Doc::intersperse(
        params.iter().map(|&(ref names, ref ann)| {
            Doc::text("(")
                .append(Doc::intersperse(
                    names.iter().map(|name| Doc::as_string(&name.1)),
                    Doc::space(),
                )).append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(ann.to_doc())
                .append(")")
        }),
        Doc::space(),
    )
}
