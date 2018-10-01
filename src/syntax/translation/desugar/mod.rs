use codespan::{ByteOffset, ByteSpan};
use im::HashMap;
use moniker::{Binder, Embed, FreeVar, Nest, Scope, Var};

use syntax::concrete;
use syntax::raw;
use syntax::{Label, Level};

#[cfg(test)]
mod tests;

/// The environment used when desugaring from the concrete to raw syntax
#[derive(Debug, Clone)]
pub struct DesugarEnv {
    /// An environment that maps strings to unique free variables
    ///
    /// This is a persistent map so that we can create new environments as we enter
    /// new scopes, allowing us to properly model variable shadowing.
    ///
    /// If we arrive at a variable that has not already been assigned a free name,
    /// we assume that it is a global name.
    locals: HashMap<String, FreeVar<String>>,
}

impl DesugarEnv {
    pub fn new(mappings: HashMap<String, FreeVar<String>>) -> DesugarEnv {
        DesugarEnv { locals: mappings }
    }

    pub fn on_item(&mut self, name: &str) -> Binder<String> {
        if let Some(free_var) = self.locals.get(name) {
            return Binder(free_var.clone());
        }
        Binder(self.on_binding(name))
    }

    pub fn on_binding(&mut self, name: &str) -> FreeVar<String> {
        let name = name.to_owned();
        let free_var = FreeVar::fresh_named(name.clone());
        self.locals.insert(name, free_var.clone());
        free_var
    }

    pub fn on_name(&self, span: ByteSpan, name: &str) -> raw::RcTerm {
        raw::RcTerm::from(raw::Term::Var(
            span,
            Var::Free(match self.locals.get(name) {
                None => FreeVar::fresh_named(name),
                Some(free_var) => free_var.clone(),
            }),
        ))
    }
}

/// Translate something to the corresponding core representation
pub trait Desugar<T> {
    fn desugar(&self, env: &DesugarEnv) -> T;
}

/// Convert a sugary pi type from something like:
///
/// ```text
/// (a b : t1) (c : t2) -> t3
/// ```
///
/// To a bunch of nested pi types like:
///
/// ```text
/// (a : t1) -> (b : t1) -> (c : t2) -> t3
/// ```
fn desugar_pi(
    env: &DesugarEnv,
    param_groups: &[concrete::PiParamGroup],
    body: &concrete::Term,
) -> raw::RcTerm {
    let mut env = env.clone();

    let mut params = Vec::new();
    for &(ref names, ref ann) in param_groups {
        let ann = raw::RcTerm::from(ann.desugar(&env));
        params.extend(names.iter().map(|&(start, ref name)| {
            let free_var = env.on_binding(name);
            (start, Binder(free_var), ann.clone())
        }));
    }

    params
        .into_iter()
        .rev()
        .fold(body.desugar(&env), |acc, (start, binder, ann)| {
            raw::RcTerm::from(raw::Term::Pi(
                ByteSpan::new(start, acc.span().end()),
                Scope::new((binder, Embed(ann.clone())), acc),
            ))
        })
}

/// Convert a sugary lambda from something like:
///
/// ```text
/// \(a b : t1) c (d : t2) => t3
/// ```
///
/// To a bunch of nested lambdas like:
///
/// ```text
/// \(a : t1) => \(b : t1) => \c => \(d : t2) => t3
/// ```
fn desugar_lam(
    env: &DesugarEnv,
    param_groups: &[concrete::LamParamGroup],
    return_ann: Option<&concrete::Term>,
    body: &concrete::Term,
) -> raw::RcTerm {
    let mut env = env.clone();

    let mut params = Vec::new();
    for &(ref names, ref ann) in param_groups {
        let ann = match *ann {
            None => raw::RcTerm::from(raw::Term::Hole(ByteSpan::default())),
            Some(ref ann) => ann.desugar(&env),
        };

        params.extend(names.iter().map(|&(start, ref name)| {
            let free_var = env.on_binding(name);
            (start, Binder(free_var), ann.clone())
        }));
    }

    let body = match return_ann {
        None => body.desugar(&env),
        Some(ann) => raw::RcTerm::from(raw::Term::Ann(body.desugar(&env), ann.desugar(&env))),
    };

    params
        .into_iter()
        .rev()
        .fold(body, |acc, (start, binder, ann)| {
            raw::RcTerm::from(raw::Term::Lam(
                ByteSpan::new(start, acc.span().end()),
                Scope::new((binder, Embed(ann.clone())), acc),
            ))
        })
}

fn desugar_struct(
    env: &DesugarEnv,
    span: ByteSpan,
    fields: &[concrete::StructField],
) -> raw::RcTerm {
    let fields = fields
        .iter()
        .map(|field| {
            let (_, ref label) = field.label;
            let term = field.term.desugar(&env);
            (Label(label.clone()), term)
        }).collect::<Vec<_>>();

    raw::RcTerm::from(raw::Term::Struct(span, fields))
}

impl Desugar<raw::Module> for concrete::Module {
    fn desugar(&self, env: &DesugarEnv) -> raw::Module {
        let mut env = env.clone();
        let (name, concrete_items) = match *self {
            concrete::Module::Valid {
                name: (_, ref name),
                ref items,
            } => (name.clone(), items),
            concrete::Module::Error(_) => unimplemented!("error recovery"),
        };

        let mut items = Vec::with_capacity(concrete_items.len());
        for concrete_item in concrete_items {
            let item = match *concrete_item {
                concrete::Item::Import { .. } => unimplemented!("import declarations"),
                concrete::Item::Declaration {
                    name: (start, ref name),
                    ref ann,
                } => {
                    let term = ann.desugar(&env);

                    raw::Item::Declaration {
                        label_span: ByteSpan::from_offset(start, ByteOffset::from_str(name)),
                        label: Label(name.clone()),
                        binder: env.on_item(name),
                        term,
                    }
                },
                concrete::Item::Definition(concrete::Definition::Alias {
                    name: (start, ref name),
                    ref params,
                    ref return_ann,
                    ref term,
                }) => {
                    let return_ann = return_ann.as_ref().map(<_>::as_ref);
                    let term = desugar_lam(&env, params, return_ann, term);

                    raw::Item::Definition {
                        label_span: ByteSpan::from_offset(start, ByteOffset::from_str(name)),
                        label: Label(name.clone()),
                        binder: env.on_item(name),
                        definition: raw::Definition::Alias(term),
                    }
                },
                concrete::Item::Definition(concrete::Definition::StructType {
                    span,
                    name: (start, ref name),
                    ref params,
                    ref fields,
                }) => {
                    let scope = {
                        let mut env = env.clone();

                        let params = params
                            .iter()
                            .map(|&(ref name, ref ann)| {
                                let ann = ann.desugar(&env);
                                let binder = env.on_binding(name);
                                (Binder(binder), Embed(ann))
                            }).collect();

                        let fields = fields
                            .iter()
                            .map(|field| {
                                let (_, ref label) = field.label;
                                let ann = field.ann.desugar(&env);
                                let free_var = env.on_binding(label);
                                (Label(label.clone()), Binder(free_var), Embed(ann))
                            }).collect();

                        Scope::new(Nest::new(params), Scope::new(Nest::new(fields), ()))
                    };

                    raw::Item::Definition {
                        label_span: ByteSpan::from_offset(start, ByteOffset::from_str(name)),
                        label: Label(name.clone()),
                        binder: env.on_item(name),
                        definition: raw::Definition::StructType(span, scope),
                    }
                },
                concrete::Item::Error(_) => unimplemented!("error recovery"),
            };

            items.push(item);
        }

        raw::Module { name, items }
    }
}

impl Desugar<raw::Literal> for concrete::Literal {
    fn desugar(&self, _: &DesugarEnv) -> raw::Literal {
        match *self {
            concrete::Literal::String(span, ref val) => raw::Literal::String(span, val.clone()),
            concrete::Literal::Char(span, val) => raw::Literal::Char(span, val),
            concrete::Literal::Int(span, ref val, format) => {
                raw::Literal::Int(span, val.clone(), format)
            },
            concrete::Literal::Float(span, val, format) => raw::Literal::Float(span, val, format),
        }
    }
}

impl Desugar<(raw::RcPattern, DesugarEnv)> for concrete::Pattern {
    fn desugar(&self, env: &DesugarEnv) -> (raw::RcPattern, DesugarEnv) {
        let span = self.span();
        match *self {
            concrete::Pattern::Parens(_, ref pattern) => pattern.desugar(env),
            concrete::Pattern::Ann(ref pattern, ref ty) => {
                let ty = ty.desugar(env);
                let (pattern, env) = pattern.desugar(env);
                let ann_pattern = raw::RcPattern::from(raw::Pattern::Ann(pattern, Embed(ty)));

                (ann_pattern, env)
            },
            concrete::Pattern::Name(_, ref name) => match env.locals.get(name) {
                Some(free_var) => {
                    let var = Var::Free(free_var.clone());
                    let pattern = raw::RcPattern::from(raw::Pattern::Var(span, Embed(var)));

                    (pattern, env.clone())
                },
                None => {
                    let mut env = env.clone();
                    let free_var = env.on_binding(name);
                    let binder = Binder(free_var);
                    let pattern = raw::RcPattern::from(raw::Pattern::Binder(span, binder));

                    (pattern, env)
                },
            },
            concrete::Pattern::Literal(ref literal) => (
                raw::RcPattern::from(raw::Pattern::Literal(literal.desugar(env))),
                env.clone(),
            ),
            concrete::Pattern::Error(_) => unimplemented!("error recovery"),
        }
    }
}

impl Desugar<raw::RcTerm> for concrete::Term {
    fn desugar(&self, env: &DesugarEnv) -> raw::RcTerm {
        let span = self.span();
        match *self {
            concrete::Term::Parens(_, ref term) => term.desugar(env),
            concrete::Term::Ann(ref expr, ref ty) => {
                raw::RcTerm::from(raw::Term::Ann(expr.desugar(env), ty.desugar(env)))
            },
            concrete::Term::Universe(_, level) => {
                raw::RcTerm::from(raw::Term::Universe(span, Level(level.unwrap_or(0))))
            },
            concrete::Term::IntTypeSingleton(_, ref value) => {
                let value = value.desugar(env);
                raw::RcTerm::from(raw::Term::IntType(span, Some(value.clone()), Some(value)))
            },
            concrete::Term::IntType(_, ref min, ref max) => raw::RcTerm::from(raw::Term::IntType(
                span,
                min.as_ref().map(|x| x.desugar(env)),
                max.as_ref().map(|x| x.desugar(env)),
            )),
            concrete::Term::Extern(_, name_span, ref name) => {
                raw::RcTerm::from(raw::Term::Extern(span, name_span, name.clone()))
            },
            concrete::Term::Literal(ref literal) => {
                raw::RcTerm::from(raw::Term::Literal(literal.desugar(env)))
            },
            concrete::Term::Array(_, ref elems) => raw::RcTerm::from(raw::Term::Array(
                span,
                elems.iter().map(|elem| elem.desugar(env)).collect(),
            )),
            concrete::Term::Hole(_) => raw::RcTerm::from(raw::Term::Hole(span)),
            concrete::Term::Name(_, ref name) => env.on_name(span, name),
            concrete::Term::Pi(_, ref params, ref body) => desugar_pi(env, params, body),
            concrete::Term::Lam(_, ref params, ref body) => desugar_lam(env, params, None, body),
            concrete::Term::Arrow(ref ann, ref body) => raw::RcTerm::from(raw::Term::Pi(
                span,
                Scope::new(
                    (Binder(FreeVar::fresh_unnamed()), Embed(ann.desugar(env))),
                    body.desugar(env),
                ),
            )),
            concrete::Term::App(ref head, ref args) => {
                args.iter().fold(head.desugar(env), |acc, arg| {
                    raw::RcTerm::from(raw::Term::App(acc, arg.desugar(env)))
                })
            },
            concrete::Term::Unop(start, op, ref term) => {
                raw::RcTerm::from(raw::Term::Unop(start, op, term.desugar(env)))
            },
            concrete::Term::Binop(ref lhs, op, ref rhs) => {
                raw::RcTerm::from(raw::Term::Binop(lhs.desugar(env), op, rhs.desugar(env)))
            },
            concrete::Term::Let(_, ref _items, ref _body) => unimplemented!("let bindings"),
            concrete::Term::If(_, ref cond, ref if_true, ref if_false) => {
                let bool_pattern = |name: &str| {
                    raw::RcPattern::from(raw::Pattern::Var(
                        ByteSpan::default(),
                        Embed(Var::Free(match env.locals.get(name) {
                            Some(free_var) => free_var.clone(),
                            None => FreeVar::fresh_named("oops"),
                        })),
                    ))
                };

                raw::RcTerm::from(raw::Term::Match(
                    span,
                    cond.desugar(env),
                    vec![
                        Scope::new(bool_pattern("true"), if_true.desugar(&env)),
                        Scope::new(bool_pattern("false"), if_false.desugar(&env)),
                    ],
                ))
            },
            concrete::Term::Match(span, ref head, ref clauses) => {
                raw::RcTerm::from(raw::Term::Match(
                    span,
                    head.desugar(env),
                    clauses
                        .iter()
                        .map(|(pattern, term)| {
                            let (pattern, env) = pattern.desugar(env);
                            Scope::new(pattern, term.desugar(&env))
                        }).collect(),
                ))
            },
            concrete::Term::Struct(span, ref fields) => desugar_struct(env, span, fields),
            concrete::Term::Proj(ref tm, label_start, ref label) => {
                raw::RcTerm::from(raw::Term::Proj(
                    span,
                    tm.desugar(env),
                    ByteSpan::from_offset(label_start, ByteOffset::from_str(label)),
                    Label(label.clone()),
                ))
            },
            concrete::Term::Error(_) => unimplemented!("error recovery"),
        }
    }
}
