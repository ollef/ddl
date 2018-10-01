//! The semantics of the language
//!
//! Here we define the rules of normalization, type checking, and type inference.
//!
//! For more information, check out the theory appendix of the DDL book.

use codespan::ByteSpan;
use moniker::{Binder, BoundTerm, Embed, FreeVar, Nest, Scope, Var};
use num_traits::ToPrimitive;

use syntax::core::{
    Definition, Head, Item, Literal, Module, Pattern, RcPattern, RcTerm, RcType, RcValue, Term,
    Type, Value,
};
use syntax::raw;
use syntax::translation::Resugar;
use syntax::{FloatFormat, IntFormat, Label, Level};

mod env;
mod errors;
mod normalize;
pub mod parser;
#[cfg(test)]
mod tests;

pub use self::env::{DeclarationEnv, DefinitionEnv, Extern, GlobalEnv, Globals, TcEnv};
pub use self::errors::{InternalError, TypeError};
pub use self::normalize::{match_value, nf_term};

/// Type check and elaborate a module
pub fn check_module<Env>(env: &Env, raw_module: &raw::Module) -> Result<Module, TypeError>
where
    Env: DeclarationEnv + DefinitionEnv,
{
    use im::HashMap;

    #[derive(Clone)]
    pub enum ForwardDecl {
        Pending(ByteSpan, RcTerm),
        Defined(ByteSpan),
    }

    // Declarations that may be waiting to be defined
    let mut forward_declarations = HashMap::new();
    let mut env = env.clone();
    // The elaborated items, pre-allocated to improve performance
    let mut items = Vec::with_capacity(raw_module.items.len());
    let name = raw_module.name.clone();

    // Iterate through the items in the module, checking each in turn
    for raw_item in &raw_module.items {
        match *raw_item {
            raw::Item::Declaration {
                label_span,
                ref label,
                ref binder,
                term: ref raw_term,
            } => {
                // Ensure that this declaration has not already been seen
                match forward_declarations.get(binder) {
                    // There's already a definition associated with this name -
                    // we can't add a new declaration for it!
                    Some(&ForwardDecl::Defined(definition_span)) => {
                        return Err(TypeError::DeclarationFollowedDefinition {
                            definition_span,
                            declaration_span: label_span,
                            binder: binder.clone(),
                        });
                    },
                    // There's a declaration  for this name already pending - we
                    // can't add a new one!
                    Some(&ForwardDecl::Pending(original_span, _)) => {
                        return Err(TypeError::DuplicateDeclarations {
                            original_span,
                            duplicate_span: label_span,
                            binder: binder.clone(),
                        });
                    },
                    // No previous declaration for this name was seen, so we can
                    // go-ahead and type check, elaborate, and then add it to
                    // the context
                    None => {},
                }

                // Ensure that the declaration's type annotation is actually a type
                let (term, _) = infer_universe(&env, raw_term)?;
                // Remember the declaration for when we get to a subsequent definition
                let declaration = ForwardDecl::Pending(label_span, term.clone());
                forward_declarations.insert(binder.clone(), declaration);
                // Add the declaration to the elaborated items
                items.push(Item::Declaration {
                    label: label.clone(),
                    binder: binder.clone(),
                    term,
                });
            },

            raw::Item::Definition {
                label_span,
                ref label,
                ref binder,
                ref definition,
            } => {
                let (definition, ty) = match (forward_declarations.get(binder), definition) {
                    // This declaration was already given a definition, so this
                    // is an error!
                    //
                    // NOTE: Some languages (eg. Haskell, Agda, Idris, and
                    // Erlang) turn duplicate definitions into match matches.
                    // Languages like Elm don't. What should we do here?
                    (Some(&ForwardDecl::Defined(original_span)), _) => {
                        return Err(TypeError::DuplicateDefinitions {
                            original_span,
                            duplicate_span: label_span,
                            binder: binder.clone(),
                        });
                    },
                    // We found a prior declaration, so we'll use it as a basis
                    // for checking the definition
                    (
                        Some(ForwardDecl::Pending(_, ref ty)),
                        &raw::Definition::Alias(ref raw_term),
                    ) => {
                        let ty = nf_term(&env, ty)?;
                        (Definition::Alias(check_term(&env, &raw_term, &ty)?), ty)
                    },
                    (Some(ForwardDecl::Pending(_, _)), &raw::Definition::StructType(_, _)) => {
                        unimplemented!("forward struct definitions");
                    },
                    // No prior declaration was found, so try to infer the type
                    // from the given definition alone
                    (None, &raw::Definition::Alias(ref raw_term)) => {
                        let (term, ty) = infer_term(&env, &raw_term)?;
                        (Definition::Alias(term), ty)
                    },
                    (None, &raw::Definition::StructType(_, ref raw_scope)) => {
                        use std::cmp;

                        let mut env = env.clone();
                        let mut max_level = Level(0);

                        let (raw_params, raw_fields_scope) = raw_scope.clone().unbind();
                        let (raw_fields, ()) = raw_fields_scope.unbind();
                        let raw_params = raw_params.unnest();

                        let mut struct_params = Vec::with_capacity(raw_params.len());
                        let mut pi_params = Vec::with_capacity(raw_params.len());

                        for (Binder(free_var), Embed(raw_ann)) in raw_params {
                            let (ann, _) = infer_universe(&env, &raw_ann)?;
                            let nf_ann = nf_term(&env, &ann)?;

                            env.insert_declaration(free_var.clone(), nf_ann.clone());

                            struct_params.push((Binder(free_var.clone()), Embed(ann)));
                            pi_params.push((Binder(free_var), Embed(nf_ann)));
                        }

                        // FIXME: Check that struct is well-formed?
                        let fields = raw_fields
                            .unnest()
                            .into_iter()
                            .map(|(label, Binder(free_var), Embed(raw_ann))| {
                                let (ann, ann_level) = infer_universe(&env, &raw_ann)?;
                                let nf_ann = nf_term(&env, &ann)?;

                                max_level = cmp::max(max_level, ann_level);
                                env.insert_declaration(free_var.clone(), nf_ann);

                                Ok((label, Binder(free_var), Embed(ann)))
                            }).collect::<Result<_, TypeError>>()?;

                        let struct_ty = Definition::StructType(Scope::new(
                            Nest::new(struct_params),
                            Scope::new(Nest::new(fields), ()),
                        ));

                        let ty = pi_params
                            .into_iter()
                            .rev()
                            .fold(RcValue::from(Value::Universe(max_level)), |acc, param| {
                                RcValue::from(Value::Pi(Scope::new(param, acc)))
                            });

                        (struct_ty, ty)
                    },
                };

                // We must not remove this from the list of pending
                // declarations, lest we encounter another declaration or
                // definition of the same name later on!
                forward_declarations.insert(binder.clone(), ForwardDecl::Defined(label_span));
                // Add the declaration and definition to the environment,
                // allowing them to be used in later type checking
                env.insert_declaration(binder.0.clone(), ty);
                env.insert_definition(binder.0.clone(), definition.clone());
                // Add the definition to the elaborated items
                items.push(Item::Definition {
                    label: label.clone(),
                    binder: binder.clone(),
                    definition,
                });
            },
        }
    }

    Ok(Module { name, items })
}

/// Check that `ty1` is a subtype of `ty2`
pub fn is_subtype<Env>(env: &Env, ty1: &RcType, ty2: &RcType) -> bool
where
    Env: GlobalEnv,
{
    match (&*ty1.inner, &*ty2.inner) {
        (&Value::IntType(ref min1, ref max1), &Value::IntType(ref min2, ref max2)) => {
            let in_min_bound = match (min1, min2) {
                (None, None) => true,     // -∞ <= -∞
                (Some(_), None) => true,  //  n <= -∞
                (None, Some(_)) => false, // -∞ <=  n
                (Some(ref min1), Some(ref min2)) => match (&*min1.inner, &*min2.inner) {
                    (
                        Value::Literal(Literal::Int(ref min1, IntFormat::Dec)),
                        Value::Literal(Literal::Int(ref min2, IntFormat::Dec)),
                    ) => min1 >= min2,
                    _ => Value::term_eq(min1, min2), // Fallback to alpha-equality
                },
            };

            let in_max_bound = match (max1, max2) {
                (None, None) => true,     // +∞ <= +∞
                (Some(_), None) => true,  //  n <= +∞
                (None, Some(_)) => false, // +∞ <=  n
                (Some(ref max1), Some(ref max2)) => match (&*max1.inner, &*max2.inner) {
                    (
                        Value::Literal(Literal::Int(ref max1, IntFormat::Dec)),
                        Value::Literal(Literal::Int(ref max2, IntFormat::Dec)),
                    ) => max1 <= max2,
                    _ => Value::term_eq(max1, max2), // Fallback to alpha-equality
                },
            };

            in_min_bound && in_max_bound
        },

        _ if ty1 == env.u16le() => is_subtype(env, env.u16(), ty2),
        _ if ty1 == env.u32le() => is_subtype(env, env.u32(), ty2),
        _ if ty1 == env.u64le() => is_subtype(env, env.u64(), ty2),
        _ if ty1 == env.s16le() => is_subtype(env, env.s16(), ty2),
        _ if ty1 == env.s32le() => is_subtype(env, env.s32(), ty2),
        _ if ty1 == env.s64le() => is_subtype(env, env.s64(), ty2),
        _ if ty1 == env.f32le() && ty2 == env.f32() => true,
        _ if ty1 == env.f64le() && ty2 == env.f64() => true,
        _ if ty1 == env.u16be() => is_subtype(env, env.u16(), ty2),
        _ if ty1 == env.u32be() => is_subtype(env, env.u32(), ty2),
        _ if ty1 == env.u64be() => is_subtype(env, env.u64(), ty2),
        _ if ty1 == env.s16be() => is_subtype(env, env.s16(), ty2),
        _ if ty1 == env.s32be() => is_subtype(env, env.s32(), ty2),
        _ if ty1 == env.s64be() => is_subtype(env, env.s64(), ty2),
        _ if ty1 == env.f32be() && ty2 == env.f32() => true,
        _ if ty1 == env.f64be() && ty2 == env.f64() => true,

        // Fallback to alpha-equality
        _ => Type::term_eq(ty1, ty2),
    }
}

/// Ensures that the given term is a universe, returning the level of that
/// universe and its elaborated form.
fn infer_universe<Env>(env: &Env, raw_term: &raw::RcTerm) -> Result<(RcTerm, Level), TypeError>
where
    Env: DeclarationEnv + DefinitionEnv,
{
    let (term, ty) = infer_term(env, raw_term)?;
    match *ty {
        Value::Universe(level) => Ok((term, level)),
        _ => Err(TypeError::ExpectedUniverse {
            span: raw_term.span(),
            found: Box::new(ty.resugar(env.resugar_env())),
        }),
    }
}

/// Checks that a literal is compatible with the given type, returning the
/// elaborated literal if successful
fn check_literal<Env, T>(
    env: &Env,
    raw_literal: &raw::Literal,
    expected_ty: &RcType,
    wrap_literal: impl Fn(Literal) -> T,
    wrap_array: impl Fn(Vec<T>) -> T,
) -> Result<T, TypeError>
where
    Env: GlobalEnv,
{
    match *raw_literal {
        raw::Literal::String(_, ref val) if env.string() == expected_ty => {
            return Ok(wrap_literal(Literal::String(val.clone())));
        },
        raw::Literal::String(_, ref val) => match env.array(expected_ty) {
            Some((len, elem_ty)) if *len == val.len().into() && elem_ty == env.u8() => {
                let elems = val
                    .bytes()
                    .map(|elem| wrap_literal(Literal::Int(elem.into(), IntFormat::Dec)))
                    .collect();

                return Ok(wrap_array(elems));
            },
            Some((len, _)) => {
                return Err(TypeError::ArrayLengthMismatch {
                    span: raw_literal.span(),
                    found_len: val.len(),
                    expected_len: len.clone(),
                });
            },
            None => {},
        },
        raw::Literal::Char(_, val) if env.char() == expected_ty => {
            return Ok(wrap_literal(Literal::Char(val)));
        },

        // FIXME: overflow?
        raw::Literal::Int(_, ref val, _) if env.f32() == expected_ty => {
            return Ok(wrap_literal(Literal::F32(
                val.to_f32().unwrap(),
                FloatFormat::Dec,
            )));
        },
        raw::Literal::Int(_, ref val, _) if env.f64() == expected_ty => {
            return Ok(wrap_literal(Literal::F64(
                val.to_f64().unwrap(),
                FloatFormat::Dec,
            )));
        },
        raw::Literal::Float(_, val, format) if env.f32() == expected_ty => {
            return Ok(wrap_literal(Literal::F32(val as f32, format)));
        },
        raw::Literal::Float(_, val, format) if env.f64() == expected_ty => {
            return Ok(wrap_literal(Literal::F64(val, format)));
        },

        _ => {},
    }

    let (term, inferred_ty) = infer_literal(env, raw_literal, wrap_literal)?;
    if is_subtype(env, &inferred_ty, expected_ty) {
        Ok(term)
    } else {
        Err(TypeError::LiteralMismatch {
            literal_span: raw_literal.span(),
            found: raw_literal.clone(),
            expected: Box::new(expected_ty.resugar(env.resugar_env())),
        })
    }
}

/// Synthesize the type of a literal, returning the elaborated literal and the
/// inferred type if successful
fn infer_literal<Env, T>(
    env: &Env,
    raw_literal: &raw::Literal,
    wrap_literal: impl Fn(Literal) -> T,
) -> Result<(T, RcType), TypeError>
where
    Env: GlobalEnv,
{
    match *raw_literal {
        raw::Literal::String(span, _) => Err(TypeError::AmbiguousStringLiteral { span }),
        raw::Literal::Char(_, value) => {
            Ok((wrap_literal(Literal::Char(value)), env.char().clone()))
        },
        raw::Literal::Int(_, ref value, format) => {
            Ok((wrap_literal(Literal::Int(value.clone(), format)), {
                let value = RcValue::from(Value::Literal(Literal::Int(value.clone(), format)));
                RcValue::from(Value::IntType(Some(value.clone()), Some(value)))
            }))
        },
        raw::Literal::Float(span, _, _) => Err(TypeError::AmbiguousFloatLiteral { span }),
    }
}

/// Checks that a pattern is compatible with the given type, returning the
/// elaborated pattern and a vector of the declarations it introduced if successful
pub fn check_pattern<Env>(
    env: &Env,
    raw_pattern: &raw::RcPattern,
    expected_ty: &RcType,
) -> Result<(RcPattern, Vec<(FreeVar<String>, RcType)>), TypeError>
where
    Env: DeclarationEnv + DefinitionEnv,
{
    match (&*raw_pattern.inner, &*expected_ty.inner) {
        (&raw::Pattern::Binder(_, Binder(ref free_var)), _) => {
            return Ok((
                RcPattern::from(Pattern::Binder(Binder(free_var.clone()))),
                vec![(free_var.clone(), expected_ty.clone())],
            ));
        },
        (&raw::Pattern::Literal(ref raw_literal), _) => {
            return Ok((
                check_literal(
                    env,
                    raw_literal,
                    expected_ty,
                    |lit| RcPattern::from(Pattern::Literal(lit)),
                    |elems| RcPattern::from(Pattern::Array(elems)),
                )?,
                vec![],
            ));
        },
        _ => {},
    }

    let (pattern, inferred_ty, declarations) = infer_pattern(env, raw_pattern)?;
    if Type::term_eq(&inferred_ty, expected_ty) {
        Ok((pattern, declarations))
    } else {
        Err(TypeError::Mismatch {
            span: raw_pattern.span(),
            found: Box::new(inferred_ty.resugar(env.resugar_env())),
            expected: Box::new(expected_ty.resugar(env.resugar_env())),
        })
    }
}

/// Synthesize the type of a pattern, returning the elaborated pattern, the
/// inferred type, and a vector of the declarations it introduced if successful
pub fn infer_pattern<Env>(
    env: &Env,
    raw_pattern: &raw::RcPattern,
) -> Result<(RcPattern, RcType, Vec<(FreeVar<String>, RcType)>), TypeError>
where
    Env: DeclarationEnv + DefinitionEnv,
{
    match *raw_pattern.inner {
        raw::Pattern::Ann(ref raw_pattern, Embed(ref raw_ty)) => {
            let (ty, _) = infer_universe(env, raw_ty)?;
            let value_ty = nf_term(env, &ty)?;
            let (pattern, declarations) = check_pattern(env, raw_pattern, &value_ty)?;

            Ok((
                RcPattern::from(Pattern::Ann(pattern, Embed(ty))),
                value_ty,
                declarations,
            ))
        },
        raw::Pattern::Binder(span, ref binder) => Err(TypeError::BinderNeedsAnnotation {
            span,
            binder: binder.clone(),
        }),
        raw::Pattern::Var(span, Embed(ref var)) => match *var {
            Var::Free(ref free_var) => match env.get_declaration(free_var) {
                Some(ty) => Ok((
                    RcPattern::from(Pattern::Var(Embed(var.clone()))),
                    ty.clone(),
                    vec![],
                )),
                None => Err(TypeError::UndefinedName {
                    span,
                    free_var: free_var.clone(),
                }),
            },

            // We should always be substituting bound variables with fresh
            // variables when entering scopes using `unbind`, so if we've
            // encountered one here this is definitely a bug!
            Var::Bound(_) => Err(InternalError::UnexpectedBoundVar {
                span: Some(raw_pattern.span()),
                var: var.clone(),
            }.into()),
        },
        raw::Pattern::Literal(ref literal) => {
            let (pattern, ty) =
                infer_literal(env, literal, |lit| RcPattern::from(Pattern::Literal(lit)))?;
            Ok((pattern, ty, vec![]))
        },
    }
}

pub fn expect_struct<Env>(
    env: &Env,
    ty: &RcType,
) -> Option<(
    Vec<(Label, Binder<String>, Embed<RcTerm>)>,
    Vec<(FreeVar<String>, RcTerm)>,
)>
where
    Env: DeclarationEnv + DefinitionEnv,
{
    match ty.inner.head_app()? {
        (Head::Var(Var::Free(ref free_var)), spine) => {
            match *env.get_definition(free_var)? {
                Definition::Alias(_) => None, // FIXME: follow alias?
                Definition::StructType(ref scope) => {
                    let (params, fields_scope) = scope.clone().unbind();
                    let (fields, ()) = fields_scope.unbind();
                    let params = params.unnest();
                    let fields = fields.unnest();

                    if params.len() != spine.len() {
                        unimplemented!();
                    }

                    // FIXME: check that the args match the spine

                    let mut mappings = Vec::with_capacity(params.len() + fields.len());

                    for (&(Binder(ref free_var), _), arg) in
                        Iterator::zip(params.iter(), spine.iter())
                    {
                        let arg = arg.substs(&mappings);
                        mappings.push((free_var.clone(), arg));
                    }

                    Some((fields, mappings))
                },
            }
        },
        _ => None,
    }
}

/// Checks that a term is compatible with the given type, returning the
/// elaborated term if successful
pub fn check_term<Env>(
    env: &Env,
    raw_term: &raw::RcTerm,
    expected_ty: &RcType,
) -> Result<RcTerm, TypeError>
where
    Env: DeclarationEnv + DefinitionEnv,
{
    match (&*raw_term.inner, &*expected_ty.inner) {
        (&raw::Term::Literal(ref raw_literal), _) => {
            return check_literal(
                env,
                raw_literal,
                expected_ty,
                |lit| RcTerm::from(Term::Literal(lit)),
                |elems| RcTerm::from(Term::Array(elems)),
            );
        },

        (&raw::Term::Extern(_, name_span, ref name), _) => match env.get_extern_definition(name) {
            Some(_) => return Ok(RcTerm::from(Term::Extern(name.clone()))),
            None => {
                return Err(TypeError::UndefinedExternName {
                    span: name_span,
                    name: name.clone(),
                });
            },
        },

        // C-LAM
        (&raw::Term::Lam(_, ref lam_scope), &Value::Pi(ref pi_scope)) => {
            let ((lam_name, Embed(lam_ann)), lam_body, (Binder(pi_name), Embed(pi_ann)), pi_body) =
                Scope::unbind2(lam_scope.clone(), pi_scope.clone());

            // Elaborate the hole, if it exists
            if let raw::Term::Hole(_) = *lam_ann.inner {
                let lam_ann = RcTerm::from(Term::from(&*pi_ann));
                let lam_body = {
                    let mut body_env = env.clone();
                    body_env.insert_declaration(pi_name, pi_ann);
                    check_term(&body_env, &lam_body, &pi_body)?
                };
                let lam_scope = Scope::new((lam_name, Embed(lam_ann)), lam_body);

                return Ok(RcTerm::from(Term::Lam(lam_scope)));
            }

            // TODO: We might want to optimise for this match, rather than
            // falling through to `infer` and unbinding again at I-LAM
        },
        (&raw::Term::Lam(_, _), _) => {
            return Err(TypeError::UnexpectedFunction {
                span: raw_term.span(),
                expected: Box::new(expected_ty.resugar(env.resugar_env())),
            });
        },

        // C-STRUCT
        (&raw::Term::Struct(span, ref raw_fields), _) => {
            if let Some((ty_fields, mut mappings)) = expect_struct(env, expected_ty) {
                if raw_fields.len() != ty_fields.len() {
                    return Err(TypeError::StructSizeMismatch {
                        span,
                        found_size: raw_fields.len() as u64,
                        expected_size: ty_fields.len() as u64,
                    });
                }

                // FIXME: Check that struct is well-formed?
                let fields = <_>::zip(raw_fields.into_iter(), ty_fields.into_iter())
                    .map(|(field, ty_field)| {
                        let &(ref label, ref raw_expr) = field;
                        let (ty_label, Binder(free_var), Embed(ann)) = ty_field;

                        if *label == ty_label {
                            let ann = nf_term(env, &ann.substs(&mappings))?;
                            let expr = check_term(env, raw_expr, &ann)?;
                            mappings.push((free_var, expr.clone()));
                            Ok((label.clone(), expr))
                        } else {
                            Err(TypeError::LabelMismatch {
                                span,
                                found: label.clone(),
                                expected: ty_label,
                            })
                        }
                    }).collect::<Result<_, _>>()?;

                return Ok(RcTerm::from(Term::Struct(fields)));
            }
        },

        (&raw::Term::Match(_, ref raw_head, ref raw_clauses), _) => {
            let (head, head_ty) = infer_term(env, raw_head)?;

            // TODO: ensure that patterns are exhaustive
            let clauses = raw_clauses
                .iter()
                .map(|raw_clause| {
                    let (raw_pattern, raw_body) = raw_clause.clone().unbind();
                    let (pattern, declarations) = check_pattern(env, &raw_pattern, &head_ty)?;

                    let mut body_env = env.clone();
                    body_env.extend_declarations(declarations);
                    let body = check_term(&body_env, &raw_body, expected_ty)?;

                    Ok(Scope::new(pattern, body))
                }).collect::<Result<_, TypeError>>()?;

            return Ok(RcTerm::from(Term::Match(head, clauses)));
        },

        (&raw::Term::Array(span, ref elems), _) => {
            return match env.array(expected_ty) {
                Some((len, elem_ty)) if *len == elems.len().into() => {
                    let elems = elems
                        .iter()
                        .map(|elem| check_term(env, elem, elem_ty))
                        .collect::<Result<_, _>>()?;

                    Ok(RcTerm::from(Term::Array(elems)))
                },
                Some((len, _)) => Err(TypeError::ArrayLengthMismatch {
                    span,
                    found_len: elems.len(),
                    expected_len: len.clone(),
                }),
                None => Err(TypeError::Internal(InternalError::Unimplemented {
                    span: Some(span),
                    message: "unexpected arguments to `Array`".to_owned(),
                })),
            }
        },

        (&raw::Term::Hole(span), _) => {
            let expected = Some(Box::new(expected_ty.resugar(env.resugar_env())));
            return Err(TypeError::UnableToElaborateHole { span, expected });
        },

        _ => {},
    }

    // C-CONV
    let (term, inferred_ty) = infer_term(env, raw_term)?;
    if is_subtype(env, &inferred_ty, expected_ty) {
        Ok(term)
    } else {
        Err(TypeError::Mismatch {
            span: raw_term.span(),
            found: Box::new(inferred_ty.resugar(env.resugar_env())),
            expected: Box::new(expected_ty.resugar(env.resugar_env())),
        })
    }
}

/// Synthesize the type of a term, returning the elaborated term and the
/// inferred type if successful
pub fn infer_term<Env>(env: &Env, raw_term: &raw::RcTerm) -> Result<(RcTerm, RcType), TypeError>
where
    Env: DeclarationEnv + DefinitionEnv,
{
    use std::cmp;

    match *raw_term.inner {
        //  I-ANN
        raw::Term::Ann(ref raw_expr, ref raw_ty) => {
            let (ty, _) = infer_universe(env, raw_ty)?;
            let value_ty = nf_term(env, &ty)?;
            let expr = check_term(env, raw_expr, &value_ty)?;

            Ok((RcTerm::from(Term::Ann(expr, ty)), value_ty))
        },

        // I-TYPE
        raw::Term::Universe(_, level) => Ok((
            RcTerm::from(Term::Universe(level)),
            RcValue::from(Value::Universe(level.succ())),
        )),

        raw::Term::Hole(span) => {
            let expected = None;
            Err(TypeError::UnableToElaborateHole { span, expected })
        },

        raw::Term::IntType(_, ref min, ref max) => {
            let min = match *min {
                None => None,
                Some(ref min) => {
                    let any_int = RcValue::from(Value::IntType(None, None));
                    Some(check_term(env, min, &any_int)?)
                },
            };

            let max = match *max {
                None => None,
                Some(ref max) => {
                    let any_int = RcValue::from(Value::IntType(None, None));
                    Some(check_term(env, max, &any_int)?)
                },
            };

            Ok((
                RcTerm::from(Term::IntType(min, max)),
                RcValue::from(Value::Universe(Level(0))),
            ))
        },

        raw::Term::Literal(ref raw_literal) => {
            infer_literal(env, raw_literal, |lit| RcTerm::from(Term::Literal(lit)))
        },

        // I-VAR
        raw::Term::Var(span, ref var) => match *var {
            Var::Free(ref free_var) => match env.get_declaration(free_var) {
                Some(ty) => Ok((RcTerm::from(Term::Var(var.clone())), ty.clone())),
                None => Err(TypeError::UndefinedName {
                    span,
                    free_var: free_var.clone(),
                }),
            },

            // We should always be substituting bound variables with fresh
            // variables when entering scopes using `unbind`, so if we've
            // encountered one here this is definitely a bug!
            Var::Bound(_) => Err(InternalError::UnexpectedBoundVar {
                span: Some(raw_term.span()),
                var: var.clone(),
            }.into()),
        },

        raw::Term::Extern(span, name_span, ref name) => match env.get_extern_definition(name) {
            Some(_) => Err(TypeError::AmbiguousExtern { span }),
            None => Err(TypeError::UndefinedExternName {
                span: name_span,
                name: name.clone(),
            }),
        },

        // I-PI
        raw::Term::Pi(_, ref raw_scope) => {
            let ((Binder(free_var), Embed(raw_ann)), raw_body) = raw_scope.clone().unbind();

            let (ann, ann_level) = infer_universe(env, &raw_ann)?;
            let (body, body_level) = {
                let ann = nf_term(env, &ann)?;
                let mut body_env = env.clone();
                body_env.insert_declaration(free_var.clone(), ann);
                infer_universe(&body_env, &raw_body)?
            };

            Ok((
                RcTerm::from(Term::Pi(Scope::new((Binder(free_var), Embed(ann)), body))),
                RcValue::from(Value::Universe(cmp::max(ann_level, body_level))),
            ))
        },

        // I-LAM
        raw::Term::Lam(_, ref raw_scope) => {
            let ((Binder(free_var), Embed(raw_ann)), raw_body) = raw_scope.clone().unbind();

            // Check for holes before entering to ensure we get a nice error
            if let raw::Term::Hole(_) = *raw_ann {
                return Err(TypeError::FunctionParamNeedsAnnotation {
                    param_span: ByteSpan::default(), // TODO: param.span(),
                    var_span: None,
                    name: free_var.clone(),
                });
            }

            let (lam_ann, _) = infer_universe(env, &raw_ann)?;
            let pi_ann = nf_term(env, &lam_ann)?;
            let (lam_body, pi_body) = {
                let mut body_env = env.clone();
                body_env.insert_declaration(free_var.clone(), pi_ann.clone());
                infer_term(&body_env, &raw_body)?
            };

            let lam_param = (Binder(free_var.clone()), Embed(lam_ann));
            let pi_param = (Binder(free_var.clone()), Embed(pi_ann));

            Ok((
                RcTerm::from(Term::Lam(Scope::new(lam_param, lam_body))),
                RcValue::from(Value::Pi(Scope::new(pi_param, pi_body))),
            ))
        },

        // I-APP
        raw::Term::App(ref raw_head, ref raw_arg) => {
            let (head, head_ty) = infer_term(env, raw_head)?;

            match *head_ty {
                Value::Pi(ref scope) => {
                    let ((Binder(free_var), Embed(ann)), body) = scope.clone().unbind();

                    let arg = check_term(env, raw_arg, &ann)?;
                    let body = nf_term(env, &body.substs(&[(free_var, arg.clone())]))?;

                    Ok((RcTerm::from(Term::App(head, arg)), body))
                },
                _ => Err(TypeError::ArgAppliedToNonFunction {
                    fn_span: raw_head.span(),
                    arg_span: raw_arg.span(),
                    found: Box::new(head_ty.resugar(env.resugar_env())),
                }),
            }
        },

        raw::Term::Unop(_, op, ref raw_operand) => {
            use syntax::Unop;

            let unnop = |extern_name: &str, operand| {
                RcTerm::from(Term::App(
                    RcTerm::from(Term::Extern(extern_name.to_owned())),
                    operand,
                ))
            };

            let (operand, operand_ty) = infer_term(env, raw_operand)?;

            if operand_ty == *env.f32() {
                let (extern_name, ty) = match op {
                    Unop::Neg => ("f32-neg", env.f32().clone()),
                    _ => {
                        return Err(InternalError::Unimplemented {
                            span: Some(raw_term.span()),
                            message: "binary operator error".to_owned(),
                        }.into())
                    },
                };

                Ok((unnop(extern_name, operand), ty))
            } else if operand_ty == *env.f64() {
                let (extern_name, ty) = match op {
                    Unop::Neg => ("f64-neg", env.f64().clone()),
                    _ => {
                        return Err(InternalError::Unimplemented {
                            span: Some(raw_term.span()),
                            message: "binary operator error".to_owned(),
                        }.into())
                    },
                };

                Ok((unnop(extern_name, operand), ty))
            } else if operand_ty == *env.bool() {
                let (extern_name, ty) = match op {
                    Unop::Not => ("bool-not", env.bool().clone()),
                    _ => {
                        return Err(InternalError::Unimplemented {
                            span: Some(raw_term.span()),
                            message: "binary operator error".to_owned(),
                        }.into())
                    },
                };

                Ok((unnop(extern_name, operand), ty))
            } else {
                Err(InternalError::Unimplemented {
                    span: Some(raw_term.span()),
                    message: "unary operators".to_owned(),
                }.into())
            }
        },

        raw::Term::Binop(ref raw_lhs, op, ref raw_rhs) => {
            use syntax::Binop;

            let binop = |extern_name: &str, lhs, rhs| {
                RcTerm::from(Term::App(
                    RcTerm::from(Term::App(
                        RcTerm::from(Term::Extern(extern_name.to_owned())),
                        lhs,
                    )),
                    rhs,
                ))
            };

            let (lhs, lhs_ty) = infer_term(env, raw_lhs)?;
            let (rhs, rhs_ty) = infer_term(env, raw_rhs)?;

            if lhs_ty == *env.bool() && rhs_ty == *env.bool() {
                let (extern_name, ty) = match op {
                    Binop::Or => ("bool-or", env.bool().clone()),
                    Binop::And => ("bool-and", env.bool().clone()),
                    Binop::Eq => ("bool-eq", env.bool().clone()),
                    Binop::Ne => ("bool-ne", env.bool().clone()),
                    _ => {
                        return Err(InternalError::Unimplemented {
                            span: Some(raw_term.span()),
                            message: "binary operator error".to_owned(),
                        }.into())
                    },
                };

                Ok((binop(extern_name, lhs, rhs), ty))
            } else if lhs_ty == *env.f32() && rhs_ty == *env.f32() {
                let (extern_name, ty) = match op {
                    Binop::Eq => ("f32-eq", env.bool().clone()),
                    Binop::Ne => ("f32-ne", env.bool().clone()),
                    Binop::Le => ("f32-le", env.bool().clone()),
                    Binop::Lt => ("f32-lt", env.bool().clone()),
                    Binop::Gt => ("f32-gt", env.bool().clone()),
                    Binop::Ge => ("f32-ge", env.bool().clone()),
                    Binop::Add => ("f32-add", env.f32().clone()),
                    Binop::Sub => ("f32-sub", env.f32().clone()),
                    Binop::Mul => ("f32-mul", env.f32().clone()),
                    Binop::Div => ("f32-div", env.f32().clone()),
                    _ => {
                        return Err(InternalError::Unimplemented {
                            span: Some(raw_term.span()),
                            message: "binary operator error".to_owned(),
                        }.into())
                    },
                };

                Ok((binop(extern_name, lhs, rhs), ty))
            } else if lhs_ty == *env.f64() && rhs_ty == *env.f64() {
                let (extern_name, ty) = match op {
                    Binop::Eq => ("f64-eq", env.bool().clone()),
                    Binop::Ne => ("f64-ne", env.bool().clone()),
                    Binop::Le => ("f64-le", env.bool().clone()),
                    Binop::Lt => ("f64-lt", env.bool().clone()),
                    Binop::Gt => ("f64-gt", env.bool().clone()),
                    Binop::Ge => ("f64-ge", env.bool().clone()),
                    Binop::Add => ("f64-add", env.f64().clone()),
                    Binop::Sub => ("f64-sub", env.f64().clone()),
                    Binop::Mul => ("f64-mul", env.f64().clone()),
                    Binop::Div => ("f64-div", env.f64().clone()),
                    _ => {
                        return Err(InternalError::Unimplemented {
                            span: Some(raw_term.span()),
                            message: "binary operator error".to_owned(),
                        }.into())
                    },
                };

                Ok((binop(extern_name, lhs, rhs), ty))
            } else {
                Err(InternalError::Unimplemented {
                    span: Some(raw_term.span()),
                    message: "binary operators".to_owned(),
                }.into())
            }
        },

        raw::Term::Struct(span, _) => Err(TypeError::AmbiguousStruct { span }),

        // I-PROJ
        raw::Term::Proj(_, ref expr, label_span, ref label) => {
            let (expr, ty) = infer_term(env, expr)?;

            if let Some((ty_fields, mut mappings)) = expect_struct(env, &ty) {
                for (current_label, Binder(free_var), Embed(current_ann)) in ty_fields {
                    if current_label == *label {
                        return Ok((
                            RcTerm::from(Term::Proj(expr, current_label)),
                            nf_term(env, &current_ann.substs(&mappings))?,
                        ));
                    } else {
                        mappings.push((
                            free_var,
                            RcTerm::from(Term::Proj(expr.clone(), current_label)),
                        ));
                    }
                }
            }

            Err(TypeError::NoFieldInType {
                label_span,
                expected_label: label.clone(),
                found: Box::new(ty.resugar(env.resugar_env())),
            })
        },

        // I-CASE
        raw::Term::Match(span, ref raw_head, ref raw_clauses) => {
            let (head, head_ty) = infer_term(env, raw_head)?;
            let mut ty = None;

            // TODO: ensure that patterns are exhaustive
            let clauses = raw_clauses
                .iter()
                .map(|raw_clause| {
                    let (raw_pattern, raw_body) = raw_clause.clone().unbind();
                    let (pattern, declarations) = check_pattern(env, &raw_pattern, &head_ty)?;

                    let (body, body_ty) = {
                        let mut body_env = env.clone();
                        body_env.extend_declarations(declarations);
                        infer_term(&body_env, &raw_body)?
                    };

                    match ty {
                        None => ty = Some(body_ty),
                        Some(ref ty) if RcValue::term_eq(&body_ty, ty) => {},
                        Some(ref ty) => {
                            return Err(TypeError::Mismatch {
                                span: raw_body.span(),
                                found: Box::new(body_ty.resugar(env.resugar_env())),
                                expected: Box::new(ty.resugar(env.resugar_env())),
                            });
                        },
                    }

                    Ok(Scope::new(pattern, body))
                }).collect::<Result<_, TypeError>>()?;

            match ty {
                Some(ty) => Ok((RcTerm::from(Term::Match(head, clauses)), ty)),
                None => Err(TypeError::AmbiguousEmptyMatch { span }),
            }
        },

        raw::Term::Array(span, _) => Err(TypeError::AmbiguousArrayLiteral { span }),
    }
}
