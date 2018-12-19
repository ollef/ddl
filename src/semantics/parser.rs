use im;
use moniker::{Binder, Embed, FreeVar, Scope, Var};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::io;

use crate::semantics::{Context, Definition, InternalError};
use crate::syntax::core;
use crate::syntax::Label;

#[derive(Debug)]
pub enum ParseError {
    InvalidType(core::RcType),
    InvalidValue(core::RcValue),
    Internal(InternalError),
    BadArrayIndex(core::RcValue),
    OffsetPointedToDifferentTypes(core::RcType, core::RcType),
    MismatchedIntersectionSize(u64, u64),
    ParametrizedStructType,
    ParametrizedUnionType,
    FailedPredicate(core::RcValue),
    NoVariantMatched,
    MissingRoot(Label),
    Io(io::Error),
}

impl From<InternalError> for ParseError {
    fn from(src: InternalError) -> ParseError {
        ParseError::Internal(src)
    }
}

impl From<io::Error> for ParseError {
    fn from(src: io::Error) -> ParseError {
        ParseError::Io(src)
    }
}

/// A stack of references that we still need to parse
type PendingOffsets = Vec<(u64, core::RcType)>;

/// Values returned as a result of parsing a binary format
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Pos(u64),
    Int(BigInt),
    F32(f32),
    F64(f64),
    Bool(bool),
    String(String),
    Struct(Vec<(Label, Value)>),
    Array(Vec<Value>),
}

impl Value {
    pub fn int(value: impl Into<BigInt>) -> Value {
        Value::Int(value.into())
    }

    pub fn try_from_core_value(term: &core::RcValue) -> Result<Value, ParseError> {
        match *term.inner {
            core::Value::Literal(core::Literal::Int(ref value, _)) => Ok(Value::Int(value.clone())),
            core::Value::Literal(core::Literal::F32(value, _)) => Ok(Value::F32(value)),
            core::Value::Literal(core::Literal::F64(value, _)) => Ok(Value::F64(value)),
            core::Value::Literal(core::Literal::Bool(value)) => Ok(Value::Bool(value)),
            core::Value::Literal(core::Literal::String(ref value)) => {
                Ok(Value::String(value.clone()))
            },
            core::Value::Struct(ref fields) => {
                let fields = fields
                    .iter()
                    .map(|&(ref label, ref value)| {
                        Ok((label.clone(), Value::try_from_core_value(value)?))
                    })
                    .collect::<Result<_, ParseError>>()?;

                Ok(Value::Struct(fields))
            },
            core::Value::Array(ref elems) => {
                let elems = elems
                    .iter()
                    .map(|elem| Value::try_from_core_value(elem))
                    .collect::<Result<_, _>>()?;

                Ok(Value::Array(elems))
            },
            _ => Err(ParseError::InvalidValue(term.clone())),
        }
    }
}

impl<'a> From<&'a Value> for core::Term {
    fn from(src: &'a Value) -> core::Term {
        use crate::syntax::core::{Literal, RcTerm, Term};
        use crate::syntax::{FloatFormat, IntFormat};

        match *src {
            Value::Pos(value) => Term::Literal(Literal::Pos(value)),
            Value::Int(ref value) => Term::Literal(Literal::Int(value.clone(), IntFormat::Dec)),
            Value::F32(value) => Term::Literal(Literal::F32(value.into(), FloatFormat::Dec)),
            Value::F64(value) => Term::Literal(Literal::F64(value.into(), FloatFormat::Dec)),
            Value::Bool(value) => Term::Literal(Literal::Bool(value)),
            Value::String(ref value) => Term::Literal(Literal::String(value.clone())),
            Value::Struct(ref fields) => {
                let fields = fields
                    .iter()
                    .map(|&(ref label, ref val)| (label.clone(), RcTerm::from(Term::from(val))))
                    .collect();

                Term::Struct(fields)
            },
            Value::Array(ref elems) => {
                let elems = elems
                    .iter()
                    .map(|elem| RcTerm::from(Term::from(elem)))
                    .collect();

                Term::Array(elems)
            },
        }
    }
}

pub fn ptr_deref<T>(
    context: &Context,
    pending: &mut PendingOffsets,
    ptr: &core::RcValue,
    bytes: &mut io::Cursor<T>,
) -> Result<core::RcValue, InternalError>
where
    io::Cursor<T>: io::Read + io::Seek + Clone,
{
    unimplemented!("deref!")
}

/// Reduce a term to its normal form
pub fn nf_term<T>(
    context: &Context,
    pending: &mut PendingOffsets,
    term: &core::RcTerm,
    bytes: &mut io::Cursor<T>,
) -> Result<core::RcValue, InternalError>
where
    io::Cursor<T>: io::Read + io::Seek + Clone,
{
    println!("parser::nf_term: {}", term);
    match *term.inner {
        // E-ANN
        core::Term::Ann(ref expr, _) => nf_term(context, pending, expr, bytes),

        // E-TYPE
        core::Term::Universe(level) => Ok(core::RcValue::from(core::Value::Universe(level))),

        core::Term::IntType(ref min, ref max) => {
            let min = match *min {
                None => None,
                Some(ref x) => Some(nf_term(context, pending, x, bytes)?),
            };

            let max = match *max {
                None => None,
                Some(ref x) => Some(nf_term(context, pending, x, bytes)?),
            };

            Ok(core::RcValue::from(core::Value::IntType(min, max)))
        },

        core::Term::Literal(ref lit) => Ok(core::RcValue::from(core::Value::Literal(lit.clone()))),

        // E-VAR, E-VAR-DEF
        core::Term::Var(ref var) => match *var {
            Var::Free(ref name) => match context.get_definition(name) {
                Some(&Definition::Alias(ref term)) => nf_term(context, pending, term, bytes),
                Some(&Definition::IntersectionType(_))
                | Some(&Definition::StructType(_))
                | Some(&Definition::UnionType(_))
                | None => Ok(core::RcValue::from(core::Value::from(var.clone()))),
            },

            // We should always be substituting bound variables with fresh
            // variables when entering scopes using `unbind`, so if we've
            // encountered one here this is definitely a bug!
            Var::Bound(_) => Err(InternalError::UnexpectedBoundVar {
                span: None,
                var: var.clone(),
            }),
        },

        core::Term::Extern(ref name) => Ok(core::RcValue::from(core::Value::from(
            core::Neutral::Head(core::Head::Extern(name.clone()), core::Spine::new()),
        ))),

        // E-PI
        core::Term::Pi(ref scope) => {
            let ((name, Embed(ann)), body) = scope.clone().unbind();

            Ok(core::RcValue::from(core::Value::Pi(Scope::new(
                (name, Embed(nf_term(context, pending, &ann, bytes)?)),
                nf_term(context, pending, &body, bytes)?,
            ))))
        },

        // E-LAM
        core::Term::Lam(ref scope) => {
            let ((name, Embed(ann)), body) = scope.clone().unbind();

            Ok(core::RcValue::from(core::Value::Lam(Scope::new(
                (name, Embed(nf_term(context, pending, &ann, bytes)?)),
                nf_term(context, pending, &body, bytes)?,
            ))))
        },

        // E-APP
        core::Term::App(ref head, ref arg) => {
            match *nf_term(context, pending, head, bytes)?.inner {
                core::Value::Lam(ref scope) => {
                    // FIXME: do a local unbind here
                    let ((Binder(free_var), Embed(_)), body) = scope.clone().unbind();
                    nf_term(
                        context,
                        pending,
                        &body.substs(&[(free_var, arg.clone())]),
                        bytes,
                    )
                },
                core::Value::Neutral(ref neutral) => {
                    let arg = nf_term(context, pending, arg, bytes)?;

                    Ok(core::RcValue::from(core::Value::Neutral(
                        core::RcNeutral::from(match *neutral.inner {
                            core::Neutral::Head(core::Head::Extern(ref name), ref spine) => {
                                let mut spine = spine.clone();
                                spine.push(arg);

                                println!("parser::nf_term: {}", name);

                                if let Some(prim) = context.get_extern_definition(name) {
                                    match (prim.interpretation)(context, &spine)? {
                                        Some(value) => return Ok(value),
                                        None => {},
                                    }
                                } else {
                                    match (name.as_str(), spine.as_slice()) {
                                        ("ptr-deref", &[ref ptr]) => {
                                            return ptr_deref(context, pending, ptr, bytes);
                                        },
                                        _ => {},
                                    }
                                }

                                core::Neutral::Head(core::Head::Extern(name.clone()), spine)
                            },
                            core::Neutral::Head(ref head, ref spine) => {
                                let mut spine = spine.clone();
                                spine.push(arg);

                                core::Neutral::Head(head.clone(), spine)
                            },
                            core::Neutral::Proj(ref head, ref label, ref spine) => {
                                let mut spine = spine.clone();
                                spine.push(arg);

                                core::Neutral::Proj(head.clone(), label.clone(), spine)
                            },
                            core::Neutral::Match(ref head, ref clauses, ref spine) => {
                                let mut spine = spine.clone();
                                spine.push(arg);

                                core::Neutral::Match(head.clone(), clauses.clone(), spine)
                            },
                        }),
                    )))
                },
                _ => Err(InternalError::ArgumentAppliedToNonFunction),
            }
        },

        core::Term::Refinement(ref scope) => {
            let ((name, Embed(ann)), body) = scope.clone().unbind();

            Ok(core::RcValue::from(core::Value::Refinement(Scope::new(
                (name, Embed(nf_term(context, pending, &ann, bytes)?)),
                nf_term(context, pending, &body, bytes)?,
            ))))
        },

        // E-STRUCT, E-EMPTY-STRUCT
        core::Term::Struct(ref fields) => {
            let fields = fields
                .iter()
                .map(|&(ref label, ref term)| {
                    Ok((label.clone(), nf_term(context, pending, &term, bytes)?))
                })
                .collect::<Result<_, _>>()?;

            Ok(core::RcValue::from(core::Value::Struct(fields)))
        },

        // E-PROJ
        core::Term::Proj(ref expr, ref label) => {
            match *nf_term(context, pending, expr, bytes)? {
                core::Value::Neutral(ref neutral) => {
                    return Ok(core::RcValue::from(core::Value::Neutral(
                        core::RcNeutral::from(core::Neutral::Proj(
                            neutral.clone(),
                            label.clone(),
                            core::Spine::new(),
                        )),
                    )));
                },
                core::Value::Struct(ref fields) => {
                    for &(ref current_label, ref current_expr) in fields {
                        if current_label == label {
                            return Ok(current_expr.clone());
                        }
                    }
                },
                _ => {},
            }

            Err(InternalError::ProjectedOnNonExistentField {
                label: label.clone(),
            })
        },

        // E-CASE
        core::Term::Match(ref head, ref clauses) => {
            let head = nf_term(context, pending, head, bytes)?;

            if let core::Value::Neutral(ref neutral) = *head {
                Ok(core::RcValue::from(core::Value::Neutral(
                    core::RcNeutral::from(core::Neutral::Match(
                        neutral.clone(),
                        clauses
                            .iter()
                            .map(|clause| {
                                let (pattern, body) = clause.clone().unbind();
                                Ok(Scope::new(
                                    pattern,
                                    nf_term(context, pending, &body, bytes)?,
                                ))
                            })
                            .collect::<Result<_, _>>()?,
                        core::Spine::new(),
                    )),
                )))
            } else {
                for clause in clauses {
                    let (pattern, body) = clause.clone().unbind();
                    if let Some(mappings) = match_value(context, pending, &pattern, &head, bytes)? {
                        let mappings = mappings
                            .into_iter()
                            .map(|(free_var, value)| (free_var, core::RcTerm::from(&*value.inner)))
                            .collect::<Vec<_>>();
                        return nf_term(context, pending, &body.substs(&mappings), bytes);
                    }
                }
                Err(InternalError::NoPatternsApplicable)
            }
        },

        // E-ARRAY
        core::Term::Array(ref elems) => Ok(core::RcValue::from(core::Value::Array(
            elems
                .iter()
                .map(|elem| nf_term(context, pending, elem, bytes))
                .collect::<Result<_, _>>()?,
        ))),
    }
}

/// If the pattern matches the value, this function returns the substitutions
/// needed to apply the pattern to some body expression
pub fn match_value<T>(
    context: &Context,
    pending: &mut PendingOffsets,
    pattern: &core::RcPattern,
    value: &core::RcValue,
    bytes: &mut io::Cursor<T>,
) -> Result<Option<Vec<(FreeVar<String>, core::RcValue)>>, InternalError>
where
    io::Cursor<T>: io::Read + io::Seek + Clone,
{
    match (&*pattern.inner, &*value.inner) {
        (&core::Pattern::Binder(Binder(ref free_var)), _) => {
            Ok(Some(vec![(free_var.clone(), value.clone())]))
        },
        (&core::Pattern::Var(Embed(Var::Free(ref free_var))), _) => match context
            .get_definition(free_var)
            .and_then(|definition| match definition {
                Definition::Alias(ref term) => Some(nf_term(context, pending, term, bytes)),
                Definition::IntersectionType(_)
                | Definition::StructType(_)
                | Definition::UnionType(_) => None,
            }) {
            Some(Ok(ref term)) if term == value => Ok(Some(vec![])),
            Some(Ok(_)) | None => Ok(None),
            Some(Err(err)) => Err(err),
        },
        (&core::Pattern::Literal(ref pattern_lit), &core::Value::Literal(ref value_lit))
            if pattern_lit == value_lit =>
        {
            Ok(Some(vec![]))
        },
        (_, _) => Ok(None),
    }
}

pub fn parse_module<T>(
    context: &Context,
    root: &Label,
    module: &core::Module,
    bytes: &mut io::Cursor<T>,
) -> Result<im::HashMap<u64, Value>, ParseError>
where
    io::Cursor<T>: io::Read + io::Seek + Clone,
{
    let mut context = context.clone();
    let mut pending = PendingOffsets::new();

    for (label, Binder(free_var), Embed(definition)) in module.items.clone().unnest() {
        if label == *root {
            let root_value = match definition {
                core::Definition::Alias { ref term, .. } => {
                    let term = nf_term(&context, &mut pending, term, bytes)?;
                    parse_term(&context, &mut pending, &term, bytes)?
                },
                core::Definition::IntersectionType { ref scope } => {
                    let (params, fields_scope) = scope.clone().unbind();

                    if !params.unsafe_patterns.is_empty() {
                        // TODO: more error info?
                        return Err(ParseError::ParametrizedStructType);
                    }

                    let (fields, ()) = fields_scope.unbind();
                    let fields = fields.clone().unnest();
                    let mappings = Vec::with_capacity(fields.len());

                    parse_intersection(&context, &mut pending, fields, mappings, bytes)?
                },
                core::Definition::StructType { ref scope } => {
                    let (params, fields_scope) = scope.clone().unbind();

                    if !params.unsafe_patterns.is_empty() {
                        // TODO: more error info?
                        return Err(ParseError::ParametrizedStructType);
                    }

                    let (fields, ()) = fields_scope.unbind();
                    let fields = fields.clone().unnest();
                    let mappings = Vec::with_capacity(fields.len());

                    parse_struct(&context, &mut pending, fields, mappings, bytes)?
                },
                core::Definition::UnionType { ref scope } => {
                    let (params, variants) = scope.clone().unbind();

                    if !params.unsafe_patterns.is_empty() {
                        // TODO: more error info?
                        return Err(ParseError::ParametrizedUnionType);
                    }

                    parse_union(&context, &mut pending, variants, vec![], bytes)?
                },
            };

            // A dump of the previously parsed values
            let mut parsed_values = im::HashMap::new();
            // A cache of the core types we've looked at through offsets
            let mut parsed_tys = im::HashMap::<u64, core::RcValue>::new();

            // Add root definition
            parsed_values.insert(0, root_value);

            // Follow pending offsets until exhausted ヾ(｡ꏿ﹏ꏿ)ﾉﾞ
            while let Some((pos, ty)) = pending.pop() {
                use im::hashmap::Entry;
                use moniker::BoundTerm;

                match parsed_values.entry(pos) {
                    // This position has not yet been parsed!
                    Entry::Vacant(parsed_entry) => {
                        bytes.set_position(pos); // FIXME: Bounds check?
                        let value = parse_term(&mut context, &mut pending, &ty, bytes)?;
                        parsed_entry.insert(value);
                        parsed_tys.insert(pos, ty);
                    },
                    // Was already parsed!
                    Entry::Occupied(_) => {
                        // It's ok to refer to the same region of memory from
                        // two locations in the same file if the types match
                        let parsed_ty = parsed_tys.get(&pos).expect("expected entry").clone();
                        if !core::Type::term_eq(&parsed_ty, &ty.inner) {
                            return Err(ParseError::OffsetPointedToDifferentTypes(ty, parsed_ty));
                        }
                    },
                }
            }

            return Ok(parsed_values);
        } else {
            context.insert_definition(
                free_var.clone(),
                match definition {
                    core::Definition::Alias { ref term, .. } => Definition::Alias(term.clone()),
                    core::Definition::IntersectionType { ref scope, .. } => {
                        Definition::IntersectionType(scope.clone())
                    },
                    core::Definition::StructType { ref scope } => {
                        Definition::StructType(scope.clone())
                    },
                    core::Definition::UnionType { ref scope } => {
                        Definition::UnionType(scope.clone())
                    },
                },
            );
        }
    }

    Err(ParseError::MissingRoot(root.clone()))
}

fn parse_intersection<T>(
    context: &Context,
    pending: &mut PendingOffsets,
    fields: Vec<(Label, Binder<String>, Embed<core::RcTerm>)>,
    mut mappings: Vec<(FreeVar<String>, core::RcTerm)>,
    bytes: &mut io::Cursor<T>,
) -> Result<Value, ParseError>
where
    io::Cursor<T>: io::Read + io::Seek + Clone,
{
    let mut parsed_fields = Vec::with_capacity(fields.len());
    let init_position = bytes.position();
    let mut final_bytes = None;

    for (label, binder, Embed(ann)) in fields {
        let mut inner_bytes = bytes.clone();

        let ann = nf_term(context, pending, &ann.substs(&mappings), bytes)?;
        let ann_value = parse_term(context, pending, &ann, &mut inner_bytes)?;
        mappings.push((
            binder.0.clone(),
            core::RcTerm::from(core::Term::from(&ann_value)),
        ));

        parsed_fields.push((label, ann_value));

        // FIXME: check this statically
        let current_size = inner_bytes.position() - init_position;
        match final_bytes {
            None => final_bytes = Some(inner_bytes),
            Some(ref final_bytes) => {
                let expected_size = final_bytes.position() - init_position;
                if expected_size != current_size {
                    return Err(ParseError::MismatchedIntersectionSize(
                        expected_size,
                        current_size,
                    ));
                }
            },
        }
    }

    if let Some(final_bytes) = final_bytes {
        *bytes = final_bytes;
    }

    Ok(Value::Struct(parsed_fields))
}

fn parse_struct<T>(
    context: &Context,
    pending: &mut PendingOffsets,
    fields: Vec<(Label, Binder<String>, Embed<core::RcTerm>)>,
    mut mappings: Vec<(FreeVar<String>, core::RcTerm)>,
    bytes: &mut io::Cursor<T>,
) -> Result<Value, ParseError>
where
    io::Cursor<T>: io::Read + io::Seek + Clone,
{
    let fields = fields
        .into_iter()
        .map(|(label, binder, Embed(ann))| {
            let ann = nf_term(context, pending, &ann.substs(&mappings), bytes)?;
            let ann_value = parse_term(context, pending, &ann, bytes)?;
            mappings.push((
                binder.0.clone(),
                core::RcTerm::from(core::Term::from(&ann_value)),
            ));

            Ok((label.clone(), ann_value))
        })
        .collect::<Result<_, ParseError>>()?;

    Ok(Value::Struct(fields))
}

fn parse_union<T>(
    context: &Context,
    pending: &mut PendingOffsets,
    variants: Vec<core::RcTerm>,
    mappings: Vec<(FreeVar<String>, core::RcTerm)>,
    bytes: &mut io::Cursor<T>,
) -> Result<Value, ParseError>
where
    io::Cursor<T>: io::Read + io::Seek + Clone,
{
    for ann in variants {
        let mut inner_bytes = bytes.clone();
        let mut inner_pending = pending.clone();

        let ann = nf_term(context, pending, &ann.substs(&mappings), bytes)?;

        if let Ok(value) = parse_term(context, &mut inner_pending, &ann, &mut inner_bytes) {
            *bytes = inner_bytes;
            *pending = inner_pending;
            return Ok(value);
        }
    }

    Err(ParseError::NoVariantMatched)
}

fn queue_offset(
    pending: &mut PendingOffsets,
    pos: &core::RcValue,
    offset: u64,
    ty: &core::RcType,
) -> Result<Value, ParseError> {
    match *pos.inner {
        core::Value::Literal(core::Literal::Pos(pos)) => {
            pending.push((pos + offset, ty.clone()));
            Ok(Value::Pos(pos + offset))
        },
        _ => unimplemented!(),
    }
}

fn queue_link(
    pending: &mut PendingOffsets,
    pos: &core::RcValue,
    offset: &core::RcValue,
    ty: &core::RcType,
) -> Result<Value, ParseError> {
    match *offset.inner {
        core::Value::Literal(core::Literal::Int(ref offset, _)) => {
            queue_offset(pending, pos, offset.to_u64().unwrap(), ty)
        },
        _ => unimplemented!(),
    }
}

fn parse_term<T>(
    context: &Context,
    pending: &mut PendingOffsets,
    ty: &core::RcType,
    bytes: &mut io::Cursor<T>,
) -> Result<Value, ParseError>
where
    io::Cursor<T>: io::Read + io::Seek + Clone,
{
    use byteorder::{BigEndian as Be, LittleEndian as Le, ReadBytesExt};
    use moniker::BoundTerm;

    use crate::syntax::IntFormat;

    match **ty {
        // Parse builtin types
        _ if core::RcValue::term_eq(ty, context.pos()) => Ok(Value::Pos(bytes.position())),
        _ if core::RcValue::term_eq(ty, context.u8()) => Ok(Value::int(bytes.read_u8()?)),
        _ if core::RcValue::term_eq(ty, context.u16le()) => Ok(Value::int(bytes.read_u16::<Le>()?)),
        _ if core::RcValue::term_eq(ty, context.u16be()) => Ok(Value::int(bytes.read_u16::<Be>()?)),
        _ if core::RcValue::term_eq(ty, context.u32le()) => Ok(Value::int(bytes.read_u32::<Le>()?)),
        _ if core::RcValue::term_eq(ty, context.u32be()) => Ok(Value::int(bytes.read_u32::<Be>()?)),
        _ if core::RcValue::term_eq(ty, context.u64le()) => Ok(Value::int(bytes.read_u64::<Le>()?)),
        _ if core::RcValue::term_eq(ty, context.u64be()) => Ok(Value::int(bytes.read_u64::<Be>()?)),
        _ if core::RcValue::term_eq(ty, context.s8()) => Ok(Value::int(bytes.read_i8()?)),
        _ if core::RcValue::term_eq(ty, context.s16le()) => Ok(Value::int(bytes.read_i16::<Le>()?)),
        _ if core::RcValue::term_eq(ty, context.s16be()) => Ok(Value::int(bytes.read_i16::<Be>()?)),
        _ if core::RcValue::term_eq(ty, context.s32le()) => Ok(Value::int(bytes.read_i32::<Le>()?)),
        _ if core::RcValue::term_eq(ty, context.s32be()) => Ok(Value::int(bytes.read_i32::<Be>()?)),
        _ if core::RcValue::term_eq(ty, context.s64le()) => Ok(Value::int(bytes.read_i64::<Le>()?)),
        _ if core::RcValue::term_eq(ty, context.s64be()) => Ok(Value::int(bytes.read_i64::<Be>()?)),
        _ if core::RcValue::term_eq(ty, context.f32le()) => Ok(Value::F32(bytes.read_f32::<Le>()?)),
        _ if core::RcValue::term_eq(ty, context.f32be()) => Ok(Value::F32(bytes.read_f32::<Be>()?)),
        _ if core::RcValue::term_eq(ty, context.f64le()) => Ok(Value::F64(bytes.read_f64::<Le>()?)),
        _ if core::RcValue::term_eq(ty, context.f64be()) => Ok(Value::F64(bytes.read_f64::<Be>()?)),

        core::Value::Refinement(ref scope) => {
            let ((Binder(free_var), Embed(ann)), pred) = scope.clone().unbind();
            let ann_value = parse_term(context, pending, &ann, bytes)?;
            let pred_value = {
                let ann_value = core::RcTerm::from(core::Term::from(&ann_value));
                nf_term(
                    context,
                    pending,
                    &pred.substs(&[(free_var, ann_value)]),
                    bytes,
                )?
            };

            match *pred_value.inner {
                core::Value::Literal(core::Literal::Bool(true)) => Ok(ann_value),
                core::Value::Literal(core::Literal::Bool(false)) => {
                    Err(ParseError::FailedPredicate(pred.clone()))
                },
                _ => unimplemented!("unexpected value: {}", pred_value),
            }
        },

        // Invalid parse types
        core::Value::Universe(_)
        | core::Value::IntType(_, _)
        | core::Value::Literal(_)
        | core::Value::Pi(_)
        | core::Value::Lam(_)
        | core::Value::Struct(_)
        | core::Value::Array(_) => Err(ParseError::InvalidType(ty.clone())),

        #[cfg_attr(rustfmt, rustfmt_skip)]
        core::Value::Neutral(ref neutral) => {
            // Parse offsets
            if let Some((pos, ty)) = context.offset8(ty) { return queue_offset(pending, pos, bytes.read_u8()? as u64, ty); }
            if let Some((pos, ty)) = context.offset16le(ty) { return queue_offset(pending, pos, bytes.read_u16::<Le>()? as u64, ty); }
            if let Some((pos, ty)) = context.offset16be(ty) { return queue_offset(pending, pos, bytes.read_u16::<Be>()? as u64, ty); }
            if let Some((pos, ty)) = context.offset32le(ty) { return queue_offset(pending, pos, bytes.read_u32::<Le>()? as u64, ty); }
            if let Some((pos, ty)) = context.offset32be(ty) { return queue_offset(pending, pos, bytes.read_u32::<Be>()? as u64, ty); }
            if let Some((pos, ty)) = context.offset64le(ty) { return queue_offset(pending, pos, bytes.read_u64::<Le>()? as u64, ty); }
            if let Some((pos, ty)) = context.offset64be(ty) { return queue_offset(pending, pos, bytes.read_u64::<Be>()? as u64, ty); }
            if let Some((pos, offset, ty)) = context.link(ty) { return queue_link(pending, pos, offset, ty); }

            // Reserved things
            if let Some(elem_ty) = context.reserved(ty) {
                parse_term(context, pending, elem_ty, bytes)?;
                return Ok(Value::Struct(Vec::new()));
            }

            // Parse arrays
            if let Some((len, elem_ty)) = context.array(ty) {
                return Ok(Value::Array(
                    (0..len.to_usize().unwrap()) // FIXME
                        .map(|_| parse_term(context, pending, elem_ty, bytes))
                        .collect::<Result<_, _>>()?,
                ));
            }

            // Computed things
            if let Some((_elem_ty, fun)) = context.compute(ty) {
                return Value::try_from_core_value(&nf_term(
                    context,
                    pending,
                    &core::RcTerm::from(core::Term::App(
                        core::RcTerm::from(core::Term::from(&**fun)),
                        core::RcTerm::from(core::Term::Struct(vec![])),
                    )),
                    bytes,
                )?);
            }

            // Make arrays
            if let Some((len, _elem_ty, fun)) = context.compute_array(ty) {
                return Ok(Value::Array(
                    (0..len.to_usize().unwrap()) // FIXME
                        .map(|i| Value::try_from_core_value(&nf_term(
                            context,
                            pending,
                            &core::RcTerm::from(core::Term::App(
                                core::RcTerm::from(core::Term::from(&**fun)),
                                core::RcTerm::from(core::Term::Literal(
                                    core::Literal::Int(i.into(), IntFormat::Dec),
                                )),
                            )),
                            bytes,
                        )?))
                        .collect::<Result<_, _>>()?,
                ));
            }

            match **neutral {
                core::Neutral::Head(core::Head::Var(Var::Free(ref free_var)), ref spine) => {
                    // Follow definitions
                    match context.get_definition(free_var) {
                        // FIXME: follow alias?
                        Some(&Definition::Alias(_)) => Err(ParseError::InvalidType(ty.clone())),
                        Some(&Definition::IntersectionType(ref scope)) => {
                            let (params, fields_scope) = scope.clone().unbind();
                            let (fields, ()) = fields_scope.unbind();
                            let params = params.unnest();
                            let fields = fields.unnest();

                            if params.len() != spine.len() {
                                unimplemented!();
                            }

                            let mut mappings = Vec::with_capacity(params.len() + fields.len());

                            for (&(Binder(ref free_var), _), arg) in
                                Iterator::zip(params.iter(), spine.iter())
                            {
                                let arg = arg.substs(&mappings);
                                mappings.push((free_var.clone(), arg));
                            }

                            parse_intersection(context, pending, fields, mappings, bytes)
                        }
                        Some(&Definition::StructType(ref scope)) => {
                            let (params, fields_scope) = scope.clone().unbind();
                            let (fields, ()) = fields_scope.unbind();
                            let params = params.unnest();
                            let fields = fields.unnest();

                            if params.len() != spine.len() {
                                unimplemented!();
                            }

                            let mut mappings = Vec::with_capacity(params.len() + fields.len());

                            for (&(Binder(ref free_var), _), arg) in
                                Iterator::zip(params.iter(), spine.iter())
                            {
                                let arg = arg.substs(&mappings);
                                mappings.push((free_var.clone(), arg));
                            }

                            parse_struct(context, pending, fields, mappings, bytes)
                        },
                        Some(&Definition::UnionType(ref scope)) => {
                            let (params, variants) = scope.clone().unbind();
                            let params = params.unnest();

                            if params.len() != spine.len() {
                                unimplemented!();
                            }

                            let mut mappings = Vec::with_capacity(params.len());

                            for (&(Binder(ref free_var), _), arg) in
                                Iterator::zip(params.iter(), spine.iter())
                            {
                                let arg = arg.substs(&mappings);
                                mappings.push((free_var.clone(), arg));
                            }

                            parse_union(context, pending, variants, mappings, bytes)
                        },
                        // Definition not found
                        None => Err(ParseError::InvalidType(ty.clone())),
                    }
                },
                // Invalid parse types
                core::Neutral::Head(..) | core::Neutral::Proj(..) | core::Neutral::Match(..) => {
                    Err(ParseError::InvalidType(ty.clone()))
                },
            }
        },
    }
}
