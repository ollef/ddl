//! Integration tests for the binary data description language.

#![warn(rust_2018_idioms)]
#![cfg(test)]

mod support;

macro_rules! test {
    ($test_name:ident, $test_path:literal) => {
        #[test]
        fn $test_name() {
            $crate::support::run_integration_test(stringify!($test_name), $test_path);
        }
    };
}

test!(pass_empty, "pass_empty.ddl");

test!(fail_duplicate_definitions, "fail_duplicate_definitions.ddl");
test!(fail_unexpected_token, "fail_unexpected_token.ddl");
test!(fail_unexpected_character, "fail_unexpected_character.ddl");

#[rustfmt::skip]
mod alias {
    test!(pass_constants, "alias/pass_constants.ddl");
    test!(pass_globals, "alias/pass_globals.ddl");
    test!(pass_ann, "alias/pass_ann.ddl");
    test!(pass_alias_type, "alias/pass_alias_type.ddl");
    test!(pass_ann_ann, "alias/pass_ann_ann.ddl");
    test!(pass_ann_sugar, "alias/pass_ann_sugar.ddl");
    test!(pass_simple, "alias/pass_simple.ddl");
    test!(pass_simple_doc, "alias/pass_simple_doc.ddl");

    test!(fail_ann_mismatch, "alias/fail_ann_mismatch.ddl");
    test!(fail_kind_has_no_type, "alias/fail_kind_has_no_type.ddl");
    test!(fail_unconstrained_int_type, "alias/fail_unconstrained_int_type.ddl");
}

#[rustfmt::skip]
mod r#struct {
    test!(pass_empty, "struct/pass_empty.ddl");
    test!(pass_empty_doc, "struct/pass_empty_doc.ddl");
    test!(pass_mixed_format_host, "struct/pass_mixed_format_host.ddl");
    test!(pass_pair, "struct/pass_pair.ddl");
    test!(pass_singleton, "struct/pass_singleton.ddl");
    test!(pass_var, "struct/pass_var.ddl");

    test!(fail_duplicate_fields, "struct/fail_duplicate_fields.ddl");
    test!(fail_field_type_mismatch, "struct/fail_field_type_mismatch.ddl");
    test!(fail_missing_closing_brace, "struct/fail_missing_closing_brace.ddl");
    test!(fail_missing_fields, "struct/fail_missing_fields.ddl");
    test!(fail_missing_name, "struct/fail_missing_name.ddl");
    test!(fail_undefined_field, "struct/fail_undefined_field.ddl");
}
