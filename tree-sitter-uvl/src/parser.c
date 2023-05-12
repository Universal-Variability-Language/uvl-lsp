#include <tree_sitter/parser.h>

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"
#endif

#define LANGUAGE_VERSION 14
#define STATE_COUNT 319
#define LARGE_STATE_COUNT 21
#define SYMBOL_COUNT 98
#define ALIAS_COUNT 2
#define TOKEN_COUNT 60
#define EXTERNAL_TOKEN_COUNT 7
#define FIELD_COUNT 16
#define MAX_ALIAS_SEQUENCE_LENGTH 7
#define PRODUCTION_ID_COUNT 38

enum {
  sym_name = 1,
  anon_sym_cardinality = 2,
  anon_sym_LBRACE = 3,
  anon_sym_COMMA = 4,
  anon_sym_RBRACE = 5,
  anon_sym_as = 6,
  anon_sym_namespace = 7,
  anon_sym_LBRACK = 8,
  anon_sym_DOT_DOT = 9,
  anon_sym_STAR = 10,
  anon_sym_RBRACK = 11,
  anon_sym_constraint = 12,
  anon_sym_constraints = 13,
  anon_sym_BANG = 14,
  anon_sym_PIPE = 15,
  anon_sym_AMP = 16,
  anon_sym_EQ_GT = 17,
  anon_sym_LT_EQ_GT = 18,
  anon_sym_GT = 19,
  anon_sym_LT = 20,
  anon_sym_EQ_EQ = 21,
  anon_sym_PLUS = 22,
  anon_sym_DASH = 23,
  anon_sym_SLASH = 24,
  anon_sym_LPAREN = 25,
  anon_sym_RPAREN = 26,
  anon_sym_true = 27,
  anon_sym_false = 28,
  sym_number = 29,
  sym_comment = 30,
  anon_sym_DOT = 31,
  anon_sym_or = 32,
  anon_sym_alternative = 33,
  anon_sym_mandatory = 34,
  anon_sym_optional = 35,
  anon_sym_SMT_DASHlevel = 36,
  anon_sym_SAT_DASHlevel = 37,
  anon_sym_TYPE_DASHlevel = 38,
  anon_sym_group_DASHcardinality = 39,
  anon_sym_feature_DASHcardinality = 40,
  anon_sym_aggregate_DASHfunction = 41,
  anon_sym_type_DASHconstraints = 42,
  anon_sym_string_DASHconstraints = 43,
  anon_sym_numeric_DASHconstraints = 44,
  anon_sym_Boolean = 45,
  anon_sym_Real = 46,
  anon_sym_Integer = 47,
  anon_sym_String = 48,
  anon_sym_SQUOTE = 49,
  anon_sym_DQUOTE = 50,
  aux_sym_string_name_token1 = 51,
  sym_string_content = 52,
  sym_imports = 53,
  sym_features = 54,
  sym_include = 55,
  sym_int = 56,
  sym__indent = 57,
  sym__dedent = 58,
  sym__newline = 59,
  sym_source_file = 60,
  sym_blk = 61,
  sym_attributes = 62,
  sym__header = 63,
  sym_typed_feature = 64,
  sym_ref = 65,
  sym_namespace = 66,
  sym_incomplete_namespace = 67,
  sym_incomplete_ref = 68,
  sym_cardinality = 69,
  sym_attribute_constraint = 70,
  sym_attribute_constraints = 71,
  sym_attribute_value = 72,
  sym__attribute = 73,
  sym__value = 74,
  sym__expr = 75,
  sym_unary_expr = 76,
  sym_binary_expr = 77,
  sym_nested_expr = 78,
  sym_function = 79,
  sym_vector = 80,
  sym_bool = 81,
  sym_path = 82,
  sym_lang_lvl = 83,
  sym_group_mode = 84,
  sym_major_lvl = 85,
  sym_minor_lvl = 86,
  sym_string = 87,
  sym_string_name = 88,
  sym_constraints = 89,
  sym__any_name = 90,
  aux_sym_source_file_repeat1 = 91,
  aux_sym_attributes_repeat1 = 92,
  aux_sym_attribute_constraints_repeat1 = 93,
  aux_sym_function_repeat1 = 94,
  aux_sym_vector_repeat1 = 95,
  aux_sym_path_repeat1 = 96,
  aux_sym_lang_lvl_repeat1 = 97,
  alias_sym_attrib_expr = 98,
  alias_sym_constraint = 99,
};

static const char * const ts_symbol_names[] = {
  [ts_builtin_sym_end] = "end",
  [sym_name] = "name",
  [anon_sym_cardinality] = "cardinality",
  [anon_sym_LBRACE] = "{",
  [anon_sym_COMMA] = ",",
  [anon_sym_RBRACE] = "}",
  [anon_sym_as] = "as",
  [anon_sym_namespace] = "namespace",
  [anon_sym_LBRACK] = "[",
  [anon_sym_DOT_DOT] = "..",
  [anon_sym_STAR] = "*",
  [anon_sym_RBRACK] = "]",
  [anon_sym_constraint] = "constraint",
  [anon_sym_constraints] = "constraints",
  [anon_sym_BANG] = "!",
  [anon_sym_PIPE] = "|",
  [anon_sym_AMP] = "&",
  [anon_sym_EQ_GT] = "=>",
  [anon_sym_LT_EQ_GT] = "<=>",
  [anon_sym_GT] = ">",
  [anon_sym_LT] = "<",
  [anon_sym_EQ_EQ] = "==",
  [anon_sym_PLUS] = "+",
  [anon_sym_DASH] = "-",
  [anon_sym_SLASH] = "/",
  [anon_sym_LPAREN] = "(",
  [anon_sym_RPAREN] = ")",
  [anon_sym_true] = "true",
  [anon_sym_false] = "false",
  [sym_number] = "number",
  [sym_comment] = "comment",
  [anon_sym_DOT] = ".",
  [anon_sym_or] = "or",
  [anon_sym_alternative] = "alternative",
  [anon_sym_mandatory] = "mandatory",
  [anon_sym_optional] = "optional",
  [anon_sym_SMT_DASHlevel] = "SMT-level",
  [anon_sym_SAT_DASHlevel] = "SAT-level",
  [anon_sym_TYPE_DASHlevel] = "TYPE-level",
  [anon_sym_group_DASHcardinality] = "group-cardinality",
  [anon_sym_feature_DASHcardinality] = "feature-cardinality",
  [anon_sym_aggregate_DASHfunction] = "aggregate-function",
  [anon_sym_type_DASHconstraints] = "type-constraints",
  [anon_sym_string_DASHconstraints] = "string-constraints",
  [anon_sym_numeric_DASHconstraints] = "numeric-constraints",
  [anon_sym_Boolean] = "Boolean",
  [anon_sym_Real] = "Real",
  [anon_sym_Integer] = "Integer",
  [anon_sym_String] = "String",
  [anon_sym_SQUOTE] = "'",
  [anon_sym_DQUOTE] = "\"",
  [aux_sym_string_name_token1] = "string_name_token1",
  [sym_string_content] = "string_content",
  [sym_imports] = "imports",
  [sym_features] = "features",
  [sym_include] = "include",
  [sym_int] = "int",
  [sym__indent] = "_indent",
  [sym__dedent] = "_dedent",
  [sym__newline] = "_newline",
  [sym_source_file] = "source_file",
  [sym_blk] = "blk",
  [sym_attributes] = "attributes",
  [sym__header] = "_header",
  [sym_typed_feature] = "typed_feature",
  [sym_ref] = "ref",
  [sym_namespace] = "namespace",
  [sym_incomplete_namespace] = "incomplete_namespace",
  [sym_incomplete_ref] = "incomplete_ref",
  [sym_cardinality] = "cardinality",
  [sym_attribute_constraint] = "attribute_constraint",
  [sym_attribute_constraints] = "attribute_constraints",
  [sym_attribute_value] = "attribute_value",
  [sym__attribute] = "_attribute",
  [sym__value] = "_value",
  [sym__expr] = "_expr",
  [sym_unary_expr] = "unary_expr",
  [sym_binary_expr] = "binary_expr",
  [sym_nested_expr] = "nested_expr",
  [sym_function] = "function",
  [sym_vector] = "vector",
  [sym_bool] = "bool",
  [sym_path] = "path",
  [sym_lang_lvl] = "lang_lvl",
  [sym_group_mode] = "group_mode",
  [sym_major_lvl] = "major_lvl",
  [sym_minor_lvl] = "minor_lvl",
  [sym_string] = "string",
  [sym_string_name] = "name",
  [sym_constraints] = "constraints",
  [sym__any_name] = "_any_name",
  [aux_sym_source_file_repeat1] = "source_file_repeat1",
  [aux_sym_attributes_repeat1] = "attributes_repeat1",
  [aux_sym_attribute_constraints_repeat1] = "attribute_constraints_repeat1",
  [aux_sym_function_repeat1] = "function_repeat1",
  [aux_sym_vector_repeat1] = "vector_repeat1",
  [aux_sym_path_repeat1] = "path_repeat1",
  [aux_sym_lang_lvl_repeat1] = "lang_lvl_repeat1",
  [alias_sym_attrib_expr] = "attrib_expr",
  [alias_sym_constraint] = "constraint",
};

static const TSSymbol ts_symbol_map[] = {
  [ts_builtin_sym_end] = ts_builtin_sym_end,
  [sym_name] = sym_name,
  [anon_sym_cardinality] = anon_sym_cardinality,
  [anon_sym_LBRACE] = anon_sym_LBRACE,
  [anon_sym_COMMA] = anon_sym_COMMA,
  [anon_sym_RBRACE] = anon_sym_RBRACE,
  [anon_sym_as] = anon_sym_as,
  [anon_sym_namespace] = anon_sym_namespace,
  [anon_sym_LBRACK] = anon_sym_LBRACK,
  [anon_sym_DOT_DOT] = anon_sym_DOT_DOT,
  [anon_sym_STAR] = anon_sym_STAR,
  [anon_sym_RBRACK] = anon_sym_RBRACK,
  [anon_sym_constraint] = anon_sym_constraint,
  [anon_sym_constraints] = anon_sym_constraints,
  [anon_sym_BANG] = anon_sym_BANG,
  [anon_sym_PIPE] = anon_sym_PIPE,
  [anon_sym_AMP] = anon_sym_AMP,
  [anon_sym_EQ_GT] = anon_sym_EQ_GT,
  [anon_sym_LT_EQ_GT] = anon_sym_LT_EQ_GT,
  [anon_sym_GT] = anon_sym_GT,
  [anon_sym_LT] = anon_sym_LT,
  [anon_sym_EQ_EQ] = anon_sym_EQ_EQ,
  [anon_sym_PLUS] = anon_sym_PLUS,
  [anon_sym_DASH] = anon_sym_DASH,
  [anon_sym_SLASH] = anon_sym_SLASH,
  [anon_sym_LPAREN] = anon_sym_LPAREN,
  [anon_sym_RPAREN] = anon_sym_RPAREN,
  [anon_sym_true] = anon_sym_true,
  [anon_sym_false] = anon_sym_false,
  [sym_number] = sym_number,
  [sym_comment] = sym_comment,
  [anon_sym_DOT] = anon_sym_DOT,
  [anon_sym_or] = anon_sym_or,
  [anon_sym_alternative] = anon_sym_alternative,
  [anon_sym_mandatory] = anon_sym_mandatory,
  [anon_sym_optional] = anon_sym_optional,
  [anon_sym_SMT_DASHlevel] = anon_sym_SMT_DASHlevel,
  [anon_sym_SAT_DASHlevel] = anon_sym_SAT_DASHlevel,
  [anon_sym_TYPE_DASHlevel] = anon_sym_TYPE_DASHlevel,
  [anon_sym_group_DASHcardinality] = anon_sym_group_DASHcardinality,
  [anon_sym_feature_DASHcardinality] = anon_sym_feature_DASHcardinality,
  [anon_sym_aggregate_DASHfunction] = anon_sym_aggregate_DASHfunction,
  [anon_sym_type_DASHconstraints] = anon_sym_type_DASHconstraints,
  [anon_sym_string_DASHconstraints] = anon_sym_string_DASHconstraints,
  [anon_sym_numeric_DASHconstraints] = anon_sym_numeric_DASHconstraints,
  [anon_sym_Boolean] = anon_sym_Boolean,
  [anon_sym_Real] = anon_sym_Real,
  [anon_sym_Integer] = anon_sym_Integer,
  [anon_sym_String] = anon_sym_String,
  [anon_sym_SQUOTE] = anon_sym_SQUOTE,
  [anon_sym_DQUOTE] = anon_sym_DQUOTE,
  [aux_sym_string_name_token1] = aux_sym_string_name_token1,
  [sym_string_content] = sym_string_content,
  [sym_imports] = sym_imports,
  [sym_features] = sym_features,
  [sym_include] = sym_include,
  [sym_int] = sym_int,
  [sym__indent] = sym__indent,
  [sym__dedent] = sym__dedent,
  [sym__newline] = sym__newline,
  [sym_source_file] = sym_source_file,
  [sym_blk] = sym_blk,
  [sym_attributes] = sym_attributes,
  [sym__header] = sym__header,
  [sym_typed_feature] = sym_typed_feature,
  [sym_ref] = sym_ref,
  [sym_namespace] = sym_namespace,
  [sym_incomplete_namespace] = sym_incomplete_namespace,
  [sym_incomplete_ref] = sym_incomplete_ref,
  [sym_cardinality] = sym_cardinality,
  [sym_attribute_constraint] = sym_attribute_constraint,
  [sym_attribute_constraints] = sym_attribute_constraints,
  [sym_attribute_value] = sym_attribute_value,
  [sym__attribute] = sym__attribute,
  [sym__value] = sym__value,
  [sym__expr] = sym__expr,
  [sym_unary_expr] = sym_unary_expr,
  [sym_binary_expr] = sym_binary_expr,
  [sym_nested_expr] = sym_nested_expr,
  [sym_function] = sym_function,
  [sym_vector] = sym_vector,
  [sym_bool] = sym_bool,
  [sym_path] = sym_path,
  [sym_lang_lvl] = sym_lang_lvl,
  [sym_group_mode] = sym_group_mode,
  [sym_major_lvl] = sym_major_lvl,
  [sym_minor_lvl] = sym_minor_lvl,
  [sym_string] = sym_string,
  [sym_string_name] = sym_name,
  [sym_constraints] = sym_constraints,
  [sym__any_name] = sym__any_name,
  [aux_sym_source_file_repeat1] = aux_sym_source_file_repeat1,
  [aux_sym_attributes_repeat1] = aux_sym_attributes_repeat1,
  [aux_sym_attribute_constraints_repeat1] = aux_sym_attribute_constraints_repeat1,
  [aux_sym_function_repeat1] = aux_sym_function_repeat1,
  [aux_sym_vector_repeat1] = aux_sym_vector_repeat1,
  [aux_sym_path_repeat1] = aux_sym_path_repeat1,
  [aux_sym_lang_lvl_repeat1] = aux_sym_lang_lvl_repeat1,
  [alias_sym_attrib_expr] = alias_sym_attrib_expr,
  [alias_sym_constraint] = alias_sym_constraint,
};

static const TSSymbolMetadata ts_symbol_metadata[] = {
  [ts_builtin_sym_end] = {
    .visible = false,
    .named = true,
  },
  [sym_name] = {
    .visible = true,
    .named = true,
  },
  [anon_sym_cardinality] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_LBRACE] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_COMMA] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_RBRACE] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_as] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_namespace] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_LBRACK] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_DOT_DOT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_STAR] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_RBRACK] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_constraint] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_constraints] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_BANG] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_PIPE] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_AMP] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_EQ_GT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_LT_EQ_GT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_GT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_LT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_EQ_EQ] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_PLUS] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_DASH] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_SLASH] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_LPAREN] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_RPAREN] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_true] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_false] = {
    .visible = true,
    .named = false,
  },
  [sym_number] = {
    .visible = true,
    .named = true,
  },
  [sym_comment] = {
    .visible = true,
    .named = true,
  },
  [anon_sym_DOT] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_or] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_alternative] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_mandatory] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_optional] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_SMT_DASHlevel] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_SAT_DASHlevel] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_TYPE_DASHlevel] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_group_DASHcardinality] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_feature_DASHcardinality] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_aggregate_DASHfunction] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_type_DASHconstraints] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_string_DASHconstraints] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_numeric_DASHconstraints] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_Boolean] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_Real] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_Integer] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_String] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_SQUOTE] = {
    .visible = true,
    .named = false,
  },
  [anon_sym_DQUOTE] = {
    .visible = true,
    .named = false,
  },
  [aux_sym_string_name_token1] = {
    .visible = false,
    .named = false,
  },
  [sym_string_content] = {
    .visible = true,
    .named = true,
  },
  [sym_imports] = {
    .visible = true,
    .named = true,
  },
  [sym_features] = {
    .visible = true,
    .named = true,
  },
  [sym_include] = {
    .visible = true,
    .named = true,
  },
  [sym_int] = {
    .visible = true,
    .named = true,
  },
  [sym__indent] = {
    .visible = false,
    .named = true,
  },
  [sym__dedent] = {
    .visible = false,
    .named = true,
  },
  [sym__newline] = {
    .visible = false,
    .named = true,
  },
  [sym_source_file] = {
    .visible = true,
    .named = true,
  },
  [sym_blk] = {
    .visible = true,
    .named = true,
  },
  [sym_attributes] = {
    .visible = true,
    .named = true,
  },
  [sym__header] = {
    .visible = false,
    .named = true,
  },
  [sym_typed_feature] = {
    .visible = true,
    .named = true,
  },
  [sym_ref] = {
    .visible = true,
    .named = true,
  },
  [sym_namespace] = {
    .visible = true,
    .named = true,
  },
  [sym_incomplete_namespace] = {
    .visible = true,
    .named = true,
  },
  [sym_incomplete_ref] = {
    .visible = true,
    .named = true,
  },
  [sym_cardinality] = {
    .visible = true,
    .named = true,
  },
  [sym_attribute_constraint] = {
    .visible = true,
    .named = true,
  },
  [sym_attribute_constraints] = {
    .visible = true,
    .named = true,
  },
  [sym_attribute_value] = {
    .visible = true,
    .named = true,
  },
  [sym__attribute] = {
    .visible = false,
    .named = true,
  },
  [sym__value] = {
    .visible = false,
    .named = true,
  },
  [sym__expr] = {
    .visible = false,
    .named = true,
  },
  [sym_unary_expr] = {
    .visible = true,
    .named = true,
  },
  [sym_binary_expr] = {
    .visible = true,
    .named = true,
  },
  [sym_nested_expr] = {
    .visible = true,
    .named = true,
  },
  [sym_function] = {
    .visible = true,
    .named = true,
  },
  [sym_vector] = {
    .visible = true,
    .named = true,
  },
  [sym_bool] = {
    .visible = true,
    .named = true,
  },
  [sym_path] = {
    .visible = true,
    .named = true,
  },
  [sym_lang_lvl] = {
    .visible = true,
    .named = true,
  },
  [sym_group_mode] = {
    .visible = true,
    .named = true,
  },
  [sym_major_lvl] = {
    .visible = true,
    .named = true,
  },
  [sym_minor_lvl] = {
    .visible = true,
    .named = true,
  },
  [sym_string] = {
    .visible = true,
    .named = true,
  },
  [sym_string_name] = {
    .visible = true,
    .named = true,
  },
  [sym_constraints] = {
    .visible = true,
    .named = true,
  },
  [sym__any_name] = {
    .visible = false,
    .named = true,
  },
  [aux_sym_source_file_repeat1] = {
    .visible = false,
    .named = false,
  },
  [aux_sym_attributes_repeat1] = {
    .visible = false,
    .named = false,
  },
  [aux_sym_attribute_constraints_repeat1] = {
    .visible = false,
    .named = false,
  },
  [aux_sym_function_repeat1] = {
    .visible = false,
    .named = false,
  },
  [aux_sym_vector_repeat1] = {
    .visible = false,
    .named = false,
  },
  [aux_sym_path_repeat1] = {
    .visible = false,
    .named = false,
  },
  [aux_sym_lang_lvl_repeat1] = {
    .visible = false,
    .named = false,
  },
  [alias_sym_attrib_expr] = {
    .visible = true,
    .named = true,
  },
  [alias_sym_constraint] = {
    .visible = true,
    .named = true,
  },
};

enum {
  field_alias = 1,
  field_arg = 2,
  field_attribs = 3,
  field_begin = 4,
  field_cardinality = 5,
  field_child = 6,
  field_end = 7,
  field_header = 8,
  field_lhs = 9,
  field_name = 10,
  field_op = 11,
  field_path = 12,
  field_rhs = 13,
  field_tail = 14,
  field_type = 15,
  field_value = 16,
};

static const char * const ts_field_names[] = {
  [0] = NULL,
  [field_alias] = "alias",
  [field_arg] = "arg",
  [field_attribs] = "attribs",
  [field_begin] = "begin",
  [field_cardinality] = "cardinality",
  [field_child] = "child",
  [field_end] = "end",
  [field_header] = "header",
  [field_lhs] = "lhs",
  [field_name] = "name",
  [field_op] = "op",
  [field_path] = "path",
  [field_rhs] = "rhs",
  [field_tail] = "tail",
  [field_type] = "type",
  [field_value] = "value",
};

static const TSFieldMapSlice ts_field_map_slices[PRODUCTION_ID_COUNT] = {
  [2] = {.index = 0, .length = 1},
  [3] = {.index = 1, .length = 1},
  [4] = {.index = 2, .length = 2},
  [5] = {.index = 4, .length = 1},
  [6] = {.index = 5, .length = 2},
  [7] = {.index = 7, .length = 1},
  [8] = {.index = 8, .length = 2},
  [9] = {.index = 10, .length = 1},
  [10] = {.index = 11, .length = 1},
  [11] = {.index = 12, .length = 3},
  [12] = {.index = 15, .length = 2},
  [13] = {.index = 17, .length = 1},
  [14] = {.index = 18, .length = 2},
  [15] = {.index = 20, .length = 3},
  [16] = {.index = 23, .length = 2},
  [17] = {.index = 25, .length = 3},
  [19] = {.index = 28, .length = 2},
  [21] = {.index = 30, .length = 4},
  [22] = {.index = 34, .length = 2},
  [23] = {.index = 36, .length = 3},
  [24] = {.index = 39, .length = 1},
  [25] = {.index = 40, .length = 3},
  [26] = {.index = 43, .length = 2},
  [27] = {.index = 45, .length = 4},
  [28] = {.index = 49, .length = 5},
  [29] = {.index = 54, .length = 4},
  [30] = {.index = 58, .length = 4},
  [31] = {.index = 62, .length = 5},
  [33] = {.index = 67, .length = 1},
  [34] = {.index = 68, .length = 5},
  [35] = {.index = 73, .length = 6},
  [36] = {.index = 67, .length = 1},
  [37] = {.index = 79, .length = 1},
};

static const TSFieldMapEntry ts_field_map_entries[] = {
  [0] =
    {field_path, 0},
  [1] =
    {field_name, 1},
  [2] =
    {field_lhs, 1},
    {field_op, 0},
  [4] =
    {field_header, 0},
  [5] =
    {field_attribs, 1},
    {field_header, 0},
  [7] =
    {field_tail, 1},
  [8] =
    {field_name, 1},
    {field_type, 0},
  [10] =
    {field_end, 1},
  [11] =
    {field_name, 0},
  [12] =
    {field_lhs, 0},
    {field_op, 1},
    {field_rhs, 2},
  [15] =
    {field_alias, 2},
    {field_path, 0},
  [17] =
    {field_tail, 2},
  [18] =
    {field_arg, 2},
    {field_op, 0},
  [20] =
    {field_child, 2},
    {field_child, 3},
    {field_header, 0},
  [23] =
    {field_cardinality, 2},
    {field_header, 0},
  [25] =
    {field_attribs, 3},
    {field_cardinality, 2},
    {field_header, 0},
  [28] =
    {field_name, 0},
    {field_value, 1},
  [30] =
    {field_attribs, 1},
    {field_child, 2},
    {field_child, 3},
    {field_header, 0},
  [34] =
    {field_begin, 1},
    {field_end, 3},
  [36] =
    {field_arg, 2},
    {field_op, 0},
    {field_tail, 3},
  [39] =
    {field_arg, 1},
  [40] =
    {field_arg, 2},
    {field_arg, 3, .inherited = true},
    {field_op, 0},
  [43] =
    {field_arg, 0, .inherited = true},
    {field_arg, 1, .inherited = true},
  [45] =
    {field_child, 2},
    {field_child, 3},
    {field_child, 4},
    {field_header, 0},
  [49] =
    {field_attribs, 1},
    {field_child, 2},
    {field_child, 3},
    {field_child, 4},
    {field_header, 0},
  [54] =
    {field_arg, 2},
    {field_arg, 3, .inherited = true},
    {field_op, 0},
    {field_tail, 4},
  [58] =
    {field_cardinality, 2},
    {field_child, 4},
    {field_child, 5},
    {field_header, 0},
  [62] =
    {field_attribs, 3},
    {field_cardinality, 2},
    {field_child, 4},
    {field_child, 5},
    {field_header, 0},
  [67] =
    {field_tail, 3},
  [68] =
    {field_cardinality, 2},
    {field_child, 4},
    {field_child, 5},
    {field_child, 6},
    {field_header, 0},
  [73] =
    {field_attribs, 3},
    {field_cardinality, 2},
    {field_child, 4},
    {field_child, 5},
    {field_child, 6},
    {field_header, 0},
  [79] =
    {field_tail, 4},
};

static const TSSymbol ts_alias_sequences[PRODUCTION_ID_COUNT][MAX_ALIAS_SEQUENCE_LENGTH] = {
  [0] = {0},
  [1] = {
    [0] = alias_sym_constraint,
  },
  [18] = {
    [1] = alias_sym_constraint,
  },
  [20] = {
    [0] = alias_sym_attrib_expr,
  },
  [32] = {
    [2] = alias_sym_constraint,
  },
  [36] = {
    [2] = alias_sym_constraint,
  },
  [37] = {
    [2] = alias_sym_constraint,
  },
};

static const uint16_t ts_non_terminal_alias_map[] = {
  sym__expr, 3,
    sym__expr,
    alias_sym_attrib_expr,
    alias_sym_constraint,
  0,
};

static const TSStateId ts_primary_state_ids[STATE_COUNT] = {
  [0] = 0,
  [1] = 1,
  [2] = 2,
  [3] = 2,
  [4] = 4,
  [5] = 5,
  [6] = 6,
  [7] = 7,
  [8] = 8,
  [9] = 9,
  [10] = 10,
  [11] = 11,
  [12] = 8,
  [13] = 13,
  [14] = 6,
  [15] = 11,
  [16] = 7,
  [17] = 13,
  [18] = 9,
  [19] = 4,
  [20] = 5,
  [21] = 21,
  [22] = 22,
  [23] = 23,
  [24] = 24,
  [25] = 25,
  [26] = 26,
  [27] = 27,
  [28] = 26,
  [29] = 27,
  [30] = 23,
  [31] = 31,
  [32] = 25,
  [33] = 31,
  [34] = 34,
  [35] = 22,
  [36] = 36,
  [37] = 36,
  [38] = 24,
  [39] = 21,
  [40] = 40,
  [41] = 41,
  [42] = 42,
  [43] = 43,
  [44] = 44,
  [45] = 44,
  [46] = 41,
  [47] = 47,
  [48] = 48,
  [49] = 40,
  [50] = 50,
  [51] = 43,
  [52] = 50,
  [53] = 47,
  [54] = 48,
  [55] = 42,
  [56] = 56,
  [57] = 57,
  [58] = 58,
  [59] = 59,
  [60] = 57,
  [61] = 59,
  [62] = 62,
  [63] = 62,
  [64] = 64,
  [65] = 65,
  [66] = 66,
  [67] = 67,
  [68] = 67,
  [69] = 69,
  [70] = 70,
  [71] = 71,
  [72] = 72,
  [73] = 71,
  [74] = 71,
  [75] = 71,
  [76] = 67,
  [77] = 67,
  [78] = 78,
  [79] = 79,
  [80] = 80,
  [81] = 80,
  [82] = 82,
  [83] = 82,
  [84] = 84,
  [85] = 85,
  [86] = 86,
  [87] = 87,
  [88] = 87,
  [89] = 89,
  [90] = 90,
  [91] = 85,
  [92] = 89,
  [93] = 90,
  [94] = 80,
  [95] = 84,
  [96] = 85,
  [97] = 85,
  [98] = 90,
  [99] = 89,
  [100] = 100,
  [101] = 87,
  [102] = 82,
  [103] = 80,
  [104] = 90,
  [105] = 89,
  [106] = 87,
  [107] = 84,
  [108] = 108,
  [109] = 58,
  [110] = 110,
  [111] = 82,
  [112] = 112,
  [113] = 84,
  [114] = 108,
  [115] = 72,
  [116] = 108,
  [117] = 108,
  [118] = 72,
  [119] = 72,
  [120] = 120,
  [121] = 121,
  [122] = 122,
  [123] = 123,
  [124] = 124,
  [125] = 125,
  [126] = 70,
  [127] = 70,
  [128] = 128,
  [129] = 120,
  [130] = 121,
  [131] = 121,
  [132] = 120,
  [133] = 121,
  [134] = 124,
  [135] = 124,
  [136] = 70,
  [137] = 120,
  [138] = 124,
  [139] = 139,
  [140] = 140,
  [141] = 141,
  [142] = 142,
  [143] = 143,
  [144] = 144,
  [145] = 145,
  [146] = 123,
  [147] = 143,
  [148] = 123,
  [149] = 149,
  [150] = 150,
  [151] = 151,
  [152] = 152,
  [153] = 153,
  [154] = 154,
  [155] = 123,
  [156] = 156,
  [157] = 58,
  [158] = 143,
  [159] = 58,
  [160] = 160,
  [161] = 143,
  [162] = 162,
  [163] = 154,
  [164] = 156,
  [165] = 149,
  [166] = 153,
  [167] = 145,
  [168] = 144,
  [169] = 140,
  [170] = 150,
  [171] = 154,
  [172] = 151,
  [173] = 150,
  [174] = 140,
  [175] = 142,
  [176] = 162,
  [177] = 177,
  [178] = 178,
  [179] = 144,
  [180] = 139,
  [181] = 141,
  [182] = 145,
  [183] = 162,
  [184] = 156,
  [185] = 178,
  [186] = 153,
  [187] = 187,
  [188] = 139,
  [189] = 149,
  [190] = 151,
  [191] = 149,
  [192] = 151,
  [193] = 141,
  [194] = 153,
  [195] = 142,
  [196] = 156,
  [197] = 141,
  [198] = 139,
  [199] = 199,
  [200] = 162,
  [201] = 145,
  [202] = 144,
  [203] = 142,
  [204] = 140,
  [205] = 154,
  [206] = 150,
  [207] = 207,
  [208] = 207,
  [209] = 207,
  [210] = 207,
  [211] = 211,
  [212] = 211,
  [213] = 213,
  [214] = 211,
  [215] = 215,
  [216] = 215,
  [217] = 213,
  [218] = 213,
  [219] = 213,
  [220] = 215,
  [221] = 211,
  [222] = 215,
  [223] = 223,
  [224] = 224,
  [225] = 225,
  [226] = 226,
  [227] = 227,
  [228] = 228,
  [229] = 229,
  [230] = 230,
  [231] = 231,
  [232] = 231,
  [233] = 231,
  [234] = 229,
  [235] = 231,
  [236] = 236,
  [237] = 237,
  [238] = 238,
  [239] = 239,
  [240] = 240,
  [241] = 241,
  [242] = 242,
  [243] = 243,
  [244] = 244,
  [245] = 243,
  [246] = 246,
  [247] = 247,
  [248] = 239,
  [249] = 249,
  [250] = 250,
  [251] = 243,
  [252] = 252,
  [253] = 253,
  [254] = 239,
  [255] = 249,
  [256] = 256,
  [257] = 257,
  [258] = 258,
  [259] = 259,
  [260] = 260,
  [261] = 249,
  [262] = 249,
  [263] = 263,
  [264] = 239,
  [265] = 260,
  [266] = 258,
  [267] = 243,
  [268] = 253,
  [269] = 25,
  [270] = 270,
  [271] = 271,
  [272] = 272,
  [273] = 273,
  [274] = 274,
  [275] = 275,
  [276] = 276,
  [277] = 277,
  [278] = 278,
  [279] = 23,
  [280] = 280,
  [281] = 281,
  [282] = 270,
  [283] = 283,
  [284] = 27,
  [285] = 277,
  [286] = 286,
  [287] = 31,
  [288] = 280,
  [289] = 289,
  [290] = 26,
  [291] = 275,
  [292] = 25,
  [293] = 271,
  [294] = 23,
  [295] = 31,
  [296] = 27,
  [297] = 297,
  [298] = 26,
  [299] = 299,
  [300] = 300,
  [301] = 301,
  [302] = 300,
  [303] = 303,
  [304] = 304,
  [305] = 305,
  [306] = 306,
  [307] = 305,
  [308] = 306,
  [309] = 299,
  [310] = 310,
  [311] = 300,
  [312] = 306,
  [313] = 305,
  [314] = 299,
  [315] = 299,
  [316] = 306,
  [317] = 305,
  [318] = 300,
};

static inline bool sym_name_character_set_1(int32_t c) {
  return (c < 43514
    ? (c < 4193
      ? (c < 2707
        ? (c < 1994
          ? (c < 931
            ? (c < 748
              ? (c < 192
                ? (c < 170
                  ? (c < 'b'
                    ? (c >= 'A' && c <= 'Z')
                    : c <= 'z')
                  : (c <= 170 || (c < 186
                    ? c == 181
                    : c <= 186)))
                : (c <= 214 || (c < 710
                  ? (c < 248
                    ? (c >= 216 && c <= 246)
                    : c <= 705)
                  : (c <= 721 || (c >= 736 && c <= 740)))))
              : (c <= 748 || (c < 895
                ? (c < 886
                  ? (c < 880
                    ? c == 750
                    : c <= 884)
                  : (c <= 887 || (c >= 891 && c <= 893)))
                : (c <= 895 || (c < 908
                  ? (c < 904
                    ? c == 902
                    : c <= 906)
                  : (c <= 908 || (c >= 910 && c <= 929)))))))
            : (c <= 1013 || (c < 1649
              ? (c < 1376
                ? (c < 1329
                  ? (c < 1162
                    ? (c >= 1015 && c <= 1153)
                    : c <= 1327)
                  : (c <= 1366 || c == 1369))
                : (c <= 1416 || (c < 1568
                  ? (c < 1519
                    ? (c >= 1488 && c <= 1514)
                    : c <= 1522)
                  : (c <= 1610 || (c >= 1646 && c <= 1647)))))
              : (c <= 1747 || (c < 1791
                ? (c < 1774
                  ? (c < 1765
                    ? c == 1749
                    : c <= 1766)
                  : (c <= 1775 || (c >= 1786 && c <= 1788)))
                : (c <= 1791 || (c < 1869
                  ? (c < 1810
                    ? c == 1808
                    : c <= 1839)
                  : (c <= 1957 || c == 1969))))))))
          : (c <= 2026 || (c < 2482
            ? (c < 2208
              ? (c < 2088
                ? (c < 2048
                  ? (c < 2042
                    ? (c >= 2036 && c <= 2037)
                    : c <= 2042)
                  : (c <= 2069 || (c < 2084
                    ? c == 2074
                    : c <= 2084)))
                : (c <= 2088 || (c < 2160
                  ? (c < 2144
                    ? (c >= 2112 && c <= 2136)
                    : c <= 2154)
                  : (c <= 2183 || (c >= 2185 && c <= 2190)))))
              : (c <= 2249 || (c < 2417
                ? (c < 2384
                  ? (c < 2365
                    ? (c >= 2308 && c <= 2361)
                    : c <= 2365)
                  : (c <= 2384 || (c >= 2392 && c <= 2401)))
                : (c <= 2432 || (c < 2451
                  ? (c < 2447
                    ? (c >= 2437 && c <= 2444)
                    : c <= 2448)
                  : (c <= 2472 || (c >= 2474 && c <= 2480)))))))
            : (c <= 2482 || (c < 2579
              ? (c < 2527
                ? (c < 2510
                  ? (c < 2493
                    ? (c >= 2486 && c <= 2489)
                    : c <= 2493)
                  : (c <= 2510 || (c >= 2524 && c <= 2525)))
                : (c <= 2529 || (c < 2565
                  ? (c < 2556
                    ? (c >= 2544 && c <= 2545)
                    : c <= 2556)
                  : (c <= 2570 || (c >= 2575 && c <= 2576)))))
              : (c <= 2600 || (c < 2649
                ? (c < 2613
                  ? (c < 2610
                    ? (c >= 2602 && c <= 2608)
                    : c <= 2611)
                  : (c <= 2614 || (c >= 2616 && c <= 2617)))
                : (c <= 2652 || (c < 2693
                  ? (c < 2674
                    ? c == 2654
                    : c <= 2676)
                  : (c <= 2701 || (c >= 2703 && c <= 2705)))))))))))
        : (c <= 2728 || (c < 3242
          ? (c < 2962
            ? (c < 2858
              ? (c < 2784
                ? (c < 2741
                  ? (c < 2738
                    ? (c >= 2730 && c <= 2736)
                    : c <= 2739)
                  : (c <= 2745 || (c < 2768
                    ? c == 2749
                    : c <= 2768)))
                : (c <= 2785 || (c < 2831
                  ? (c < 2821
                    ? c == 2809
                    : c <= 2828)
                  : (c <= 2832 || (c >= 2835 && c <= 2856)))))
              : (c <= 2864 || (c < 2911
                ? (c < 2877
                  ? (c < 2869
                    ? (c >= 2866 && c <= 2867)
                    : c <= 2873)
                  : (c <= 2877 || (c >= 2908 && c <= 2909)))
                : (c <= 2913 || (c < 2949
                  ? (c < 2947
                    ? c == 2929
                    : c <= 2947)
                  : (c <= 2954 || (c >= 2958 && c <= 2960)))))))
            : (c <= 2965 || (c < 3090
              ? (c < 2984
                ? (c < 2974
                  ? (c < 2972
                    ? (c >= 2969 && c <= 2970)
                    : c <= 2972)
                  : (c <= 2975 || (c >= 2979 && c <= 2980)))
                : (c <= 2986 || (c < 3077
                  ? (c < 3024
                    ? (c >= 2990 && c <= 3001)
                    : c <= 3024)
                  : (c <= 3084 || (c >= 3086 && c <= 3088)))))
              : (c <= 3112 || (c < 3168
                ? (c < 3160
                  ? (c < 3133
                    ? (c >= 3114 && c <= 3129)
                    : c <= 3133)
                  : (c <= 3162 || c == 3165))
                : (c <= 3169 || (c < 3214
                  ? (c < 3205
                    ? c == 3200
                    : c <= 3212)
                  : (c <= 3216 || (c >= 3218 && c <= 3240)))))))))
          : (c <= 3251 || (c < 3648
            ? (c < 3412
              ? (c < 3332
                ? (c < 3293
                  ? (c < 3261
                    ? (c >= 3253 && c <= 3257)
                    : c <= 3261)
                  : (c <= 3294 || (c < 3313
                    ? (c >= 3296 && c <= 3297)
                    : c <= 3314)))
                : (c <= 3340 || (c < 3389
                  ? (c < 3346
                    ? (c >= 3342 && c <= 3344)
                    : c <= 3386)
                  : (c <= 3389 || c == 3406))))
              : (c <= 3414 || (c < 3507
                ? (c < 3461
                  ? (c < 3450
                    ? (c >= 3423 && c <= 3425)
                    : c <= 3455)
                  : (c <= 3478 || (c >= 3482 && c <= 3505)))
                : (c <= 3515 || (c < 3585
                  ? (c < 3520
                    ? c == 3517
                    : c <= 3526)
                  : (c <= 3632 || c == 3634))))))
            : (c <= 3654 || (c < 3782
              ? (c < 3749
                ? (c < 3718
                  ? (c < 3716
                    ? (c >= 3713 && c <= 3714)
                    : c <= 3716)
                  : (c <= 3722 || (c >= 3724 && c <= 3747)))
                : (c <= 3749 || (c < 3773
                  ? (c < 3762
                    ? (c >= 3751 && c <= 3760)
                    : c <= 3762)
                  : (c <= 3773 || (c >= 3776 && c <= 3780)))))
              : (c <= 3782 || (c < 3976
                ? (c < 3904
                  ? (c < 3840
                    ? (c >= 3804 && c <= 3807)
                    : c <= 3840)
                  : (c <= 3911 || (c >= 3913 && c <= 3948)))
                : (c <= 3980 || (c < 4176
                  ? (c < 4159
                    ? (c >= 4096 && c <= 4138)
                    : c <= 4159)
                  : (c <= 4181 || (c >= 4186 && c <= 4189)))))))))))))
      : (c <= 4193 || (c < 8134
        ? (c < 6176
          ? (c < 4808
            ? (c < 4688
              ? (c < 4295
                ? (c < 4213
                  ? (c < 4206
                    ? (c >= 4197 && c <= 4198)
                    : c <= 4208)
                  : (c <= 4225 || (c < 4256
                    ? c == 4238
                    : c <= 4293)))
                : (c <= 4295 || (c < 4348
                  ? (c < 4304
                    ? c == 4301
                    : c <= 4346)
                  : (c <= 4680 || (c >= 4682 && c <= 4685)))))
              : (c <= 4694 || (c < 4752
                ? (c < 4704
                  ? (c < 4698
                    ? c == 4696
                    : c <= 4701)
                  : (c <= 4744 || (c >= 4746 && c <= 4749)))
                : (c <= 4784 || (c < 4800
                  ? (c < 4792
                    ? (c >= 4786 && c <= 4789)
                    : c <= 4798)
                  : (c <= 4800 || (c >= 4802 && c <= 4805)))))))
            : (c <= 4822 || (c < 5792
              ? (c < 5024
                ? (c < 4888
                  ? (c < 4882
                    ? (c >= 4824 && c <= 4880)
                    : c <= 4885)
                  : (c <= 4954 || (c >= 4992 && c <= 5007)))
                : (c <= 5109 || (c < 5743
                  ? (c < 5121
                    ? (c >= 5112 && c <= 5117)
                    : c <= 5740)
                  : (c <= 5759 || (c >= 5761 && c <= 5786)))))
              : (c <= 5866 || (c < 5984
                ? (c < 5919
                  ? (c < 5888
                    ? (c >= 5870 && c <= 5880)
                    : c <= 5905)
                  : (c <= 5937 || (c >= 5952 && c <= 5969)))
                : (c <= 5996 || (c < 6103
                  ? (c < 6016
                    ? (c >= 5998 && c <= 6000)
                    : c <= 6067)
                  : (c <= 6103 || c == 6108))))))))
          : (c <= 6264 || (c < 7312
            ? (c < 6823
              ? (c < 6512
                ? (c < 6320
                  ? (c < 6314
                    ? (c >= 6272 && c <= 6312)
                    : c <= 6314)
                  : (c <= 6389 || (c < 6480
                    ? (c >= 6400 && c <= 6430)
                    : c <= 6509)))
                : (c <= 6516 || (c < 6656
                  ? (c < 6576
                    ? (c >= 6528 && c <= 6571)
                    : c <= 6601)
                  : (c <= 6678 || (c >= 6688 && c <= 6740)))))
              : (c <= 6823 || (c < 7098
                ? (c < 7043
                  ? (c < 6981
                    ? (c >= 6917 && c <= 6963)
                    : c <= 6988)
                  : (c <= 7072 || (c >= 7086 && c <= 7087)))
                : (c <= 7141 || (c < 7258
                  ? (c < 7245
                    ? (c >= 7168 && c <= 7203)
                    : c <= 7247)
                  : (c <= 7293 || (c >= 7296 && c <= 7304)))))))
            : (c <= 7354 || (c < 8008
              ? (c < 7418
                ? (c < 7406
                  ? (c < 7401
                    ? (c >= 7357 && c <= 7359)
                    : c <= 7404)
                  : (c <= 7411 || (c >= 7413 && c <= 7414)))
                : (c <= 7418 || (c < 7960
                  ? (c < 7680
                    ? (c >= 7424 && c <= 7615)
                    : c <= 7957)
                  : (c <= 7965 || (c >= 7968 && c <= 8005)))))
              : (c <= 8013 || (c < 8031
                ? (c < 8027
                  ? (c < 8025
                    ? (c >= 8016 && c <= 8023)
                    : c <= 8025)
                  : (c <= 8027 || c == 8029))
                : (c <= 8061 || (c < 8126
                  ? (c < 8118
                    ? (c >= 8064 && c <= 8116)
                    : c <= 8124)
                  : (c <= 8126 || (c >= 8130 && c <= 8132)))))))))))
        : (c <= 8140 || (c < 12337
          ? (c < 8544
            ? (c < 8458
              ? (c < 8305
                ? (c < 8160
                  ? (c < 8150
                    ? (c >= 8144 && c <= 8147)
                    : c <= 8155)
                  : (c <= 8172 || (c < 8182
                    ? (c >= 8178 && c <= 8180)
                    : c <= 8188)))
                : (c <= 8305 || (c < 8450
                  ? (c < 8336
                    ? c == 8319
                    : c <= 8348)
                  : (c <= 8450 || c == 8455))))
              : (c <= 8467 || (c < 8488
                ? (c < 8484
                  ? (c < 8472
                    ? c == 8469
                    : c <= 8477)
                  : (c <= 8484 || c == 8486))
                : (c <= 8488 || (c < 8517
                  ? (c < 8508
                    ? (c >= 8490 && c <= 8505)
                    : c <= 8511)
                  : (c <= 8521 || c == 8526))))))
            : (c <= 8584 || (c < 11680
              ? (c < 11559
                ? (c < 11506
                  ? (c < 11499
                    ? (c >= 11264 && c <= 11492)
                    : c <= 11502)
                  : (c <= 11507 || (c >= 11520 && c <= 11557)))
                : (c <= 11559 || (c < 11631
                  ? (c < 11568
                    ? c == 11565
                    : c <= 11623)
                  : (c <= 11631 || (c >= 11648 && c <= 11670)))))
              : (c <= 11686 || (c < 11720
                ? (c < 11704
                  ? (c < 11696
                    ? (c >= 11688 && c <= 11694)
                    : c <= 11702)
                  : (c <= 11710 || (c >= 11712 && c <= 11718)))
                : (c <= 11726 || (c < 12293
                  ? (c < 11736
                    ? (c >= 11728 && c <= 11734)
                    : c <= 11742)
                  : (c <= 12295 || (c >= 12321 && c <= 12329)))))))))
          : (c <= 12341 || (c < 42891
            ? (c < 19968
              ? (c < 12549
                ? (c < 12445
                  ? (c < 12353
                    ? (c >= 12344 && c <= 12348)
                    : c <= 12438)
                  : (c <= 12447 || (c < 12540
                    ? (c >= 12449 && c <= 12538)
                    : c <= 12543)))
                : (c <= 12591 || (c < 12784
                  ? (c < 12704
                    ? (c >= 12593 && c <= 12686)
                    : c <= 12735)
                  : (c <= 12799 || (c >= 13312 && c <= 19903)))))
              : (c <= 42124 || (c < 42560
                ? (c < 42512
                  ? (c < 42240
                    ? (c >= 42192 && c <= 42237)
                    : c <= 42508)
                  : (c <= 42527 || (c >= 42538 && c <= 42539)))
                : (c <= 42606 || (c < 42775
                  ? (c < 42656
                    ? (c >= 42623 && c <= 42653)
                    : c <= 42735)
                  : (c <= 42783 || (c >= 42786 && c <= 42888)))))))
            : (c <= 42954 || (c < 43250
              ? (c < 43011
                ? (c < 42965
                  ? (c < 42963
                    ? (c >= 42960 && c <= 42961)
                    : c <= 42963)
                  : (c <= 42969 || (c >= 42994 && c <= 43009)))
                : (c <= 43013 || (c < 43072
                  ? (c < 43020
                    ? (c >= 43015 && c <= 43018)
                    : c <= 43042)
                  : (c <= 43123 || (c >= 43138 && c <= 43187)))))
              : (c <= 43255 || (c < 43360
                ? (c < 43274
                  ? (c < 43261
                    ? c == 43259
                    : c <= 43262)
                  : (c <= 43301 || (c >= 43312 && c <= 43334)))
                : (c <= 43388 || (c < 43488
                  ? (c < 43471
                    ? (c >= 43396 && c <= 43442)
                    : c <= 43471)
                  : (c <= 43492 || (c >= 43494 && c <= 43503)))))))))))))))
    : (c <= 43518 || (c < 70727
      ? (c < 66956
        ? (c < 64914
          ? (c < 43868
            ? (c < 43714
              ? (c < 43646
                ? (c < 43588
                  ? (c < 43584
                    ? (c >= 43520 && c <= 43560)
                    : c <= 43586)
                  : (c <= 43595 || (c < 43642
                    ? (c >= 43616 && c <= 43638)
                    : c <= 43642)))
                : (c <= 43695 || (c < 43705
                  ? (c < 43701
                    ? c == 43697
                    : c <= 43702)
                  : (c <= 43709 || c == 43712))))
              : (c <= 43714 || (c < 43785
                ? (c < 43762
                  ? (c < 43744
                    ? (c >= 43739 && c <= 43741)
                    : c <= 43754)
                  : (c <= 43764 || (c >= 43777 && c <= 43782)))
                : (c <= 43790 || (c < 43816
                  ? (c < 43808
                    ? (c >= 43793 && c <= 43798)
                    : c <= 43814)
                  : (c <= 43822 || (c >= 43824 && c <= 43866)))))))
            : (c <= 43881 || (c < 64287
              ? (c < 63744
                ? (c < 55216
                  ? (c < 44032
                    ? (c >= 43888 && c <= 44002)
                    : c <= 55203)
                  : (c <= 55238 || (c >= 55243 && c <= 55291)))
                : (c <= 64109 || (c < 64275
                  ? (c < 64256
                    ? (c >= 64112 && c <= 64217)
                    : c <= 64262)
                  : (c <= 64279 || c == 64285))))
              : (c <= 64296 || (c < 64323
                ? (c < 64318
                  ? (c < 64312
                    ? (c >= 64298 && c <= 64310)
                    : c <= 64316)
                  : (c <= 64318 || (c >= 64320 && c <= 64321)))
                : (c <= 64324 || (c < 64612
                  ? (c < 64467
                    ? (c >= 64326 && c <= 64433)
                    : c <= 64605)
                  : (c <= 64829 || (c >= 64848 && c <= 64911)))))))))
          : (c <= 64967 || (c < 65599
            ? (c < 65382
              ? (c < 65147
                ? (c < 65139
                  ? (c < 65137
                    ? (c >= 65008 && c <= 65017)
                    : c <= 65137)
                  : (c <= 65139 || (c < 65145
                    ? c == 65143
                    : c <= 65145)))
                : (c <= 65147 || (c < 65313
                  ? (c < 65151
                    ? c == 65149
                    : c <= 65276)
                  : (c <= 65338 || (c >= 65345 && c <= 65370)))))
              : (c <= 65437 || (c < 65498
                ? (c < 65482
                  ? (c < 65474
                    ? (c >= 65440 && c <= 65470)
                    : c <= 65479)
                  : (c <= 65487 || (c >= 65490 && c <= 65495)))
                : (c <= 65500 || (c < 65576
                  ? (c < 65549
                    ? (c >= 65536 && c <= 65547)
                    : c <= 65574)
                  : (c <= 65594 || (c >= 65596 && c <= 65597)))))))
            : (c <= 65613 || (c < 66464
              ? (c < 66208
                ? (c < 65856
                  ? (c < 65664
                    ? (c >= 65616 && c <= 65629)
                    : c <= 65786)
                  : (c <= 65908 || (c >= 66176 && c <= 66204)))
                : (c <= 66256 || (c < 66384
                  ? (c < 66349
                    ? (c >= 66304 && c <= 66335)
                    : c <= 66378)
                  : (c <= 66421 || (c >= 66432 && c <= 66461)))))
              : (c <= 66499 || (c < 66776
                ? (c < 66560
                  ? (c < 66513
                    ? (c >= 66504 && c <= 66511)
                    : c <= 66517)
                  : (c <= 66717 || (c >= 66736 && c <= 66771)))
                : (c <= 66811 || (c < 66928
                  ? (c < 66864
                    ? (c >= 66816 && c <= 66855)
                    : c <= 66915)
                  : (c <= 66938 || (c >= 66940 && c <= 66954)))))))))))
        : (c <= 66962 || (c < 68864
          ? (c < 67828
            ? (c < 67506
              ? (c < 67072
                ? (c < 66979
                  ? (c < 66967
                    ? (c >= 66964 && c <= 66965)
                    : c <= 66977)
                  : (c <= 66993 || (c < 67003
                    ? (c >= 66995 && c <= 67001)
                    : c <= 67004)))
                : (c <= 67382 || (c < 67456
                  ? (c < 67424
                    ? (c >= 67392 && c <= 67413)
                    : c <= 67431)
                  : (c <= 67461 || (c >= 67463 && c <= 67504)))))
              : (c <= 67514 || (c < 67644
                ? (c < 67594
                  ? (c < 67592
                    ? (c >= 67584 && c <= 67589)
                    : c <= 67592)
                  : (c <= 67637 || (c >= 67639 && c <= 67640)))
                : (c <= 67644 || (c < 67712
                  ? (c < 67680
                    ? (c >= 67647 && c <= 67669)
                    : c <= 67702)
                  : (c <= 67742 || (c >= 67808 && c <= 67826)))))))
            : (c <= 67829 || (c < 68224
              ? (c < 68096
                ? (c < 67968
                  ? (c < 67872
                    ? (c >= 67840 && c <= 67861)
                    : c <= 67897)
                  : (c <= 68023 || (c >= 68030 && c <= 68031)))
                : (c <= 68096 || (c < 68121
                  ? (c < 68117
                    ? (c >= 68112 && c <= 68115)
                    : c <= 68119)
                  : (c <= 68149 || (c >= 68192 && c <= 68220)))))
              : (c <= 68252 || (c < 68448
                ? (c < 68352
                  ? (c < 68297
                    ? (c >= 68288 && c <= 68295)
                    : c <= 68324)
                  : (c <= 68405 || (c >= 68416 && c <= 68437)))
                : (c <= 68466 || (c < 68736
                  ? (c < 68608
                    ? (c >= 68480 && c <= 68497)
                    : c <= 68680)
                  : (c <= 68786 || (c >= 68800 && c <= 68850)))))))))
          : (c <= 68899 || (c < 70106
            ? (c < 69749
              ? (c < 69488
                ? (c < 69376
                  ? (c < 69296
                    ? (c >= 69248 && c <= 69289)
                    : c <= 69297)
                  : (c <= 69404 || (c < 69424
                    ? c == 69415
                    : c <= 69445)))
                : (c <= 69505 || (c < 69635
                  ? (c < 69600
                    ? (c >= 69552 && c <= 69572)
                    : c <= 69622)
                  : (c <= 69687 || (c >= 69745 && c <= 69746)))))
              : (c <= 69749 || (c < 69959
                ? (c < 69891
                  ? (c < 69840
                    ? (c >= 69763 && c <= 69807)
                    : c <= 69864)
                  : (c <= 69926 || c == 69956))
                : (c <= 69959 || (c < 70019
                  ? (c < 70006
                    ? (c >= 69968 && c <= 70002)
                    : c <= 70006)
                  : (c <= 70066 || (c >= 70081 && c <= 70084)))))))
            : (c <= 70106 || (c < 70405
              ? (c < 70280
                ? (c < 70163
                  ? (c < 70144
                    ? c == 70108
                    : c <= 70161)
                  : (c <= 70187 || (c >= 70272 && c <= 70278)))
                : (c <= 70280 || (c < 70303
                  ? (c < 70287
                    ? (c >= 70282 && c <= 70285)
                    : c <= 70301)
                  : (c <= 70312 || (c >= 70320 && c <= 70366)))))
              : (c <= 70412 || (c < 70453
                ? (c < 70442
                  ? (c < 70419
                    ? (c >= 70415 && c <= 70416)
                    : c <= 70440)
                  : (c <= 70448 || (c >= 70450 && c <= 70451)))
                : (c <= 70457 || (c < 70493
                  ? (c < 70480
                    ? c == 70461
                    : c <= 70480)
                  : (c <= 70497 || (c >= 70656 && c <= 70708)))))))))))))
      : (c <= 70730 || (c < 119894
        ? (c < 73056
          ? (c < 72001
            ? (c < 71424
              ? (c < 71128
                ? (c < 70852
                  ? (c < 70784
                    ? (c >= 70751 && c <= 70753)
                    : c <= 70831)
                  : (c <= 70853 || (c < 71040
                    ? c == 70855
                    : c <= 71086)))
                : (c <= 71131 || (c < 71296
                  ? (c < 71236
                    ? (c >= 71168 && c <= 71215)
                    : c <= 71236)
                  : (c <= 71338 || c == 71352))))
              : (c <= 71450 || (c < 71945
                ? (c < 71840
                  ? (c < 71680
                    ? (c >= 71488 && c <= 71494)
                    : c <= 71723)
                  : (c <= 71903 || (c >= 71935 && c <= 71942)))
                : (c <= 71945 || (c < 71960
                  ? (c < 71957
                    ? (c >= 71948 && c <= 71955)
                    : c <= 71958)
                  : (c <= 71983 || c == 71999))))))
            : (c <= 72001 || (c < 72349
              ? (c < 72192
                ? (c < 72161
                  ? (c < 72106
                    ? (c >= 72096 && c <= 72103)
                    : c <= 72144)
                  : (c <= 72161 || c == 72163))
                : (c <= 72192 || (c < 72272
                  ? (c < 72250
                    ? (c >= 72203 && c <= 72242)
                    : c <= 72250)
                  : (c <= 72272 || (c >= 72284 && c <= 72329)))))
              : (c <= 72349 || (c < 72818
                ? (c < 72714
                  ? (c < 72704
                    ? (c >= 72368 && c <= 72440)
                    : c <= 72712)
                  : (c <= 72750 || c == 72768))
                : (c <= 72847 || (c < 72971
                  ? (c < 72968
                    ? (c >= 72960 && c <= 72966)
                    : c <= 72969)
                  : (c <= 73008 || c == 73030))))))))
          : (c <= 73061 || (c < 93952
            ? (c < 82944
              ? (c < 73728
                ? (c < 73112
                  ? (c < 73066
                    ? (c >= 73063 && c <= 73064)
                    : c <= 73097)
                  : (c <= 73112 || (c < 73648
                    ? (c >= 73440 && c <= 73458)
                    : c <= 73648)))
                : (c <= 74649 || (c < 77712
                  ? (c < 74880
                    ? (c >= 74752 && c <= 74862)
                    : c <= 75075)
                  : (c <= 77808 || (c >= 77824 && c <= 78894)))))
              : (c <= 83526 || (c < 92928
                ? (c < 92784
                  ? (c < 92736
                    ? (c >= 92160 && c <= 92728)
                    : c <= 92766)
                  : (c <= 92862 || (c >= 92880 && c <= 92909)))
                : (c <= 92975 || (c < 93053
                  ? (c < 93027
                    ? (c >= 92992 && c <= 92995)
                    : c <= 93047)
                  : (c <= 93071 || (c >= 93760 && c <= 93823)))))))
            : (c <= 94026 || (c < 110589
              ? (c < 94208
                ? (c < 94176
                  ? (c < 94099
                    ? c == 94032
                    : c <= 94111)
                  : (c <= 94177 || c == 94179))
                : (c <= 100343 || (c < 110576
                  ? (c < 101632
                    ? (c >= 100352 && c <= 101589)
                    : c <= 101640)
                  : (c <= 110579 || (c >= 110581 && c <= 110587)))))
              : (c <= 110590 || (c < 113664
                ? (c < 110948
                  ? (c < 110928
                    ? (c >= 110592 && c <= 110882)
                    : c <= 110930)
                  : (c <= 110951 || (c >= 110960 && c <= 111355)))
                : (c <= 113770 || (c < 113808
                  ? (c < 113792
                    ? (c >= 113776 && c <= 113788)
                    : c <= 113800)
                  : (c <= 113817 || (c >= 119808 && c <= 119892)))))))))))
        : (c <= 119964 || (c < 125259
          ? (c < 120572
            ? (c < 120086
              ? (c < 119995
                ? (c < 119973
                  ? (c < 119970
                    ? (c >= 119966 && c <= 119967)
                    : c <= 119970)
                  : (c <= 119974 || (c < 119982
                    ? (c >= 119977 && c <= 119980)
                    : c <= 119993)))
                : (c <= 119995 || (c < 120071
                  ? (c < 120005
                    ? (c >= 119997 && c <= 120003)
                    : c <= 120069)
                  : (c <= 120074 || (c >= 120077 && c <= 120084)))))
              : (c <= 120092 || (c < 120138
                ? (c < 120128
                  ? (c < 120123
                    ? (c >= 120094 && c <= 120121)
                    : c <= 120126)
                  : (c <= 120132 || c == 120134))
                : (c <= 120144 || (c < 120514
                  ? (c < 120488
                    ? (c >= 120146 && c <= 120485)
                    : c <= 120512)
                  : (c <= 120538 || (c >= 120540 && c <= 120570)))))))
            : (c <= 120596 || (c < 123191
              ? (c < 120714
                ? (c < 120656
                  ? (c < 120630
                    ? (c >= 120598 && c <= 120628)
                    : c <= 120654)
                  : (c <= 120686 || (c >= 120688 && c <= 120712)))
                : (c <= 120744 || (c < 122624
                  ? (c < 120772
                    ? (c >= 120746 && c <= 120770)
                    : c <= 120779)
                  : (c <= 122654 || (c >= 123136 && c <= 123180)))))
              : (c <= 123197 || (c < 124904
                ? (c < 123584
                  ? (c < 123536
                    ? c == 123214
                    : c <= 123565)
                  : (c <= 123627 || (c >= 124896 && c <= 124902)))
                : (c <= 124907 || (c < 124928
                  ? (c < 124912
                    ? (c >= 124909 && c <= 124910)
                    : c <= 124926)
                  : (c <= 125124 || (c >= 125184 && c <= 125251)))))))))
          : (c <= 125259 || (c < 126559
            ? (c < 126535
              ? (c < 126505
                ? (c < 126497
                  ? (c < 126469
                    ? (c >= 126464 && c <= 126467)
                    : c <= 126495)
                  : (c <= 126498 || (c < 126503
                    ? c == 126500
                    : c <= 126503)))
                : (c <= 126514 || (c < 126523
                  ? (c < 126521
                    ? (c >= 126516 && c <= 126519)
                    : c <= 126521)
                  : (c <= 126523 || c == 126530))))
              : (c <= 126535 || (c < 126548
                ? (c < 126541
                  ? (c < 126539
                    ? c == 126537
                    : c <= 126539)
                  : (c <= 126543 || (c >= 126545 && c <= 126546)))
                : (c <= 126548 || (c < 126555
                  ? (c < 126553
                    ? c == 126551
                    : c <= 126553)
                  : (c <= 126555 || c == 126557))))))
            : (c <= 126559 || (c < 126625
              ? (c < 126580
                ? (c < 126567
                  ? (c < 126564
                    ? (c >= 126561 && c <= 126562)
                    : c <= 126564)
                  : (c <= 126570 || (c >= 126572 && c <= 126578)))
                : (c <= 126583 || (c < 126592
                  ? (c < 126590
                    ? (c >= 126585 && c <= 126588)
                    : c <= 126590)
                  : (c <= 126601 || (c >= 126603 && c <= 126619)))))
              : (c <= 126627 || (c < 177984
                ? (c < 131072
                  ? (c < 126635
                    ? (c >= 126629 && c <= 126633)
                    : c <= 126651)
                  : (c <= 173791 || (c >= 173824 && c <= 177976)))
                : (c <= 178205 || (c < 194560
                  ? (c < 183984
                    ? (c >= 178208 && c <= 183969)
                    : c <= 191456)
                  : (c <= 195101 || (c >= 196608 && c <= 201546)))))))))))))))));
}

static inline bool sym_name_character_set_2(int32_t c) {
  return (c < 43514
    ? (c < 4193
      ? (c < 2707
        ? (c < 1994
          ? (c < 910
            ? (c < 736
              ? (c < 186
                ? (c < 'a'
                  ? (c < '_'
                    ? (c >= 'A' && c <= 'Z')
                    : c <= '_')
                  : (c <= 'z' || (c < 181
                    ? c == 170
                    : c <= 181)))
                : (c <= 186 || (c < 248
                  ? (c < 216
                    ? (c >= 192 && c <= 214)
                    : c <= 246)
                  : (c <= 705 || (c >= 710 && c <= 721)))))
              : (c <= 740 || (c < 891
                ? (c < 880
                  ? (c < 750
                    ? c == 748
                    : c <= 750)
                  : (c <= 884 || (c >= 886 && c <= 887)))
                : (c <= 893 || (c < 904
                  ? (c < 902
                    ? c == 895
                    : c <= 902)
                  : (c <= 906 || c == 908))))))
            : (c <= 929 || (c < 1649
              ? (c < 1376
                ? (c < 1162
                  ? (c < 1015
                    ? (c >= 931 && c <= 1013)
                    : c <= 1153)
                  : (c <= 1327 || (c < 1369
                    ? (c >= 1329 && c <= 1366)
                    : c <= 1369)))
                : (c <= 1416 || (c < 1568
                  ? (c < 1519
                    ? (c >= 1488 && c <= 1514)
                    : c <= 1522)
                  : (c <= 1610 || (c >= 1646 && c <= 1647)))))
              : (c <= 1747 || (c < 1791
                ? (c < 1774
                  ? (c < 1765
                    ? c == 1749
                    : c <= 1766)
                  : (c <= 1775 || (c >= 1786 && c <= 1788)))
                : (c <= 1791 || (c < 1869
                  ? (c < 1810
                    ? c == 1808
                    : c <= 1839)
                  : (c <= 1957 || c == 1969))))))))
          : (c <= 2026 || (c < 2482
            ? (c < 2208
              ? (c < 2088
                ? (c < 2048
                  ? (c < 2042
                    ? (c >= 2036 && c <= 2037)
                    : c <= 2042)
                  : (c <= 2069 || (c < 2084
                    ? c == 2074
                    : c <= 2084)))
                : (c <= 2088 || (c < 2160
                  ? (c < 2144
                    ? (c >= 2112 && c <= 2136)
                    : c <= 2154)
                  : (c <= 2183 || (c >= 2185 && c <= 2190)))))
              : (c <= 2249 || (c < 2417
                ? (c < 2384
                  ? (c < 2365
                    ? (c >= 2308 && c <= 2361)
                    : c <= 2365)
                  : (c <= 2384 || (c >= 2392 && c <= 2401)))
                : (c <= 2432 || (c < 2451
                  ? (c < 2447
                    ? (c >= 2437 && c <= 2444)
                    : c <= 2448)
                  : (c <= 2472 || (c >= 2474 && c <= 2480)))))))
            : (c <= 2482 || (c < 2579
              ? (c < 2527
                ? (c < 2510
                  ? (c < 2493
                    ? (c >= 2486 && c <= 2489)
                    : c <= 2493)
                  : (c <= 2510 || (c >= 2524 && c <= 2525)))
                : (c <= 2529 || (c < 2565
                  ? (c < 2556
                    ? (c >= 2544 && c <= 2545)
                    : c <= 2556)
                  : (c <= 2570 || (c >= 2575 && c <= 2576)))))
              : (c <= 2600 || (c < 2649
                ? (c < 2613
                  ? (c < 2610
                    ? (c >= 2602 && c <= 2608)
                    : c <= 2611)
                  : (c <= 2614 || (c >= 2616 && c <= 2617)))
                : (c <= 2652 || (c < 2693
                  ? (c < 2674
                    ? c == 2654
                    : c <= 2676)
                  : (c <= 2701 || (c >= 2703 && c <= 2705)))))))))))
        : (c <= 2728 || (c < 3242
          ? (c < 2962
            ? (c < 2858
              ? (c < 2784
                ? (c < 2741
                  ? (c < 2738
                    ? (c >= 2730 && c <= 2736)
                    : c <= 2739)
                  : (c <= 2745 || (c < 2768
                    ? c == 2749
                    : c <= 2768)))
                : (c <= 2785 || (c < 2831
                  ? (c < 2821
                    ? c == 2809
                    : c <= 2828)
                  : (c <= 2832 || (c >= 2835 && c <= 2856)))))
              : (c <= 2864 || (c < 2911
                ? (c < 2877
                  ? (c < 2869
                    ? (c >= 2866 && c <= 2867)
                    : c <= 2873)
                  : (c <= 2877 || (c >= 2908 && c <= 2909)))
                : (c <= 2913 || (c < 2949
                  ? (c < 2947
                    ? c == 2929
                    : c <= 2947)
                  : (c <= 2954 || (c >= 2958 && c <= 2960)))))))
            : (c <= 2965 || (c < 3090
              ? (c < 2984
                ? (c < 2974
                  ? (c < 2972
                    ? (c >= 2969 && c <= 2970)
                    : c <= 2972)
                  : (c <= 2975 || (c >= 2979 && c <= 2980)))
                : (c <= 2986 || (c < 3077
                  ? (c < 3024
                    ? (c >= 2990 && c <= 3001)
                    : c <= 3024)
                  : (c <= 3084 || (c >= 3086 && c <= 3088)))))
              : (c <= 3112 || (c < 3168
                ? (c < 3160
                  ? (c < 3133
                    ? (c >= 3114 && c <= 3129)
                    : c <= 3133)
                  : (c <= 3162 || c == 3165))
                : (c <= 3169 || (c < 3214
                  ? (c < 3205
                    ? c == 3200
                    : c <= 3212)
                  : (c <= 3216 || (c >= 3218 && c <= 3240)))))))))
          : (c <= 3251 || (c < 3648
            ? (c < 3412
              ? (c < 3332
                ? (c < 3293
                  ? (c < 3261
                    ? (c >= 3253 && c <= 3257)
                    : c <= 3261)
                  : (c <= 3294 || (c < 3313
                    ? (c >= 3296 && c <= 3297)
                    : c <= 3314)))
                : (c <= 3340 || (c < 3389
                  ? (c < 3346
                    ? (c >= 3342 && c <= 3344)
                    : c <= 3386)
                  : (c <= 3389 || c == 3406))))
              : (c <= 3414 || (c < 3507
                ? (c < 3461
                  ? (c < 3450
                    ? (c >= 3423 && c <= 3425)
                    : c <= 3455)
                  : (c <= 3478 || (c >= 3482 && c <= 3505)))
                : (c <= 3515 || (c < 3585
                  ? (c < 3520
                    ? c == 3517
                    : c <= 3526)
                  : (c <= 3632 || c == 3634))))))
            : (c <= 3654 || (c < 3782
              ? (c < 3749
                ? (c < 3718
                  ? (c < 3716
                    ? (c >= 3713 && c <= 3714)
                    : c <= 3716)
                  : (c <= 3722 || (c >= 3724 && c <= 3747)))
                : (c <= 3749 || (c < 3773
                  ? (c < 3762
                    ? (c >= 3751 && c <= 3760)
                    : c <= 3762)
                  : (c <= 3773 || (c >= 3776 && c <= 3780)))))
              : (c <= 3782 || (c < 3976
                ? (c < 3904
                  ? (c < 3840
                    ? (c >= 3804 && c <= 3807)
                    : c <= 3840)
                  : (c <= 3911 || (c >= 3913 && c <= 3948)))
                : (c <= 3980 || (c < 4176
                  ? (c < 4159
                    ? (c >= 4096 && c <= 4138)
                    : c <= 4159)
                  : (c <= 4181 || (c >= 4186 && c <= 4189)))))))))))))
      : (c <= 4193 || (c < 8134
        ? (c < 6176
          ? (c < 4808
            ? (c < 4688
              ? (c < 4295
                ? (c < 4213
                  ? (c < 4206
                    ? (c >= 4197 && c <= 4198)
                    : c <= 4208)
                  : (c <= 4225 || (c < 4256
                    ? c == 4238
                    : c <= 4293)))
                : (c <= 4295 || (c < 4348
                  ? (c < 4304
                    ? c == 4301
                    : c <= 4346)
                  : (c <= 4680 || (c >= 4682 && c <= 4685)))))
              : (c <= 4694 || (c < 4752
                ? (c < 4704
                  ? (c < 4698
                    ? c == 4696
                    : c <= 4701)
                  : (c <= 4744 || (c >= 4746 && c <= 4749)))
                : (c <= 4784 || (c < 4800
                  ? (c < 4792
                    ? (c >= 4786 && c <= 4789)
                    : c <= 4798)
                  : (c <= 4800 || (c >= 4802 && c <= 4805)))))))
            : (c <= 4822 || (c < 5792
              ? (c < 5024
                ? (c < 4888
                  ? (c < 4882
                    ? (c >= 4824 && c <= 4880)
                    : c <= 4885)
                  : (c <= 4954 || (c >= 4992 && c <= 5007)))
                : (c <= 5109 || (c < 5743
                  ? (c < 5121
                    ? (c >= 5112 && c <= 5117)
                    : c <= 5740)
                  : (c <= 5759 || (c >= 5761 && c <= 5786)))))
              : (c <= 5866 || (c < 5984
                ? (c < 5919
                  ? (c < 5888
                    ? (c >= 5870 && c <= 5880)
                    : c <= 5905)
                  : (c <= 5937 || (c >= 5952 && c <= 5969)))
                : (c <= 5996 || (c < 6103
                  ? (c < 6016
                    ? (c >= 5998 && c <= 6000)
                    : c <= 6067)
                  : (c <= 6103 || c == 6108))))))))
          : (c <= 6264 || (c < 7312
            ? (c < 6823
              ? (c < 6512
                ? (c < 6320
                  ? (c < 6314
                    ? (c >= 6272 && c <= 6312)
                    : c <= 6314)
                  : (c <= 6389 || (c < 6480
                    ? (c >= 6400 && c <= 6430)
                    : c <= 6509)))
                : (c <= 6516 || (c < 6656
                  ? (c < 6576
                    ? (c >= 6528 && c <= 6571)
                    : c <= 6601)
                  : (c <= 6678 || (c >= 6688 && c <= 6740)))))
              : (c <= 6823 || (c < 7098
                ? (c < 7043
                  ? (c < 6981
                    ? (c >= 6917 && c <= 6963)
                    : c <= 6988)
                  : (c <= 7072 || (c >= 7086 && c <= 7087)))
                : (c <= 7141 || (c < 7258
                  ? (c < 7245
                    ? (c >= 7168 && c <= 7203)
                    : c <= 7247)
                  : (c <= 7293 || (c >= 7296 && c <= 7304)))))))
            : (c <= 7354 || (c < 8008
              ? (c < 7418
                ? (c < 7406
                  ? (c < 7401
                    ? (c >= 7357 && c <= 7359)
                    : c <= 7404)
                  : (c <= 7411 || (c >= 7413 && c <= 7414)))
                : (c <= 7418 || (c < 7960
                  ? (c < 7680
                    ? (c >= 7424 && c <= 7615)
                    : c <= 7957)
                  : (c <= 7965 || (c >= 7968 && c <= 8005)))))
              : (c <= 8013 || (c < 8031
                ? (c < 8027
                  ? (c < 8025
                    ? (c >= 8016 && c <= 8023)
                    : c <= 8025)
                  : (c <= 8027 || c == 8029))
                : (c <= 8061 || (c < 8126
                  ? (c < 8118
                    ? (c >= 8064 && c <= 8116)
                    : c <= 8124)
                  : (c <= 8126 || (c >= 8130 && c <= 8132)))))))))))
        : (c <= 8140 || (c < 12337
          ? (c < 8544
            ? (c < 8458
              ? (c < 8305
                ? (c < 8160
                  ? (c < 8150
                    ? (c >= 8144 && c <= 8147)
                    : c <= 8155)
                  : (c <= 8172 || (c < 8182
                    ? (c >= 8178 && c <= 8180)
                    : c <= 8188)))
                : (c <= 8305 || (c < 8450
                  ? (c < 8336
                    ? c == 8319
                    : c <= 8348)
                  : (c <= 8450 || c == 8455))))
              : (c <= 8467 || (c < 8488
                ? (c < 8484
                  ? (c < 8472
                    ? c == 8469
                    : c <= 8477)
                  : (c <= 8484 || c == 8486))
                : (c <= 8488 || (c < 8517
                  ? (c < 8508
                    ? (c >= 8490 && c <= 8505)
                    : c <= 8511)
                  : (c <= 8521 || c == 8526))))))
            : (c <= 8584 || (c < 11680
              ? (c < 11559
                ? (c < 11506
                  ? (c < 11499
                    ? (c >= 11264 && c <= 11492)
                    : c <= 11502)
                  : (c <= 11507 || (c >= 11520 && c <= 11557)))
                : (c <= 11559 || (c < 11631
                  ? (c < 11568
                    ? c == 11565
                    : c <= 11623)
                  : (c <= 11631 || (c >= 11648 && c <= 11670)))))
              : (c <= 11686 || (c < 11720
                ? (c < 11704
                  ? (c < 11696
                    ? (c >= 11688 && c <= 11694)
                    : c <= 11702)
                  : (c <= 11710 || (c >= 11712 && c <= 11718)))
                : (c <= 11726 || (c < 12293
                  ? (c < 11736
                    ? (c >= 11728 && c <= 11734)
                    : c <= 11742)
                  : (c <= 12295 || (c >= 12321 && c <= 12329)))))))))
          : (c <= 12341 || (c < 42891
            ? (c < 19968
              ? (c < 12549
                ? (c < 12445
                  ? (c < 12353
                    ? (c >= 12344 && c <= 12348)
                    : c <= 12438)
                  : (c <= 12447 || (c < 12540
                    ? (c >= 12449 && c <= 12538)
                    : c <= 12543)))
                : (c <= 12591 || (c < 12784
                  ? (c < 12704
                    ? (c >= 12593 && c <= 12686)
                    : c <= 12735)
                  : (c <= 12799 || (c >= 13312 && c <= 19903)))))
              : (c <= 42124 || (c < 42560
                ? (c < 42512
                  ? (c < 42240
                    ? (c >= 42192 && c <= 42237)
                    : c <= 42508)
                  : (c <= 42527 || (c >= 42538 && c <= 42539)))
                : (c <= 42606 || (c < 42775
                  ? (c < 42656
                    ? (c >= 42623 && c <= 42653)
                    : c <= 42735)
                  : (c <= 42783 || (c >= 42786 && c <= 42888)))))))
            : (c <= 42954 || (c < 43250
              ? (c < 43011
                ? (c < 42965
                  ? (c < 42963
                    ? (c >= 42960 && c <= 42961)
                    : c <= 42963)
                  : (c <= 42969 || (c >= 42994 && c <= 43009)))
                : (c <= 43013 || (c < 43072
                  ? (c < 43020
                    ? (c >= 43015 && c <= 43018)
                    : c <= 43042)
                  : (c <= 43123 || (c >= 43138 && c <= 43187)))))
              : (c <= 43255 || (c < 43360
                ? (c < 43274
                  ? (c < 43261
                    ? c == 43259
                    : c <= 43262)
                  : (c <= 43301 || (c >= 43312 && c <= 43334)))
                : (c <= 43388 || (c < 43488
                  ? (c < 43471
                    ? (c >= 43396 && c <= 43442)
                    : c <= 43471)
                  : (c <= 43492 || (c >= 43494 && c <= 43503)))))))))))))))
    : (c <= 43518 || (c < 70727
      ? (c < 66956
        ? (c < 64914
          ? (c < 43868
            ? (c < 43714
              ? (c < 43646
                ? (c < 43588
                  ? (c < 43584
                    ? (c >= 43520 && c <= 43560)
                    : c <= 43586)
                  : (c <= 43595 || (c < 43642
                    ? (c >= 43616 && c <= 43638)
                    : c <= 43642)))
                : (c <= 43695 || (c < 43705
                  ? (c < 43701
                    ? c == 43697
                    : c <= 43702)
                  : (c <= 43709 || c == 43712))))
              : (c <= 43714 || (c < 43785
                ? (c < 43762
                  ? (c < 43744
                    ? (c >= 43739 && c <= 43741)
                    : c <= 43754)
                  : (c <= 43764 || (c >= 43777 && c <= 43782)))
                : (c <= 43790 || (c < 43816
                  ? (c < 43808
                    ? (c >= 43793 && c <= 43798)
                    : c <= 43814)
                  : (c <= 43822 || (c >= 43824 && c <= 43866)))))))
            : (c <= 43881 || (c < 64287
              ? (c < 63744
                ? (c < 55216
                  ? (c < 44032
                    ? (c >= 43888 && c <= 44002)
                    : c <= 55203)
                  : (c <= 55238 || (c >= 55243 && c <= 55291)))
                : (c <= 64109 || (c < 64275
                  ? (c < 64256
                    ? (c >= 64112 && c <= 64217)
                    : c <= 64262)
                  : (c <= 64279 || c == 64285))))
              : (c <= 64296 || (c < 64323
                ? (c < 64318
                  ? (c < 64312
                    ? (c >= 64298 && c <= 64310)
                    : c <= 64316)
                  : (c <= 64318 || (c >= 64320 && c <= 64321)))
                : (c <= 64324 || (c < 64612
                  ? (c < 64467
                    ? (c >= 64326 && c <= 64433)
                    : c <= 64605)
                  : (c <= 64829 || (c >= 64848 && c <= 64911)))))))))
          : (c <= 64967 || (c < 65599
            ? (c < 65382
              ? (c < 65147
                ? (c < 65139
                  ? (c < 65137
                    ? (c >= 65008 && c <= 65017)
                    : c <= 65137)
                  : (c <= 65139 || (c < 65145
                    ? c == 65143
                    : c <= 65145)))
                : (c <= 65147 || (c < 65313
                  ? (c < 65151
                    ? c == 65149
                    : c <= 65276)
                  : (c <= 65338 || (c >= 65345 && c <= 65370)))))
              : (c <= 65437 || (c < 65498
                ? (c < 65482
                  ? (c < 65474
                    ? (c >= 65440 && c <= 65470)
                    : c <= 65479)
                  : (c <= 65487 || (c >= 65490 && c <= 65495)))
                : (c <= 65500 || (c < 65576
                  ? (c < 65549
                    ? (c >= 65536 && c <= 65547)
                    : c <= 65574)
                  : (c <= 65594 || (c >= 65596 && c <= 65597)))))))
            : (c <= 65613 || (c < 66464
              ? (c < 66208
                ? (c < 65856
                  ? (c < 65664
                    ? (c >= 65616 && c <= 65629)
                    : c <= 65786)
                  : (c <= 65908 || (c >= 66176 && c <= 66204)))
                : (c <= 66256 || (c < 66384
                  ? (c < 66349
                    ? (c >= 66304 && c <= 66335)
                    : c <= 66378)
                  : (c <= 66421 || (c >= 66432 && c <= 66461)))))
              : (c <= 66499 || (c < 66776
                ? (c < 66560
                  ? (c < 66513
                    ? (c >= 66504 && c <= 66511)
                    : c <= 66517)
                  : (c <= 66717 || (c >= 66736 && c <= 66771)))
                : (c <= 66811 || (c < 66928
                  ? (c < 66864
                    ? (c >= 66816 && c <= 66855)
                    : c <= 66915)
                  : (c <= 66938 || (c >= 66940 && c <= 66954)))))))))))
        : (c <= 66962 || (c < 68864
          ? (c < 67828
            ? (c < 67506
              ? (c < 67072
                ? (c < 66979
                  ? (c < 66967
                    ? (c >= 66964 && c <= 66965)
                    : c <= 66977)
                  : (c <= 66993 || (c < 67003
                    ? (c >= 66995 && c <= 67001)
                    : c <= 67004)))
                : (c <= 67382 || (c < 67456
                  ? (c < 67424
                    ? (c >= 67392 && c <= 67413)
                    : c <= 67431)
                  : (c <= 67461 || (c >= 67463 && c <= 67504)))))
              : (c <= 67514 || (c < 67644
                ? (c < 67594
                  ? (c < 67592
                    ? (c >= 67584 && c <= 67589)
                    : c <= 67592)
                  : (c <= 67637 || (c >= 67639 && c <= 67640)))
                : (c <= 67644 || (c < 67712
                  ? (c < 67680
                    ? (c >= 67647 && c <= 67669)
                    : c <= 67702)
                  : (c <= 67742 || (c >= 67808 && c <= 67826)))))))
            : (c <= 67829 || (c < 68224
              ? (c < 68096
                ? (c < 67968
                  ? (c < 67872
                    ? (c >= 67840 && c <= 67861)
                    : c <= 67897)
                  : (c <= 68023 || (c >= 68030 && c <= 68031)))
                : (c <= 68096 || (c < 68121
                  ? (c < 68117
                    ? (c >= 68112 && c <= 68115)
                    : c <= 68119)
                  : (c <= 68149 || (c >= 68192 && c <= 68220)))))
              : (c <= 68252 || (c < 68448
                ? (c < 68352
                  ? (c < 68297
                    ? (c >= 68288 && c <= 68295)
                    : c <= 68324)
                  : (c <= 68405 || (c >= 68416 && c <= 68437)))
                : (c <= 68466 || (c < 68736
                  ? (c < 68608
                    ? (c >= 68480 && c <= 68497)
                    : c <= 68680)
                  : (c <= 68786 || (c >= 68800 && c <= 68850)))))))))
          : (c <= 68899 || (c < 70106
            ? (c < 69749
              ? (c < 69488
                ? (c < 69376
                  ? (c < 69296
                    ? (c >= 69248 && c <= 69289)
                    : c <= 69297)
                  : (c <= 69404 || (c < 69424
                    ? c == 69415
                    : c <= 69445)))
                : (c <= 69505 || (c < 69635
                  ? (c < 69600
                    ? (c >= 69552 && c <= 69572)
                    : c <= 69622)
                  : (c <= 69687 || (c >= 69745 && c <= 69746)))))
              : (c <= 69749 || (c < 69959
                ? (c < 69891
                  ? (c < 69840
                    ? (c >= 69763 && c <= 69807)
                    : c <= 69864)
                  : (c <= 69926 || c == 69956))
                : (c <= 69959 || (c < 70019
                  ? (c < 70006
                    ? (c >= 69968 && c <= 70002)
                    : c <= 70006)
                  : (c <= 70066 || (c >= 70081 && c <= 70084)))))))
            : (c <= 70106 || (c < 70405
              ? (c < 70280
                ? (c < 70163
                  ? (c < 70144
                    ? c == 70108
                    : c <= 70161)
                  : (c <= 70187 || (c >= 70272 && c <= 70278)))
                : (c <= 70280 || (c < 70303
                  ? (c < 70287
                    ? (c >= 70282 && c <= 70285)
                    : c <= 70301)
                  : (c <= 70312 || (c >= 70320 && c <= 70366)))))
              : (c <= 70412 || (c < 70453
                ? (c < 70442
                  ? (c < 70419
                    ? (c >= 70415 && c <= 70416)
                    : c <= 70440)
                  : (c <= 70448 || (c >= 70450 && c <= 70451)))
                : (c <= 70457 || (c < 70493
                  ? (c < 70480
                    ? c == 70461
                    : c <= 70480)
                  : (c <= 70497 || (c >= 70656 && c <= 70708)))))))))))))
      : (c <= 70730 || (c < 119894
        ? (c < 73056
          ? (c < 72001
            ? (c < 71424
              ? (c < 71128
                ? (c < 70852
                  ? (c < 70784
                    ? (c >= 70751 && c <= 70753)
                    : c <= 70831)
                  : (c <= 70853 || (c < 71040
                    ? c == 70855
                    : c <= 71086)))
                : (c <= 71131 || (c < 71296
                  ? (c < 71236
                    ? (c >= 71168 && c <= 71215)
                    : c <= 71236)
                  : (c <= 71338 || c == 71352))))
              : (c <= 71450 || (c < 71945
                ? (c < 71840
                  ? (c < 71680
                    ? (c >= 71488 && c <= 71494)
                    : c <= 71723)
                  : (c <= 71903 || (c >= 71935 && c <= 71942)))
                : (c <= 71945 || (c < 71960
                  ? (c < 71957
                    ? (c >= 71948 && c <= 71955)
                    : c <= 71958)
                  : (c <= 71983 || c == 71999))))))
            : (c <= 72001 || (c < 72349
              ? (c < 72192
                ? (c < 72161
                  ? (c < 72106
                    ? (c >= 72096 && c <= 72103)
                    : c <= 72144)
                  : (c <= 72161 || c == 72163))
                : (c <= 72192 || (c < 72272
                  ? (c < 72250
                    ? (c >= 72203 && c <= 72242)
                    : c <= 72250)
                  : (c <= 72272 || (c >= 72284 && c <= 72329)))))
              : (c <= 72349 || (c < 72818
                ? (c < 72714
                  ? (c < 72704
                    ? (c >= 72368 && c <= 72440)
                    : c <= 72712)
                  : (c <= 72750 || c == 72768))
                : (c <= 72847 || (c < 72971
                  ? (c < 72968
                    ? (c >= 72960 && c <= 72966)
                    : c <= 72969)
                  : (c <= 73008 || c == 73030))))))))
          : (c <= 73061 || (c < 93952
            ? (c < 82944
              ? (c < 73728
                ? (c < 73112
                  ? (c < 73066
                    ? (c >= 73063 && c <= 73064)
                    : c <= 73097)
                  : (c <= 73112 || (c < 73648
                    ? (c >= 73440 && c <= 73458)
                    : c <= 73648)))
                : (c <= 74649 || (c < 77712
                  ? (c < 74880
                    ? (c >= 74752 && c <= 74862)
                    : c <= 75075)
                  : (c <= 77808 || (c >= 77824 && c <= 78894)))))
              : (c <= 83526 || (c < 92928
                ? (c < 92784
                  ? (c < 92736
                    ? (c >= 92160 && c <= 92728)
                    : c <= 92766)
                  : (c <= 92862 || (c >= 92880 && c <= 92909)))
                : (c <= 92975 || (c < 93053
                  ? (c < 93027
                    ? (c >= 92992 && c <= 92995)
                    : c <= 93047)
                  : (c <= 93071 || (c >= 93760 && c <= 93823)))))))
            : (c <= 94026 || (c < 110589
              ? (c < 94208
                ? (c < 94176
                  ? (c < 94099
                    ? c == 94032
                    : c <= 94111)
                  : (c <= 94177 || c == 94179))
                : (c <= 100343 || (c < 110576
                  ? (c < 101632
                    ? (c >= 100352 && c <= 101589)
                    : c <= 101640)
                  : (c <= 110579 || (c >= 110581 && c <= 110587)))))
              : (c <= 110590 || (c < 113664
                ? (c < 110948
                  ? (c < 110928
                    ? (c >= 110592 && c <= 110882)
                    : c <= 110930)
                  : (c <= 110951 || (c >= 110960 && c <= 111355)))
                : (c <= 113770 || (c < 113808
                  ? (c < 113792
                    ? (c >= 113776 && c <= 113788)
                    : c <= 113800)
                  : (c <= 113817 || (c >= 119808 && c <= 119892)))))))))))
        : (c <= 119964 || (c < 125259
          ? (c < 120572
            ? (c < 120086
              ? (c < 119995
                ? (c < 119973
                  ? (c < 119970
                    ? (c >= 119966 && c <= 119967)
                    : c <= 119970)
                  : (c <= 119974 || (c < 119982
                    ? (c >= 119977 && c <= 119980)
                    : c <= 119993)))
                : (c <= 119995 || (c < 120071
                  ? (c < 120005
                    ? (c >= 119997 && c <= 120003)
                    : c <= 120069)
                  : (c <= 120074 || (c >= 120077 && c <= 120084)))))
              : (c <= 120092 || (c < 120138
                ? (c < 120128
                  ? (c < 120123
                    ? (c >= 120094 && c <= 120121)
                    : c <= 120126)
                  : (c <= 120132 || c == 120134))
                : (c <= 120144 || (c < 120514
                  ? (c < 120488
                    ? (c >= 120146 && c <= 120485)
                    : c <= 120512)
                  : (c <= 120538 || (c >= 120540 && c <= 120570)))))))
            : (c <= 120596 || (c < 123191
              ? (c < 120714
                ? (c < 120656
                  ? (c < 120630
                    ? (c >= 120598 && c <= 120628)
                    : c <= 120654)
                  : (c <= 120686 || (c >= 120688 && c <= 120712)))
                : (c <= 120744 || (c < 122624
                  ? (c < 120772
                    ? (c >= 120746 && c <= 120770)
                    : c <= 120779)
                  : (c <= 122654 || (c >= 123136 && c <= 123180)))))
              : (c <= 123197 || (c < 124904
                ? (c < 123584
                  ? (c < 123536
                    ? c == 123214
                    : c <= 123565)
                  : (c <= 123627 || (c >= 124896 && c <= 124902)))
                : (c <= 124907 || (c < 124928
                  ? (c < 124912
                    ? (c >= 124909 && c <= 124910)
                    : c <= 124926)
                  : (c <= 125124 || (c >= 125184 && c <= 125251)))))))))
          : (c <= 125259 || (c < 126559
            ? (c < 126535
              ? (c < 126505
                ? (c < 126497
                  ? (c < 126469
                    ? (c >= 126464 && c <= 126467)
                    : c <= 126495)
                  : (c <= 126498 || (c < 126503
                    ? c == 126500
                    : c <= 126503)))
                : (c <= 126514 || (c < 126523
                  ? (c < 126521
                    ? (c >= 126516 && c <= 126519)
                    : c <= 126521)
                  : (c <= 126523 || c == 126530))))
              : (c <= 126535 || (c < 126548
                ? (c < 126541
                  ? (c < 126539
                    ? c == 126537
                    : c <= 126539)
                  : (c <= 126543 || (c >= 126545 && c <= 126546)))
                : (c <= 126548 || (c < 126555
                  ? (c < 126553
                    ? c == 126551
                    : c <= 126553)
                  : (c <= 126555 || c == 126557))))))
            : (c <= 126559 || (c < 126625
              ? (c < 126580
                ? (c < 126567
                  ? (c < 126564
                    ? (c >= 126561 && c <= 126562)
                    : c <= 126564)
                  : (c <= 126570 || (c >= 126572 && c <= 126578)))
                : (c <= 126583 || (c < 126592
                  ? (c < 126590
                    ? (c >= 126585 && c <= 126588)
                    : c <= 126590)
                  : (c <= 126601 || (c >= 126603 && c <= 126619)))))
              : (c <= 126627 || (c < 177984
                ? (c < 131072
                  ? (c < 126635
                    ? (c >= 126629 && c <= 126633)
                    : c <= 126651)
                  : (c <= 173791 || (c >= 173824 && c <= 177976)))
                : (c <= 178205 || (c < 194560
                  ? (c < 183984
                    ? (c >= 178208 && c <= 183969)
                    : c <= 191456)
                  : (c <= 195101 || (c >= 196608 && c <= 201546)))))))))))))))));
}

static inline bool sym_name_character_set_3(int32_t c) {
  return (c < 43514
    ? (c < 4193
      ? (c < 2707
        ? (c < 1994
          ? (c < 910
            ? (c < 736
              ? (c < 186
                ? (c < 'b'
                  ? (c < '_'
                    ? (c >= 'A' && c <= 'Z')
                    : c <= '_')
                  : (c <= 'z' || (c < 181
                    ? c == 170
                    : c <= 181)))
                : (c <= 186 || (c < 248
                  ? (c < 216
                    ? (c >= 192 && c <= 214)
                    : c <= 246)
                  : (c <= 705 || (c >= 710 && c <= 721)))))
              : (c <= 740 || (c < 891
                ? (c < 880
                  ? (c < 750
                    ? c == 748
                    : c <= 750)
                  : (c <= 884 || (c >= 886 && c <= 887)))
                : (c <= 893 || (c < 904
                  ? (c < 902
                    ? c == 895
                    : c <= 902)
                  : (c <= 906 || c == 908))))))
            : (c <= 929 || (c < 1649
              ? (c < 1376
                ? (c < 1162
                  ? (c < 1015
                    ? (c >= 931 && c <= 1013)
                    : c <= 1153)
                  : (c <= 1327 || (c < 1369
                    ? (c >= 1329 && c <= 1366)
                    : c <= 1369)))
                : (c <= 1416 || (c < 1568
                  ? (c < 1519
                    ? (c >= 1488 && c <= 1514)
                    : c <= 1522)
                  : (c <= 1610 || (c >= 1646 && c <= 1647)))))
              : (c <= 1747 || (c < 1791
                ? (c < 1774
                  ? (c < 1765
                    ? c == 1749
                    : c <= 1766)
                  : (c <= 1775 || (c >= 1786 && c <= 1788)))
                : (c <= 1791 || (c < 1869
                  ? (c < 1810
                    ? c == 1808
                    : c <= 1839)
                  : (c <= 1957 || c == 1969))))))))
          : (c <= 2026 || (c < 2482
            ? (c < 2208
              ? (c < 2088
                ? (c < 2048
                  ? (c < 2042
                    ? (c >= 2036 && c <= 2037)
                    : c <= 2042)
                  : (c <= 2069 || (c < 2084
                    ? c == 2074
                    : c <= 2084)))
                : (c <= 2088 || (c < 2160
                  ? (c < 2144
                    ? (c >= 2112 && c <= 2136)
                    : c <= 2154)
                  : (c <= 2183 || (c >= 2185 && c <= 2190)))))
              : (c <= 2249 || (c < 2417
                ? (c < 2384
                  ? (c < 2365
                    ? (c >= 2308 && c <= 2361)
                    : c <= 2365)
                  : (c <= 2384 || (c >= 2392 && c <= 2401)))
                : (c <= 2432 || (c < 2451
                  ? (c < 2447
                    ? (c >= 2437 && c <= 2444)
                    : c <= 2448)
                  : (c <= 2472 || (c >= 2474 && c <= 2480)))))))
            : (c <= 2482 || (c < 2579
              ? (c < 2527
                ? (c < 2510
                  ? (c < 2493
                    ? (c >= 2486 && c <= 2489)
                    : c <= 2493)
                  : (c <= 2510 || (c >= 2524 && c <= 2525)))
                : (c <= 2529 || (c < 2565
                  ? (c < 2556
                    ? (c >= 2544 && c <= 2545)
                    : c <= 2556)
                  : (c <= 2570 || (c >= 2575 && c <= 2576)))))
              : (c <= 2600 || (c < 2649
                ? (c < 2613
                  ? (c < 2610
                    ? (c >= 2602 && c <= 2608)
                    : c <= 2611)
                  : (c <= 2614 || (c >= 2616 && c <= 2617)))
                : (c <= 2652 || (c < 2693
                  ? (c < 2674
                    ? c == 2654
                    : c <= 2676)
                  : (c <= 2701 || (c >= 2703 && c <= 2705)))))))))))
        : (c <= 2728 || (c < 3242
          ? (c < 2962
            ? (c < 2858
              ? (c < 2784
                ? (c < 2741
                  ? (c < 2738
                    ? (c >= 2730 && c <= 2736)
                    : c <= 2739)
                  : (c <= 2745 || (c < 2768
                    ? c == 2749
                    : c <= 2768)))
                : (c <= 2785 || (c < 2831
                  ? (c < 2821
                    ? c == 2809
                    : c <= 2828)
                  : (c <= 2832 || (c >= 2835 && c <= 2856)))))
              : (c <= 2864 || (c < 2911
                ? (c < 2877
                  ? (c < 2869
                    ? (c >= 2866 && c <= 2867)
                    : c <= 2873)
                  : (c <= 2877 || (c >= 2908 && c <= 2909)))
                : (c <= 2913 || (c < 2949
                  ? (c < 2947
                    ? c == 2929
                    : c <= 2947)
                  : (c <= 2954 || (c >= 2958 && c <= 2960)))))))
            : (c <= 2965 || (c < 3090
              ? (c < 2984
                ? (c < 2974
                  ? (c < 2972
                    ? (c >= 2969 && c <= 2970)
                    : c <= 2972)
                  : (c <= 2975 || (c >= 2979 && c <= 2980)))
                : (c <= 2986 || (c < 3077
                  ? (c < 3024
                    ? (c >= 2990 && c <= 3001)
                    : c <= 3024)
                  : (c <= 3084 || (c >= 3086 && c <= 3088)))))
              : (c <= 3112 || (c < 3168
                ? (c < 3160
                  ? (c < 3133
                    ? (c >= 3114 && c <= 3129)
                    : c <= 3133)
                  : (c <= 3162 || c == 3165))
                : (c <= 3169 || (c < 3214
                  ? (c < 3205
                    ? c == 3200
                    : c <= 3212)
                  : (c <= 3216 || (c >= 3218 && c <= 3240)))))))))
          : (c <= 3251 || (c < 3648
            ? (c < 3412
              ? (c < 3332
                ? (c < 3293
                  ? (c < 3261
                    ? (c >= 3253 && c <= 3257)
                    : c <= 3261)
                  : (c <= 3294 || (c < 3313
                    ? (c >= 3296 && c <= 3297)
                    : c <= 3314)))
                : (c <= 3340 || (c < 3389
                  ? (c < 3346
                    ? (c >= 3342 && c <= 3344)
                    : c <= 3386)
                  : (c <= 3389 || c == 3406))))
              : (c <= 3414 || (c < 3507
                ? (c < 3461
                  ? (c < 3450
                    ? (c >= 3423 && c <= 3425)
                    : c <= 3455)
                  : (c <= 3478 || (c >= 3482 && c <= 3505)))
                : (c <= 3515 || (c < 3585
                  ? (c < 3520
                    ? c == 3517
                    : c <= 3526)
                  : (c <= 3632 || c == 3634))))))
            : (c <= 3654 || (c < 3782
              ? (c < 3749
                ? (c < 3718
                  ? (c < 3716
                    ? (c >= 3713 && c <= 3714)
                    : c <= 3716)
                  : (c <= 3722 || (c >= 3724 && c <= 3747)))
                : (c <= 3749 || (c < 3773
                  ? (c < 3762
                    ? (c >= 3751 && c <= 3760)
                    : c <= 3762)
                  : (c <= 3773 || (c >= 3776 && c <= 3780)))))
              : (c <= 3782 || (c < 3976
                ? (c < 3904
                  ? (c < 3840
                    ? (c >= 3804 && c <= 3807)
                    : c <= 3840)
                  : (c <= 3911 || (c >= 3913 && c <= 3948)))
                : (c <= 3980 || (c < 4176
                  ? (c < 4159
                    ? (c >= 4096 && c <= 4138)
                    : c <= 4159)
                  : (c <= 4181 || (c >= 4186 && c <= 4189)))))))))))))
      : (c <= 4193 || (c < 8134
        ? (c < 6176
          ? (c < 4808
            ? (c < 4688
              ? (c < 4295
                ? (c < 4213
                  ? (c < 4206
                    ? (c >= 4197 && c <= 4198)
                    : c <= 4208)
                  : (c <= 4225 || (c < 4256
                    ? c == 4238
                    : c <= 4293)))
                : (c <= 4295 || (c < 4348
                  ? (c < 4304
                    ? c == 4301
                    : c <= 4346)
                  : (c <= 4680 || (c >= 4682 && c <= 4685)))))
              : (c <= 4694 || (c < 4752
                ? (c < 4704
                  ? (c < 4698
                    ? c == 4696
                    : c <= 4701)
                  : (c <= 4744 || (c >= 4746 && c <= 4749)))
                : (c <= 4784 || (c < 4800
                  ? (c < 4792
                    ? (c >= 4786 && c <= 4789)
                    : c <= 4798)
                  : (c <= 4800 || (c >= 4802 && c <= 4805)))))))
            : (c <= 4822 || (c < 5792
              ? (c < 5024
                ? (c < 4888
                  ? (c < 4882
                    ? (c >= 4824 && c <= 4880)
                    : c <= 4885)
                  : (c <= 4954 || (c >= 4992 && c <= 5007)))
                : (c <= 5109 || (c < 5743
                  ? (c < 5121
                    ? (c >= 5112 && c <= 5117)
                    : c <= 5740)
                  : (c <= 5759 || (c >= 5761 && c <= 5786)))))
              : (c <= 5866 || (c < 5984
                ? (c < 5919
                  ? (c < 5888
                    ? (c >= 5870 && c <= 5880)
                    : c <= 5905)
                  : (c <= 5937 || (c >= 5952 && c <= 5969)))
                : (c <= 5996 || (c < 6103
                  ? (c < 6016
                    ? (c >= 5998 && c <= 6000)
                    : c <= 6067)
                  : (c <= 6103 || c == 6108))))))))
          : (c <= 6264 || (c < 7312
            ? (c < 6823
              ? (c < 6512
                ? (c < 6320
                  ? (c < 6314
                    ? (c >= 6272 && c <= 6312)
                    : c <= 6314)
                  : (c <= 6389 || (c < 6480
                    ? (c >= 6400 && c <= 6430)
                    : c <= 6509)))
                : (c <= 6516 || (c < 6656
                  ? (c < 6576
                    ? (c >= 6528 && c <= 6571)
                    : c <= 6601)
                  : (c <= 6678 || (c >= 6688 && c <= 6740)))))
              : (c <= 6823 || (c < 7098
                ? (c < 7043
                  ? (c < 6981
                    ? (c >= 6917 && c <= 6963)
                    : c <= 6988)
                  : (c <= 7072 || (c >= 7086 && c <= 7087)))
                : (c <= 7141 || (c < 7258
                  ? (c < 7245
                    ? (c >= 7168 && c <= 7203)
                    : c <= 7247)
                  : (c <= 7293 || (c >= 7296 && c <= 7304)))))))
            : (c <= 7354 || (c < 8008
              ? (c < 7418
                ? (c < 7406
                  ? (c < 7401
                    ? (c >= 7357 && c <= 7359)
                    : c <= 7404)
                  : (c <= 7411 || (c >= 7413 && c <= 7414)))
                : (c <= 7418 || (c < 7960
                  ? (c < 7680
                    ? (c >= 7424 && c <= 7615)
                    : c <= 7957)
                  : (c <= 7965 || (c >= 7968 && c <= 8005)))))
              : (c <= 8013 || (c < 8031
                ? (c < 8027
                  ? (c < 8025
                    ? (c >= 8016 && c <= 8023)
                    : c <= 8025)
                  : (c <= 8027 || c == 8029))
                : (c <= 8061 || (c < 8126
                  ? (c < 8118
                    ? (c >= 8064 && c <= 8116)
                    : c <= 8124)
                  : (c <= 8126 || (c >= 8130 && c <= 8132)))))))))))
        : (c <= 8140 || (c < 12337
          ? (c < 8544
            ? (c < 8458
              ? (c < 8305
                ? (c < 8160
                  ? (c < 8150
                    ? (c >= 8144 && c <= 8147)
                    : c <= 8155)
                  : (c <= 8172 || (c < 8182
                    ? (c >= 8178 && c <= 8180)
                    : c <= 8188)))
                : (c <= 8305 || (c < 8450
                  ? (c < 8336
                    ? c == 8319
                    : c <= 8348)
                  : (c <= 8450 || c == 8455))))
              : (c <= 8467 || (c < 8488
                ? (c < 8484
                  ? (c < 8472
                    ? c == 8469
                    : c <= 8477)
                  : (c <= 8484 || c == 8486))
                : (c <= 8488 || (c < 8517
                  ? (c < 8508
                    ? (c >= 8490 && c <= 8505)
                    : c <= 8511)
                  : (c <= 8521 || c == 8526))))))
            : (c <= 8584 || (c < 11680
              ? (c < 11559
                ? (c < 11506
                  ? (c < 11499
                    ? (c >= 11264 && c <= 11492)
                    : c <= 11502)
                  : (c <= 11507 || (c >= 11520 && c <= 11557)))
                : (c <= 11559 || (c < 11631
                  ? (c < 11568
                    ? c == 11565
                    : c <= 11623)
                  : (c <= 11631 || (c >= 11648 && c <= 11670)))))
              : (c <= 11686 || (c < 11720
                ? (c < 11704
                  ? (c < 11696
                    ? (c >= 11688 && c <= 11694)
                    : c <= 11702)
                  : (c <= 11710 || (c >= 11712 && c <= 11718)))
                : (c <= 11726 || (c < 12293
                  ? (c < 11736
                    ? (c >= 11728 && c <= 11734)
                    : c <= 11742)
                  : (c <= 12295 || (c >= 12321 && c <= 12329)))))))))
          : (c <= 12341 || (c < 42891
            ? (c < 19968
              ? (c < 12549
                ? (c < 12445
                  ? (c < 12353
                    ? (c >= 12344 && c <= 12348)
                    : c <= 12438)
                  : (c <= 12447 || (c < 12540
                    ? (c >= 12449 && c <= 12538)
                    : c <= 12543)))
                : (c <= 12591 || (c < 12784
                  ? (c < 12704
                    ? (c >= 12593 && c <= 12686)
                    : c <= 12735)
                  : (c <= 12799 || (c >= 13312 && c <= 19903)))))
              : (c <= 42124 || (c < 42560
                ? (c < 42512
                  ? (c < 42240
                    ? (c >= 42192 && c <= 42237)
                    : c <= 42508)
                  : (c <= 42527 || (c >= 42538 && c <= 42539)))
                : (c <= 42606 || (c < 42775
                  ? (c < 42656
                    ? (c >= 42623 && c <= 42653)
                    : c <= 42735)
                  : (c <= 42783 || (c >= 42786 && c <= 42888)))))))
            : (c <= 42954 || (c < 43250
              ? (c < 43011
                ? (c < 42965
                  ? (c < 42963
                    ? (c >= 42960 && c <= 42961)
                    : c <= 42963)
                  : (c <= 42969 || (c >= 42994 && c <= 43009)))
                : (c <= 43013 || (c < 43072
                  ? (c < 43020
                    ? (c >= 43015 && c <= 43018)
                    : c <= 43042)
                  : (c <= 43123 || (c >= 43138 && c <= 43187)))))
              : (c <= 43255 || (c < 43360
                ? (c < 43274
                  ? (c < 43261
                    ? c == 43259
                    : c <= 43262)
                  : (c <= 43301 || (c >= 43312 && c <= 43334)))
                : (c <= 43388 || (c < 43488
                  ? (c < 43471
                    ? (c >= 43396 && c <= 43442)
                    : c <= 43471)
                  : (c <= 43492 || (c >= 43494 && c <= 43503)))))))))))))))
    : (c <= 43518 || (c < 70727
      ? (c < 66956
        ? (c < 64914
          ? (c < 43868
            ? (c < 43714
              ? (c < 43646
                ? (c < 43588
                  ? (c < 43584
                    ? (c >= 43520 && c <= 43560)
                    : c <= 43586)
                  : (c <= 43595 || (c < 43642
                    ? (c >= 43616 && c <= 43638)
                    : c <= 43642)))
                : (c <= 43695 || (c < 43705
                  ? (c < 43701
                    ? c == 43697
                    : c <= 43702)
                  : (c <= 43709 || c == 43712))))
              : (c <= 43714 || (c < 43785
                ? (c < 43762
                  ? (c < 43744
                    ? (c >= 43739 && c <= 43741)
                    : c <= 43754)
                  : (c <= 43764 || (c >= 43777 && c <= 43782)))
                : (c <= 43790 || (c < 43816
                  ? (c < 43808
                    ? (c >= 43793 && c <= 43798)
                    : c <= 43814)
                  : (c <= 43822 || (c >= 43824 && c <= 43866)))))))
            : (c <= 43881 || (c < 64287
              ? (c < 63744
                ? (c < 55216
                  ? (c < 44032
                    ? (c >= 43888 && c <= 44002)
                    : c <= 55203)
                  : (c <= 55238 || (c >= 55243 && c <= 55291)))
                : (c <= 64109 || (c < 64275
                  ? (c < 64256
                    ? (c >= 64112 && c <= 64217)
                    : c <= 64262)
                  : (c <= 64279 || c == 64285))))
              : (c <= 64296 || (c < 64323
                ? (c < 64318
                  ? (c < 64312
                    ? (c >= 64298 && c <= 64310)
                    : c <= 64316)
                  : (c <= 64318 || (c >= 64320 && c <= 64321)))
                : (c <= 64324 || (c < 64612
                  ? (c < 64467
                    ? (c >= 64326 && c <= 64433)
                    : c <= 64605)
                  : (c <= 64829 || (c >= 64848 && c <= 64911)))))))))
          : (c <= 64967 || (c < 65599
            ? (c < 65382
              ? (c < 65147
                ? (c < 65139
                  ? (c < 65137
                    ? (c >= 65008 && c <= 65017)
                    : c <= 65137)
                  : (c <= 65139 || (c < 65145
                    ? c == 65143
                    : c <= 65145)))
                : (c <= 65147 || (c < 65313
                  ? (c < 65151
                    ? c == 65149
                    : c <= 65276)
                  : (c <= 65338 || (c >= 65345 && c <= 65370)))))
              : (c <= 65437 || (c < 65498
                ? (c < 65482
                  ? (c < 65474
                    ? (c >= 65440 && c <= 65470)
                    : c <= 65479)
                  : (c <= 65487 || (c >= 65490 && c <= 65495)))
                : (c <= 65500 || (c < 65576
                  ? (c < 65549
                    ? (c >= 65536 && c <= 65547)
                    : c <= 65574)
                  : (c <= 65594 || (c >= 65596 && c <= 65597)))))))
            : (c <= 65613 || (c < 66464
              ? (c < 66208
                ? (c < 65856
                  ? (c < 65664
                    ? (c >= 65616 && c <= 65629)
                    : c <= 65786)
                  : (c <= 65908 || (c >= 66176 && c <= 66204)))
                : (c <= 66256 || (c < 66384
                  ? (c < 66349
                    ? (c >= 66304 && c <= 66335)
                    : c <= 66378)
                  : (c <= 66421 || (c >= 66432 && c <= 66461)))))
              : (c <= 66499 || (c < 66776
                ? (c < 66560
                  ? (c < 66513
                    ? (c >= 66504 && c <= 66511)
                    : c <= 66517)
                  : (c <= 66717 || (c >= 66736 && c <= 66771)))
                : (c <= 66811 || (c < 66928
                  ? (c < 66864
                    ? (c >= 66816 && c <= 66855)
                    : c <= 66915)
                  : (c <= 66938 || (c >= 66940 && c <= 66954)))))))))))
        : (c <= 66962 || (c < 68864
          ? (c < 67828
            ? (c < 67506
              ? (c < 67072
                ? (c < 66979
                  ? (c < 66967
                    ? (c >= 66964 && c <= 66965)
                    : c <= 66977)
                  : (c <= 66993 || (c < 67003
                    ? (c >= 66995 && c <= 67001)
                    : c <= 67004)))
                : (c <= 67382 || (c < 67456
                  ? (c < 67424
                    ? (c >= 67392 && c <= 67413)
                    : c <= 67431)
                  : (c <= 67461 || (c >= 67463 && c <= 67504)))))
              : (c <= 67514 || (c < 67644
                ? (c < 67594
                  ? (c < 67592
                    ? (c >= 67584 && c <= 67589)
                    : c <= 67592)
                  : (c <= 67637 || (c >= 67639 && c <= 67640)))
                : (c <= 67644 || (c < 67712
                  ? (c < 67680
                    ? (c >= 67647 && c <= 67669)
                    : c <= 67702)
                  : (c <= 67742 || (c >= 67808 && c <= 67826)))))))
            : (c <= 67829 || (c < 68224
              ? (c < 68096
                ? (c < 67968
                  ? (c < 67872
                    ? (c >= 67840 && c <= 67861)
                    : c <= 67897)
                  : (c <= 68023 || (c >= 68030 && c <= 68031)))
                : (c <= 68096 || (c < 68121
                  ? (c < 68117
                    ? (c >= 68112 && c <= 68115)
                    : c <= 68119)
                  : (c <= 68149 || (c >= 68192 && c <= 68220)))))
              : (c <= 68252 || (c < 68448
                ? (c < 68352
                  ? (c < 68297
                    ? (c >= 68288 && c <= 68295)
                    : c <= 68324)
                  : (c <= 68405 || (c >= 68416 && c <= 68437)))
                : (c <= 68466 || (c < 68736
                  ? (c < 68608
                    ? (c >= 68480 && c <= 68497)
                    : c <= 68680)
                  : (c <= 68786 || (c >= 68800 && c <= 68850)))))))))
          : (c <= 68899 || (c < 70106
            ? (c < 69749
              ? (c < 69488
                ? (c < 69376
                  ? (c < 69296
                    ? (c >= 69248 && c <= 69289)
                    : c <= 69297)
                  : (c <= 69404 || (c < 69424
                    ? c == 69415
                    : c <= 69445)))
                : (c <= 69505 || (c < 69635
                  ? (c < 69600
                    ? (c >= 69552 && c <= 69572)
                    : c <= 69622)
                  : (c <= 69687 || (c >= 69745 && c <= 69746)))))
              : (c <= 69749 || (c < 69959
                ? (c < 69891
                  ? (c < 69840
                    ? (c >= 69763 && c <= 69807)
                    : c <= 69864)
                  : (c <= 69926 || c == 69956))
                : (c <= 69959 || (c < 70019
                  ? (c < 70006
                    ? (c >= 69968 && c <= 70002)
                    : c <= 70006)
                  : (c <= 70066 || (c >= 70081 && c <= 70084)))))))
            : (c <= 70106 || (c < 70405
              ? (c < 70280
                ? (c < 70163
                  ? (c < 70144
                    ? c == 70108
                    : c <= 70161)
                  : (c <= 70187 || (c >= 70272 && c <= 70278)))
                : (c <= 70280 || (c < 70303
                  ? (c < 70287
                    ? (c >= 70282 && c <= 70285)
                    : c <= 70301)
                  : (c <= 70312 || (c >= 70320 && c <= 70366)))))
              : (c <= 70412 || (c < 70453
                ? (c < 70442
                  ? (c < 70419
                    ? (c >= 70415 && c <= 70416)
                    : c <= 70440)
                  : (c <= 70448 || (c >= 70450 && c <= 70451)))
                : (c <= 70457 || (c < 70493
                  ? (c < 70480
                    ? c == 70461
                    : c <= 70480)
                  : (c <= 70497 || (c >= 70656 && c <= 70708)))))))))))))
      : (c <= 70730 || (c < 119894
        ? (c < 73056
          ? (c < 72001
            ? (c < 71424
              ? (c < 71128
                ? (c < 70852
                  ? (c < 70784
                    ? (c >= 70751 && c <= 70753)
                    : c <= 70831)
                  : (c <= 70853 || (c < 71040
                    ? c == 70855
                    : c <= 71086)))
                : (c <= 71131 || (c < 71296
                  ? (c < 71236
                    ? (c >= 71168 && c <= 71215)
                    : c <= 71236)
                  : (c <= 71338 || c == 71352))))
              : (c <= 71450 || (c < 71945
                ? (c < 71840
                  ? (c < 71680
                    ? (c >= 71488 && c <= 71494)
                    : c <= 71723)
                  : (c <= 71903 || (c >= 71935 && c <= 71942)))
                : (c <= 71945 || (c < 71960
                  ? (c < 71957
                    ? (c >= 71948 && c <= 71955)
                    : c <= 71958)
                  : (c <= 71983 || c == 71999))))))
            : (c <= 72001 || (c < 72349
              ? (c < 72192
                ? (c < 72161
                  ? (c < 72106
                    ? (c >= 72096 && c <= 72103)
                    : c <= 72144)
                  : (c <= 72161 || c == 72163))
                : (c <= 72192 || (c < 72272
                  ? (c < 72250
                    ? (c >= 72203 && c <= 72242)
                    : c <= 72250)
                  : (c <= 72272 || (c >= 72284 && c <= 72329)))))
              : (c <= 72349 || (c < 72818
                ? (c < 72714
                  ? (c < 72704
                    ? (c >= 72368 && c <= 72440)
                    : c <= 72712)
                  : (c <= 72750 || c == 72768))
                : (c <= 72847 || (c < 72971
                  ? (c < 72968
                    ? (c >= 72960 && c <= 72966)
                    : c <= 72969)
                  : (c <= 73008 || c == 73030))))))))
          : (c <= 73061 || (c < 93952
            ? (c < 82944
              ? (c < 73728
                ? (c < 73112
                  ? (c < 73066
                    ? (c >= 73063 && c <= 73064)
                    : c <= 73097)
                  : (c <= 73112 || (c < 73648
                    ? (c >= 73440 && c <= 73458)
                    : c <= 73648)))
                : (c <= 74649 || (c < 77712
                  ? (c < 74880
                    ? (c >= 74752 && c <= 74862)
                    : c <= 75075)
                  : (c <= 77808 || (c >= 77824 && c <= 78894)))))
              : (c <= 83526 || (c < 92928
                ? (c < 92784
                  ? (c < 92736
                    ? (c >= 92160 && c <= 92728)
                    : c <= 92766)
                  : (c <= 92862 || (c >= 92880 && c <= 92909)))
                : (c <= 92975 || (c < 93053
                  ? (c < 93027
                    ? (c >= 92992 && c <= 92995)
                    : c <= 93047)
                  : (c <= 93071 || (c >= 93760 && c <= 93823)))))))
            : (c <= 94026 || (c < 110589
              ? (c < 94208
                ? (c < 94176
                  ? (c < 94099
                    ? c == 94032
                    : c <= 94111)
                  : (c <= 94177 || c == 94179))
                : (c <= 100343 || (c < 110576
                  ? (c < 101632
                    ? (c >= 100352 && c <= 101589)
                    : c <= 101640)
                  : (c <= 110579 || (c >= 110581 && c <= 110587)))))
              : (c <= 110590 || (c < 113664
                ? (c < 110948
                  ? (c < 110928
                    ? (c >= 110592 && c <= 110882)
                    : c <= 110930)
                  : (c <= 110951 || (c >= 110960 && c <= 111355)))
                : (c <= 113770 || (c < 113808
                  ? (c < 113792
                    ? (c >= 113776 && c <= 113788)
                    : c <= 113800)
                  : (c <= 113817 || (c >= 119808 && c <= 119892)))))))))))
        : (c <= 119964 || (c < 125259
          ? (c < 120572
            ? (c < 120086
              ? (c < 119995
                ? (c < 119973
                  ? (c < 119970
                    ? (c >= 119966 && c <= 119967)
                    : c <= 119970)
                  : (c <= 119974 || (c < 119982
                    ? (c >= 119977 && c <= 119980)
                    : c <= 119993)))
                : (c <= 119995 || (c < 120071
                  ? (c < 120005
                    ? (c >= 119997 && c <= 120003)
                    : c <= 120069)
                  : (c <= 120074 || (c >= 120077 && c <= 120084)))))
              : (c <= 120092 || (c < 120138
                ? (c < 120128
                  ? (c < 120123
                    ? (c >= 120094 && c <= 120121)
                    : c <= 120126)
                  : (c <= 120132 || c == 120134))
                : (c <= 120144 || (c < 120514
                  ? (c < 120488
                    ? (c >= 120146 && c <= 120485)
                    : c <= 120512)
                  : (c <= 120538 || (c >= 120540 && c <= 120570)))))))
            : (c <= 120596 || (c < 123191
              ? (c < 120714
                ? (c < 120656
                  ? (c < 120630
                    ? (c >= 120598 && c <= 120628)
                    : c <= 120654)
                  : (c <= 120686 || (c >= 120688 && c <= 120712)))
                : (c <= 120744 || (c < 122624
                  ? (c < 120772
                    ? (c >= 120746 && c <= 120770)
                    : c <= 120779)
                  : (c <= 122654 || (c >= 123136 && c <= 123180)))))
              : (c <= 123197 || (c < 124904
                ? (c < 123584
                  ? (c < 123536
                    ? c == 123214
                    : c <= 123565)
                  : (c <= 123627 || (c >= 124896 && c <= 124902)))
                : (c <= 124907 || (c < 124928
                  ? (c < 124912
                    ? (c >= 124909 && c <= 124910)
                    : c <= 124926)
                  : (c <= 125124 || (c >= 125184 && c <= 125251)))))))))
          : (c <= 125259 || (c < 126559
            ? (c < 126535
              ? (c < 126505
                ? (c < 126497
                  ? (c < 126469
                    ? (c >= 126464 && c <= 126467)
                    : c <= 126495)
                  : (c <= 126498 || (c < 126503
                    ? c == 126500
                    : c <= 126503)))
                : (c <= 126514 || (c < 126523
                  ? (c < 126521
                    ? (c >= 126516 && c <= 126519)
                    : c <= 126521)
                  : (c <= 126523 || c == 126530))))
              : (c <= 126535 || (c < 126548
                ? (c < 126541
                  ? (c < 126539
                    ? c == 126537
                    : c <= 126539)
                  : (c <= 126543 || (c >= 126545 && c <= 126546)))
                : (c <= 126548 || (c < 126555
                  ? (c < 126553
                    ? c == 126551
                    : c <= 126553)
                  : (c <= 126555 || c == 126557))))))
            : (c <= 126559 || (c < 126625
              ? (c < 126580
                ? (c < 126567
                  ? (c < 126564
                    ? (c >= 126561 && c <= 126562)
                    : c <= 126564)
                  : (c <= 126570 || (c >= 126572 && c <= 126578)))
                : (c <= 126583 || (c < 126592
                  ? (c < 126590
                    ? (c >= 126585 && c <= 126588)
                    : c <= 126590)
                  : (c <= 126601 || (c >= 126603 && c <= 126619)))))
              : (c <= 126627 || (c < 177984
                ? (c < 131072
                  ? (c < 126635
                    ? (c >= 126629 && c <= 126633)
                    : c <= 126651)
                  : (c <= 173791 || (c >= 173824 && c <= 177976)))
                : (c <= 178205 || (c < 194560
                  ? (c < 183984
                    ? (c >= 178208 && c <= 183969)
                    : c <= 191456)
                  : (c <= 195101 || (c >= 196608 && c <= 201546)))))))))))))))));
}

static inline bool sym_name_character_set_4(int32_t c) {
  return (c < 43616
    ? (c < 3782
      ? (c < 2748
        ? (c < 2045
          ? (c < 1015
            ? (c < 710
              ? (c < 181
                ? (c < '_'
                  ? (c < 'A'
                    ? (c >= '0' && c <= '9')
                    : c <= 'Z')
                  : (c <= '_' || (c < 170
                    ? (c >= 'a' && c <= 'z')
                    : c <= 170)))
                : (c <= 181 || (c < 192
                  ? (c < 186
                    ? c == 183
                    : c <= 186)
                  : (c <= 214 || (c < 248
                    ? (c >= 216 && c <= 246)
                    : c <= 705)))))
              : (c <= 721 || (c < 891
                ? (c < 750
                  ? (c < 748
                    ? (c >= 736 && c <= 740)
                    : c <= 748)
                  : (c <= 750 || (c < 886
                    ? (c >= 768 && c <= 884)
                    : c <= 887)))
                : (c <= 893 || (c < 908
                  ? (c < 902
                    ? c == 895
                    : c <= 906)
                  : (c <= 908 || (c < 931
                    ? (c >= 910 && c <= 929)
                    : c <= 1013)))))))
            : (c <= 1153 || (c < 1519
              ? (c < 1425
                ? (c < 1329
                  ? (c < 1162
                    ? (c >= 1155 && c <= 1159)
                    : c <= 1327)
                  : (c <= 1366 || (c < 1376
                    ? c == 1369
                    : c <= 1416)))
                : (c <= 1469 || (c < 1476
                  ? (c < 1473
                    ? c == 1471
                    : c <= 1474)
                  : (c <= 1477 || (c < 1488
                    ? c == 1479
                    : c <= 1514)))))
              : (c <= 1522 || (c < 1770
                ? (c < 1646
                  ? (c < 1568
                    ? (c >= 1552 && c <= 1562)
                    : c <= 1641)
                  : (c <= 1747 || (c < 1759
                    ? (c >= 1749 && c <= 1756)
                    : c <= 1768)))
                : (c <= 1788 || (c < 1869
                  ? (c < 1808
                    ? c == 1791
                    : c <= 1866)
                  : (c <= 1969 || (c < 2042
                    ? (c >= 1984 && c <= 2037)
                    : c <= 2042)))))))))
          : (c <= 2045 || (c < 2558
            ? (c < 2451
              ? (c < 2200
                ? (c < 2144
                  ? (c < 2112
                    ? (c >= 2048 && c <= 2093)
                    : c <= 2139)
                  : (c <= 2154 || (c < 2185
                    ? (c >= 2160 && c <= 2183)
                    : c <= 2190)))
                : (c <= 2273 || (c < 2417
                  ? (c < 2406
                    ? (c >= 2275 && c <= 2403)
                    : c <= 2415)
                  : (c <= 2435 || (c < 2447
                    ? (c >= 2437 && c <= 2444)
                    : c <= 2448)))))
              : (c <= 2472 || (c < 2507
                ? (c < 2486
                  ? (c < 2482
                    ? (c >= 2474 && c <= 2480)
                    : c <= 2482)
                  : (c <= 2489 || (c < 2503
                    ? (c >= 2492 && c <= 2500)
                    : c <= 2504)))
                : (c <= 2510 || (c < 2527
                  ? (c < 2524
                    ? c == 2519
                    : c <= 2525)
                  : (c <= 2531 || (c < 2556
                    ? (c >= 2534 && c <= 2545)
                    : c <= 2556)))))))
            : (c <= 2558 || (c < 2635
              ? (c < 2610
                ? (c < 2575
                  ? (c < 2565
                    ? (c >= 2561 && c <= 2563)
                    : c <= 2570)
                  : (c <= 2576 || (c < 2602
                    ? (c >= 2579 && c <= 2600)
                    : c <= 2608)))
                : (c <= 2611 || (c < 2620
                  ? (c < 2616
                    ? (c >= 2613 && c <= 2614)
                    : c <= 2617)
                  : (c <= 2620 || (c < 2631
                    ? (c >= 2622 && c <= 2626)
                    : c <= 2632)))))
              : (c <= 2637 || (c < 2693
                ? (c < 2654
                  ? (c < 2649
                    ? c == 2641
                    : c <= 2652)
                  : (c <= 2654 || (c < 2689
                    ? (c >= 2662 && c <= 2677)
                    : c <= 2691)))
                : (c <= 2701 || (c < 2730
                  ? (c < 2707
                    ? (c >= 2703 && c <= 2705)
                    : c <= 2728)
                  : (c <= 2736 || (c < 2741
                    ? (c >= 2738 && c <= 2739)
                    : c <= 2745)))))))))))
        : (c <= 2757 || (c < 3168
          ? (c < 2958
            ? (c < 2866
              ? (c < 2809
                ? (c < 2768
                  ? (c < 2763
                    ? (c >= 2759 && c <= 2761)
                    : c <= 2765)
                  : (c <= 2768 || (c < 2790
                    ? (c >= 2784 && c <= 2787)
                    : c <= 2799)))
                : (c <= 2815 || (c < 2831
                  ? (c < 2821
                    ? (c >= 2817 && c <= 2819)
                    : c <= 2828)
                  : (c <= 2832 || (c < 2858
                    ? (c >= 2835 && c <= 2856)
                    : c <= 2864)))))
              : (c <= 2867 || (c < 2908
                ? (c < 2887
                  ? (c < 2876
                    ? (c >= 2869 && c <= 2873)
                    : c <= 2884)
                  : (c <= 2888 || (c < 2901
                    ? (c >= 2891 && c <= 2893)
                    : c <= 2903)))
                : (c <= 2909 || (c < 2929
                  ? (c < 2918
                    ? (c >= 2911 && c <= 2915)
                    : c <= 2927)
                  : (c <= 2929 || (c < 2949
                    ? (c >= 2946 && c <= 2947)
                    : c <= 2954)))))))
            : (c <= 2960 || (c < 3031
              ? (c < 2984
                ? (c < 2972
                  ? (c < 2969
                    ? (c >= 2962 && c <= 2965)
                    : c <= 2970)
                  : (c <= 2972 || (c < 2979
                    ? (c >= 2974 && c <= 2975)
                    : c <= 2980)))
                : (c <= 2986 || (c < 3014
                  ? (c < 3006
                    ? (c >= 2990 && c <= 3001)
                    : c <= 3010)
                  : (c <= 3016 || (c < 3024
                    ? (c >= 3018 && c <= 3021)
                    : c <= 3024)))))
              : (c <= 3031 || (c < 3132
                ? (c < 3086
                  ? (c < 3072
                    ? (c >= 3046 && c <= 3055)
                    : c <= 3084)
                  : (c <= 3088 || (c < 3114
                    ? (c >= 3090 && c <= 3112)
                    : c <= 3129)))
                : (c <= 3140 || (c < 3157
                  ? (c < 3146
                    ? (c >= 3142 && c <= 3144)
                    : c <= 3149)
                  : (c <= 3158 || (c < 3165
                    ? (c >= 3160 && c <= 3162)
                    : c <= 3165)))))))))
          : (c <= 3171 || (c < 3450
            ? (c < 3293
              ? (c < 3242
                ? (c < 3205
                  ? (c < 3200
                    ? (c >= 3174 && c <= 3183)
                    : c <= 3203)
                  : (c <= 3212 || (c < 3218
                    ? (c >= 3214 && c <= 3216)
                    : c <= 3240)))
                : (c <= 3251 || (c < 3270
                  ? (c < 3260
                    ? (c >= 3253 && c <= 3257)
                    : c <= 3268)
                  : (c <= 3272 || (c < 3285
                    ? (c >= 3274 && c <= 3277)
                    : c <= 3286)))))
              : (c <= 3294 || (c < 3346
                ? (c < 3313
                  ? (c < 3302
                    ? (c >= 3296 && c <= 3299)
                    : c <= 3311)
                  : (c <= 3314 || (c < 3342
                    ? (c >= 3328 && c <= 3340)
                    : c <= 3344)))
                : (c <= 3396 || (c < 3412
                  ? (c < 3402
                    ? (c >= 3398 && c <= 3400)
                    : c <= 3406)
                  : (c <= 3415 || (c < 3430
                    ? (c >= 3423 && c <= 3427)
                    : c <= 3439)))))))
            : (c <= 3455 || (c < 3570
              ? (c < 3520
                ? (c < 3482
                  ? (c < 3461
                    ? (c >= 3457 && c <= 3459)
                    : c <= 3478)
                  : (c <= 3505 || (c < 3517
                    ? (c >= 3507 && c <= 3515)
                    : c <= 3517)))
                : (c <= 3526 || (c < 3542
                  ? (c < 3535
                    ? c == 3530
                    : c <= 3540)
                  : (c <= 3542 || (c < 3558
                    ? (c >= 3544 && c <= 3551)
                    : c <= 3567)))))
              : (c <= 3571 || (c < 3718
                ? (c < 3664
                  ? (c < 3648
                    ? (c >= 3585 && c <= 3642)
                    : c <= 3662)
                  : (c <= 3673 || (c < 3716
                    ? (c >= 3713 && c <= 3714)
                    : c <= 3716)))
                : (c <= 3722 || (c < 3751
                  ? (c < 3749
                    ? (c >= 3724 && c <= 3747)
                    : c <= 3749)
                  : (c <= 3773 || (c >= 3776 && c <= 3780)))))))))))))
      : (c <= 3782 || (c < 8025
        ? (c < 5888
          ? (c < 4688
            ? (c < 3953
              ? (c < 3872
                ? (c < 3804
                  ? (c < 3792
                    ? (c >= 3784 && c <= 3789)
                    : c <= 3801)
                  : (c <= 3807 || (c < 3864
                    ? c == 3840
                    : c <= 3865)))
                : (c <= 3881 || (c < 3897
                  ? (c < 3895
                    ? c == 3893
                    : c <= 3895)
                  : (c <= 3897 || (c < 3913
                    ? (c >= 3902 && c <= 3911)
                    : c <= 3948)))))
              : (c <= 3972 || (c < 4256
                ? (c < 4038
                  ? (c < 3993
                    ? (c >= 3974 && c <= 3991)
                    : c <= 4028)
                  : (c <= 4038 || (c < 4176
                    ? (c >= 4096 && c <= 4169)
                    : c <= 4253)))
                : (c <= 4293 || (c < 4304
                  ? (c < 4301
                    ? c == 4295
                    : c <= 4301)
                  : (c <= 4346 || (c < 4682
                    ? (c >= 4348 && c <= 4680)
                    : c <= 4685)))))))
            : (c <= 4694 || (c < 4882
              ? (c < 4786
                ? (c < 4704
                  ? (c < 4698
                    ? c == 4696
                    : c <= 4701)
                  : (c <= 4744 || (c < 4752
                    ? (c >= 4746 && c <= 4749)
                    : c <= 4784)))
                : (c <= 4789 || (c < 4802
                  ? (c < 4800
                    ? (c >= 4792 && c <= 4798)
                    : c <= 4800)
                  : (c <= 4805 || (c < 4824
                    ? (c >= 4808 && c <= 4822)
                    : c <= 4880)))))
              : (c <= 4885 || (c < 5112
                ? (c < 4969
                  ? (c < 4957
                    ? (c >= 4888 && c <= 4954)
                    : c <= 4959)
                  : (c <= 4977 || (c < 5024
                    ? (c >= 4992 && c <= 5007)
                    : c <= 5109)))
                : (c <= 5117 || (c < 5761
                  ? (c < 5743
                    ? (c >= 5121 && c <= 5740)
                    : c <= 5759)
                  : (c <= 5786 || (c < 5870
                    ? (c >= 5792 && c <= 5866)
                    : c <= 5880)))))))))
          : (c <= 5909 || (c < 6688
            ? (c < 6176
              ? (c < 6016
                ? (c < 5984
                  ? (c < 5952
                    ? (c >= 5919 && c <= 5940)
                    : c <= 5971)
                  : (c <= 5996 || (c < 6002
                    ? (c >= 5998 && c <= 6000)
                    : c <= 6003)))
                : (c <= 6099 || (c < 6112
                  ? (c < 6108
                    ? c == 6103
                    : c <= 6109)
                  : (c <= 6121 || (c < 6159
                    ? (c >= 6155 && c <= 6157)
                    : c <= 6169)))))
              : (c <= 6264 || (c < 6470
                ? (c < 6400
                  ? (c < 6320
                    ? (c >= 6272 && c <= 6314)
                    : c <= 6389)
                  : (c <= 6430 || (c < 6448
                    ? (c >= 6432 && c <= 6443)
                    : c <= 6459)))
                : (c <= 6509 || (c < 6576
                  ? (c < 6528
                    ? (c >= 6512 && c <= 6516)
                    : c <= 6571)
                  : (c <= 6601 || (c < 6656
                    ? (c >= 6608 && c <= 6618)
                    : c <= 6683)))))))
            : (c <= 6750 || (c < 7232
              ? (c < 6847
                ? (c < 6800
                  ? (c < 6783
                    ? (c >= 6752 && c <= 6780)
                    : c <= 6793)
                  : (c <= 6809 || (c < 6832
                    ? c == 6823
                    : c <= 6845)))
                : (c <= 6862 || (c < 7019
                  ? (c < 6992
                    ? (c >= 6912 && c <= 6988)
                    : c <= 7001)
                  : (c <= 7027 || (c < 7168
                    ? (c >= 7040 && c <= 7155)
                    : c <= 7223)))))
              : (c <= 7241 || (c < 7380
                ? (c < 7312
                  ? (c < 7296
                    ? (c >= 7245 && c <= 7293)
                    : c <= 7304)
                  : (c <= 7354 || (c < 7376
                    ? (c >= 7357 && c <= 7359)
                    : c <= 7378)))
                : (c <= 7418 || (c < 7968
                  ? (c < 7960
                    ? (c >= 7424 && c <= 7957)
                    : c <= 7965)
                  : (c <= 8005 || (c < 8016
                    ? (c >= 8008 && c <= 8013)
                    : c <= 8023)))))))))))
        : (c <= 8025 || (c < 11720
          ? (c < 8458
            ? (c < 8178
              ? (c < 8126
                ? (c < 8031
                  ? (c < 8029
                    ? c == 8027
                    : c <= 8029)
                  : (c <= 8061 || (c < 8118
                    ? (c >= 8064 && c <= 8116)
                    : c <= 8124)))
                : (c <= 8126 || (c < 8144
                  ? (c < 8134
                    ? (c >= 8130 && c <= 8132)
                    : c <= 8140)
                  : (c <= 8147 || (c < 8160
                    ? (c >= 8150 && c <= 8155)
                    : c <= 8172)))))
              : (c <= 8180 || (c < 8336
                ? (c < 8276
                  ? (c < 8255
                    ? (c >= 8182 && c <= 8188)
                    : c <= 8256)
                  : (c <= 8276 || (c < 8319
                    ? c == 8305
                    : c <= 8319)))
                : (c <= 8348 || (c < 8421
                  ? (c < 8417
                    ? (c >= 8400 && c <= 8412)
                    : c <= 8417)
                  : (c <= 8432 || (c < 8455
                    ? c == 8450
                    : c <= 8455)))))))
            : (c <= 8467 || (c < 11499
              ? (c < 8490
                ? (c < 8484
                  ? (c < 8472
                    ? c == 8469
                    : c <= 8477)
                  : (c <= 8484 || (c < 8488
                    ? c == 8486
                    : c <= 8488)))
                : (c <= 8505 || (c < 8526
                  ? (c < 8517
                    ? (c >= 8508 && c <= 8511)
                    : c <= 8521)
                  : (c <= 8526 || (c < 11264
                    ? (c >= 8544 && c <= 8584)
                    : c <= 11492)))))
              : (c <= 11507 || (c < 11647
                ? (c < 11565
                  ? (c < 11559
                    ? (c >= 11520 && c <= 11557)
                    : c <= 11559)
                  : (c <= 11565 || (c < 11631
                    ? (c >= 11568 && c <= 11623)
                    : c <= 11631)))
                : (c <= 11670 || (c < 11696
                  ? (c < 11688
                    ? (c >= 11680 && c <= 11686)
                    : c <= 11694)
                  : (c <= 11702 || (c < 11712
                    ? (c >= 11704 && c <= 11710)
                    : c <= 11718)))))))))
          : (c <= 11726 || (c < 42623
            ? (c < 12540
              ? (c < 12337
                ? (c < 11744
                  ? (c < 11736
                    ? (c >= 11728 && c <= 11734)
                    : c <= 11742)
                  : (c <= 11775 || (c < 12321
                    ? (c >= 12293 && c <= 12295)
                    : c <= 12335)))
                : (c <= 12341 || (c < 12441
                  ? (c < 12353
                    ? (c >= 12344 && c <= 12348)
                    : c <= 12438)
                  : (c <= 12442 || (c < 12449
                    ? (c >= 12445 && c <= 12447)
                    : c <= 12538)))))
              : (c <= 12543 || (c < 19968
                ? (c < 12704
                  ? (c < 12593
                    ? (c >= 12549 && c <= 12591)
                    : c <= 12686)
                  : (c <= 12735 || (c < 13312
                    ? (c >= 12784 && c <= 12799)
                    : c <= 19903)))
                : (c <= 42124 || (c < 42512
                  ? (c < 42240
                    ? (c >= 42192 && c <= 42237)
                    : c <= 42508)
                  : (c <= 42539 || (c < 42612
                    ? (c >= 42560 && c <= 42607)
                    : c <= 42621)))))))
            : (c <= 42737 || (c < 43232
              ? (c < 42965
                ? (c < 42891
                  ? (c < 42786
                    ? (c >= 42775 && c <= 42783)
                    : c <= 42888)
                  : (c <= 42954 || (c < 42963
                    ? (c >= 42960 && c <= 42961)
                    : c <= 42963)))
                : (c <= 42969 || (c < 43072
                  ? (c < 43052
                    ? (c >= 42994 && c <= 43047)
                    : c <= 43052)
                  : (c <= 43123 || (c < 43216
                    ? (c >= 43136 && c <= 43205)
                    : c <= 43225)))))
              : (c <= 43255 || (c < 43471
                ? (c < 43312
                  ? (c < 43261
                    ? c == 43259
                    : c <= 43309)
                  : (c <= 43347 || (c < 43392
                    ? (c >= 43360 && c <= 43388)
                    : c <= 43456)))
                : (c <= 43481 || (c < 43584
                  ? (c < 43520
                    ? (c >= 43488 && c <= 43518)
                    : c <= 43574)
                  : (c <= 43597 || (c >= 43600 && c <= 43609)))))))))))))))
    : (c <= 43638 || (c < 71453
      ? (c < 67639
        ? (c < 65345
          ? (c < 64312
            ? (c < 43888
              ? (c < 43785
                ? (c < 43744
                  ? (c < 43739
                    ? (c >= 43642 && c <= 43714)
                    : c <= 43741)
                  : (c <= 43759 || (c < 43777
                    ? (c >= 43762 && c <= 43766)
                    : c <= 43782)))
                : (c <= 43790 || (c < 43816
                  ? (c < 43808
                    ? (c >= 43793 && c <= 43798)
                    : c <= 43814)
                  : (c <= 43822 || (c < 43868
                    ? (c >= 43824 && c <= 43866)
                    : c <= 43881)))))
              : (c <= 44010 || (c < 63744
                ? (c < 44032
                  ? (c < 44016
                    ? (c >= 44012 && c <= 44013)
                    : c <= 44025)
                  : (c <= 55203 || (c < 55243
                    ? (c >= 55216 && c <= 55238)
                    : c <= 55291)))
                : (c <= 64109 || (c < 64275
                  ? (c < 64256
                    ? (c >= 64112 && c <= 64217)
                    : c <= 64262)
                  : (c <= 64279 || (c < 64298
                    ? (c >= 64285 && c <= 64296)
                    : c <= 64310)))))))
            : (c <= 64316 || (c < 65075
              ? (c < 64612
                ? (c < 64323
                  ? (c < 64320
                    ? c == 64318
                    : c <= 64321)
                  : (c <= 64324 || (c < 64467
                    ? (c >= 64326 && c <= 64433)
                    : c <= 64605)))
                : (c <= 64829 || (c < 65008
                  ? (c < 64914
                    ? (c >= 64848 && c <= 64911)
                    : c <= 64967)
                  : (c <= 65017 || (c < 65056
                    ? (c >= 65024 && c <= 65039)
                    : c <= 65071)))))
              : (c <= 65076 || (c < 65147
                ? (c < 65139
                  ? (c < 65137
                    ? (c >= 65101 && c <= 65103)
                    : c <= 65137)
                  : (c <= 65139 || (c < 65145
                    ? c == 65143
                    : c <= 65145)))
                : (c <= 65147 || (c < 65296
                  ? (c < 65151
                    ? c == 65149
                    : c <= 65276)
                  : (c <= 65305 || (c < 65343
                    ? (c >= 65313 && c <= 65338)
                    : c <= 65343)))))))))
          : (c <= 65370 || (c < 66513
            ? (c < 65664
              ? (c < 65536
                ? (c < 65482
                  ? (c < 65474
                    ? (c >= 65382 && c <= 65470)
                    : c <= 65479)
                  : (c <= 65487 || (c < 65498
                    ? (c >= 65490 && c <= 65495)
                    : c <= 65500)))
                : (c <= 65547 || (c < 65596
                  ? (c < 65576
                    ? (c >= 65549 && c <= 65574)
                    : c <= 65594)
                  : (c <= 65597 || (c < 65616
                    ? (c >= 65599 && c <= 65613)
                    : c <= 65629)))))
              : (c <= 65786 || (c < 66304
                ? (c < 66176
                  ? (c < 66045
                    ? (c >= 65856 && c <= 65908)
                    : c <= 66045)
                  : (c <= 66204 || (c < 66272
                    ? (c >= 66208 && c <= 66256)
                    : c <= 66272)))
                : (c <= 66335 || (c < 66432
                  ? (c < 66384
                    ? (c >= 66349 && c <= 66378)
                    : c <= 66426)
                  : (c <= 66461 || (c < 66504
                    ? (c >= 66464 && c <= 66499)
                    : c <= 66511)))))))
            : (c <= 66517 || (c < 66979
              ? (c < 66864
                ? (c < 66736
                  ? (c < 66720
                    ? (c >= 66560 && c <= 66717)
                    : c <= 66729)
                  : (c <= 66771 || (c < 66816
                    ? (c >= 66776 && c <= 66811)
                    : c <= 66855)))
                : (c <= 66915 || (c < 66956
                  ? (c < 66940
                    ? (c >= 66928 && c <= 66938)
                    : c <= 66954)
                  : (c <= 66962 || (c < 66967
                    ? (c >= 66964 && c <= 66965)
                    : c <= 66977)))))
              : (c <= 66993 || (c < 67456
                ? (c < 67072
                  ? (c < 67003
                    ? (c >= 66995 && c <= 67001)
                    : c <= 67004)
                  : (c <= 67382 || (c < 67424
                    ? (c >= 67392 && c <= 67413)
                    : c <= 67431)))
                : (c <= 67461 || (c < 67584
                  ? (c < 67506
                    ? (c >= 67463 && c <= 67504)
                    : c <= 67514)
                  : (c <= 67589 || (c < 67594
                    ? c == 67592
                    : c <= 67637)))))))))))
        : (c <= 67640 || (c < 69956
          ? (c < 68448
            ? (c < 68101
              ? (c < 67828
                ? (c < 67680
                  ? (c < 67647
                    ? c == 67644
                    : c <= 67669)
                  : (c <= 67702 || (c < 67808
                    ? (c >= 67712 && c <= 67742)
                    : c <= 67826)))
                : (c <= 67829 || (c < 67968
                  ? (c < 67872
                    ? (c >= 67840 && c <= 67861)
                    : c <= 67897)
                  : (c <= 68023 || (c < 68096
                    ? (c >= 68030 && c <= 68031)
                    : c <= 68099)))))
              : (c <= 68102 || (c < 68192
                ? (c < 68121
                  ? (c < 68117
                    ? (c >= 68108 && c <= 68115)
                    : c <= 68119)
                  : (c <= 68149 || (c < 68159
                    ? (c >= 68152 && c <= 68154)
                    : c <= 68159)))
                : (c <= 68220 || (c < 68297
                  ? (c < 68288
                    ? (c >= 68224 && c <= 68252)
                    : c <= 68295)
                  : (c <= 68326 || (c < 68416
                    ? (c >= 68352 && c <= 68405)
                    : c <= 68437)))))))
            : (c <= 68466 || (c < 69424
              ? (c < 68912
                ? (c < 68736
                  ? (c < 68608
                    ? (c >= 68480 && c <= 68497)
                    : c <= 68680)
                  : (c <= 68786 || (c < 68864
                    ? (c >= 68800 && c <= 68850)
                    : c <= 68903)))
                : (c <= 68921 || (c < 69296
                  ? (c < 69291
                    ? (c >= 69248 && c <= 69289)
                    : c <= 69292)
                  : (c <= 69297 || (c < 69415
                    ? (c >= 69376 && c <= 69404)
                    : c <= 69415)))))
              : (c <= 69456 || (c < 69759
                ? (c < 69600
                  ? (c < 69552
                    ? (c >= 69488 && c <= 69509)
                    : c <= 69572)
                  : (c <= 69622 || (c < 69734
                    ? (c >= 69632 && c <= 69702)
                    : c <= 69749)))
                : (c <= 69818 || (c < 69872
                  ? (c < 69840
                    ? c == 69826
                    : c <= 69864)
                  : (c <= 69881 || (c < 69942
                    ? (c >= 69888 && c <= 69940)
                    : c <= 69951)))))))))
          : (c <= 69959 || (c < 70459
            ? (c < 70282
              ? (c < 70108
                ? (c < 70016
                  ? (c < 70006
                    ? (c >= 69968 && c <= 70003)
                    : c <= 70006)
                  : (c <= 70084 || (c < 70094
                    ? (c >= 70089 && c <= 70092)
                    : c <= 70106)))
                : (c <= 70108 || (c < 70206
                  ? (c < 70163
                    ? (c >= 70144 && c <= 70161)
                    : c <= 70199)
                  : (c <= 70206 || (c < 70280
                    ? (c >= 70272 && c <= 70278)
                    : c <= 70280)))))
              : (c <= 70285 || (c < 70405
                ? (c < 70320
                  ? (c < 70303
                    ? (c >= 70287 && c <= 70301)
                    : c <= 70312)
                  : (c <= 70378 || (c < 70400
                    ? (c >= 70384 && c <= 70393)
                    : c <= 70403)))
                : (c <= 70412 || (c < 70442
                  ? (c < 70419
                    ? (c >= 70415 && c <= 70416)
                    : c <= 70440)
                  : (c <= 70448 || (c < 70453
                    ? (c >= 70450 && c <= 70451)
                    : c <= 70457)))))))
            : (c <= 70468 || (c < 70855
              ? (c < 70502
                ? (c < 70480
                  ? (c < 70475
                    ? (c >= 70471 && c <= 70472)
                    : c <= 70477)
                  : (c <= 70480 || (c < 70493
                    ? c == 70487
                    : c <= 70499)))
                : (c <= 70508 || (c < 70736
                  ? (c < 70656
                    ? (c >= 70512 && c <= 70516)
                    : c <= 70730)
                  : (c <= 70745 || (c < 70784
                    ? (c >= 70750 && c <= 70753)
                    : c <= 70853)))))
              : (c <= 70855 || (c < 71236
                ? (c < 71096
                  ? (c < 71040
                    ? (c >= 70864 && c <= 70873)
                    : c <= 71093)
                  : (c <= 71104 || (c < 71168
                    ? (c >= 71128 && c <= 71133)
                    : c <= 71232)))
                : (c <= 71236 || (c < 71360
                  ? (c < 71296
                    ? (c >= 71248 && c <= 71257)
                    : c <= 71352)
                  : (c <= 71369 || (c >= 71424 && c <= 71450)))))))))))))
      : (c <= 71467 || (c < 119973
        ? (c < 77824
          ? (c < 72760
            ? (c < 72016
              ? (c < 71945
                ? (c < 71680
                  ? (c < 71488
                    ? (c >= 71472 && c <= 71481)
                    : c <= 71494)
                  : (c <= 71738 || (c < 71935
                    ? (c >= 71840 && c <= 71913)
                    : c <= 71942)))
                : (c <= 71945 || (c < 71960
                  ? (c < 71957
                    ? (c >= 71948 && c <= 71955)
                    : c <= 71958)
                  : (c <= 71989 || (c < 71995
                    ? (c >= 71991 && c <= 71992)
                    : c <= 72003)))))
              : (c <= 72025 || (c < 72263
                ? (c < 72154
                  ? (c < 72106
                    ? (c >= 72096 && c <= 72103)
                    : c <= 72151)
                  : (c <= 72161 || (c < 72192
                    ? (c >= 72163 && c <= 72164)
                    : c <= 72254)))
                : (c <= 72263 || (c < 72368
                  ? (c < 72349
                    ? (c >= 72272 && c <= 72345)
                    : c <= 72349)
                  : (c <= 72440 || (c < 72714
                    ? (c >= 72704 && c <= 72712)
                    : c <= 72758)))))))
            : (c <= 72768 || (c < 73056
              ? (c < 72968
                ? (c < 72850
                  ? (c < 72818
                    ? (c >= 72784 && c <= 72793)
                    : c <= 72847)
                  : (c <= 72871 || (c < 72960
                    ? (c >= 72873 && c <= 72886)
                    : c <= 72966)))
                : (c <= 72969 || (c < 73020
                  ? (c < 73018
                    ? (c >= 72971 && c <= 73014)
                    : c <= 73018)
                  : (c <= 73021 || (c < 73040
                    ? (c >= 73023 && c <= 73031)
                    : c <= 73049)))))
              : (c <= 73061 || (c < 73440
                ? (c < 73104
                  ? (c < 73066
                    ? (c >= 73063 && c <= 73064)
                    : c <= 73102)
                  : (c <= 73105 || (c < 73120
                    ? (c >= 73107 && c <= 73112)
                    : c <= 73129)))
                : (c <= 73462 || (c < 74752
                  ? (c < 73728
                    ? c == 73648
                    : c <= 74649)
                  : (c <= 74862 || (c < 77712
                    ? (c >= 74880 && c <= 75075)
                    : c <= 77808)))))))))
          : (c <= 78894 || (c < 110576
            ? (c < 93027
              ? (c < 92864
                ? (c < 92736
                  ? (c < 92160
                    ? (c >= 82944 && c <= 83526)
                    : c <= 92728)
                  : (c <= 92766 || (c < 92784
                    ? (c >= 92768 && c <= 92777)
                    : c <= 92862)))
                : (c <= 92873 || (c < 92928
                  ? (c < 92912
                    ? (c >= 92880 && c <= 92909)
                    : c <= 92916)
                  : (c <= 92982 || (c < 93008
                    ? (c >= 92992 && c <= 92995)
                    : c <= 93017)))))
              : (c <= 93047 || (c < 94176
                ? (c < 93952
                  ? (c < 93760
                    ? (c >= 93053 && c <= 93071)
                    : c <= 93823)
                  : (c <= 94026 || (c < 94095
                    ? (c >= 94031 && c <= 94087)
                    : c <= 94111)))
                : (c <= 94177 || (c < 94208
                  ? (c < 94192
                    ? (c >= 94179 && c <= 94180)
                    : c <= 94193)
                  : (c <= 100343 || (c < 101632
                    ? (c >= 100352 && c <= 101589)
                    : c <= 101640)))))))
            : (c <= 110579 || (c < 118528
              ? (c < 110960
                ? (c < 110592
                  ? (c < 110589
                    ? (c >= 110581 && c <= 110587)
                    : c <= 110590)
                  : (c <= 110882 || (c < 110948
                    ? (c >= 110928 && c <= 110930)
                    : c <= 110951)))
                : (c <= 111355 || (c < 113792
                  ? (c < 113776
                    ? (c >= 113664 && c <= 113770)
                    : c <= 113788)
                  : (c <= 113800 || (c < 113821
                    ? (c >= 113808 && c <= 113817)
                    : c <= 113822)))))
              : (c <= 118573 || (c < 119210
                ? (c < 119149
                  ? (c < 119141
                    ? (c >= 118576 && c <= 118598)
                    : c <= 119145)
                  : (c <= 119154 || (c < 119173
                    ? (c >= 119163 && c <= 119170)
                    : c <= 119179)))
                : (c <= 119213 || (c < 119894
                  ? (c < 119808
                    ? (c >= 119362 && c <= 119364)
                    : c <= 119892)
                  : (c <= 119964 || (c < 119970
                    ? (c >= 119966 && c <= 119967)
                    : c <= 119970)))))))))))
        : (c <= 119974 || (c < 124912
          ? (c < 120746
            ? (c < 120134
              ? (c < 120071
                ? (c < 119995
                  ? (c < 119982
                    ? (c >= 119977 && c <= 119980)
                    : c <= 119993)
                  : (c <= 119995 || (c < 120005
                    ? (c >= 119997 && c <= 120003)
                    : c <= 120069)))
                : (c <= 120074 || (c < 120094
                  ? (c < 120086
                    ? (c >= 120077 && c <= 120084)
                    : c <= 120092)
                  : (c <= 120121 || (c < 120128
                    ? (c >= 120123 && c <= 120126)
                    : c <= 120132)))))
              : (c <= 120134 || (c < 120572
                ? (c < 120488
                  ? (c < 120146
                    ? (c >= 120138 && c <= 120144)
                    : c <= 120485)
                  : (c <= 120512 || (c < 120540
                    ? (c >= 120514 && c <= 120538)
                    : c <= 120570)))
                : (c <= 120596 || (c < 120656
                  ? (c < 120630
                    ? (c >= 120598 && c <= 120628)
                    : c <= 120654)
                  : (c <= 120686 || (c < 120714
                    ? (c >= 120688 && c <= 120712)
                    : c <= 120744)))))))
            : (c <= 120770 || (c < 122907
              ? (c < 121476
                ? (c < 121344
                  ? (c < 120782
                    ? (c >= 120772 && c <= 120779)
                    : c <= 120831)
                  : (c <= 121398 || (c < 121461
                    ? (c >= 121403 && c <= 121452)
                    : c <= 121461)))
                : (c <= 121476 || (c < 122624
                  ? (c < 121505
                    ? (c >= 121499 && c <= 121503)
                    : c <= 121519)
                  : (c <= 122654 || (c < 122888
                    ? (c >= 122880 && c <= 122886)
                    : c <= 122904)))))
              : (c <= 122913 || (c < 123214
                ? (c < 123136
                  ? (c < 122918
                    ? (c >= 122915 && c <= 122916)
                    : c <= 122922)
                  : (c <= 123180 || (c < 123200
                    ? (c >= 123184 && c <= 123197)
                    : c <= 123209)))
                : (c <= 123214 || (c < 124896
                  ? (c < 123584
                    ? (c >= 123536 && c <= 123566)
                    : c <= 123641)
                  : (c <= 124902 || (c < 124909
                    ? (c >= 124904 && c <= 124907)
                    : c <= 124910)))))))))
          : (c <= 124926 || (c < 126557
            ? (c < 126521
              ? (c < 126469
                ? (c < 125184
                  ? (c < 125136
                    ? (c >= 124928 && c <= 125124)
                    : c <= 125142)
                  : (c <= 125259 || (c < 126464
                    ? (c >= 125264 && c <= 125273)
                    : c <= 126467)))
                : (c <= 126495 || (c < 126503
                  ? (c < 126500
                    ? (c >= 126497 && c <= 126498)
                    : c <= 126500)
                  : (c <= 126503 || (c < 126516
                    ? (c >= 126505 && c <= 126514)
                    : c <= 126519)))))
              : (c <= 126521 || (c < 126541
                ? (c < 126535
                  ? (c < 126530
                    ? c == 126523
                    : c <= 126530)
                  : (c <= 126535 || (c < 126539
                    ? c == 126537
                    : c <= 126539)))
                : (c <= 126543 || (c < 126551
                  ? (c < 126548
                    ? (c >= 126545 && c <= 126546)
                    : c <= 126548)
                  : (c <= 126551 || (c < 126555
                    ? c == 126553
                    : c <= 126555)))))))
            : (c <= 126557 || (c < 126629
              ? (c < 126580
                ? (c < 126564
                  ? (c < 126561
                    ? c == 126559
                    : c <= 126562)
                  : (c <= 126564 || (c < 126572
                    ? (c >= 126567 && c <= 126570)
                    : c <= 126578)))
                : (c <= 126583 || (c < 126592
                  ? (c < 126590
                    ? (c >= 126585 && c <= 126588)
                    : c <= 126590)
                  : (c <= 126601 || (c < 126625
                    ? (c >= 126603 && c <= 126619)
                    : c <= 126627)))))
              : (c <= 126633 || (c < 178208
                ? (c < 131072
                  ? (c < 130032
                    ? (c >= 126635 && c <= 126651)
                    : c <= 130041)
                  : (c <= 173791 || (c < 177984
                    ? (c >= 173824 && c <= 177976)
                    : c <= 178205)))
                : (c <= 183969 || (c < 196608
                  ? (c < 194560
                    ? (c >= 183984 && c <= 191456)
                    : c <= 195101)
                  : (c <= 201546 || (c >= 917760 && c <= 917999)))))))))))))))));
}

static inline bool sym_name_character_set_5(int32_t c) {
  return (c < 43616
    ? (c < 3782
      ? (c < 2748
        ? (c < 2045
          ? (c < 1015
            ? (c < 710
              ? (c < 181
                ? (c < '_'
                  ? (c < 'B'
                    ? (c >= '0' && c <= '9')
                    : c <= 'Z')
                  : (c <= '_' || (c < 170
                    ? (c >= 'a' && c <= 'z')
                    : c <= 170)))
                : (c <= 181 || (c < 192
                  ? (c < 186
                    ? c == 183
                    : c <= 186)
                  : (c <= 214 || (c < 248
                    ? (c >= 216 && c <= 246)
                    : c <= 705)))))
              : (c <= 721 || (c < 891
                ? (c < 750
                  ? (c < 748
                    ? (c >= 736 && c <= 740)
                    : c <= 748)
                  : (c <= 750 || (c < 886
                    ? (c >= 768 && c <= 884)
                    : c <= 887)))
                : (c <= 893 || (c < 908
                  ? (c < 902
                    ? c == 895
                    : c <= 906)
                  : (c <= 908 || (c < 931
                    ? (c >= 910 && c <= 929)
                    : c <= 1013)))))))
            : (c <= 1153 || (c < 1519
              ? (c < 1425
                ? (c < 1329
                  ? (c < 1162
                    ? (c >= 1155 && c <= 1159)
                    : c <= 1327)
                  : (c <= 1366 || (c < 1376
                    ? c == 1369
                    : c <= 1416)))
                : (c <= 1469 || (c < 1476
                  ? (c < 1473
                    ? c == 1471
                    : c <= 1474)
                  : (c <= 1477 || (c < 1488
                    ? c == 1479
                    : c <= 1514)))))
              : (c <= 1522 || (c < 1770
                ? (c < 1646
                  ? (c < 1568
                    ? (c >= 1552 && c <= 1562)
                    : c <= 1641)
                  : (c <= 1747 || (c < 1759
                    ? (c >= 1749 && c <= 1756)
                    : c <= 1768)))
                : (c <= 1788 || (c < 1869
                  ? (c < 1808
                    ? c == 1791
                    : c <= 1866)
                  : (c <= 1969 || (c < 2042
                    ? (c >= 1984 && c <= 2037)
                    : c <= 2042)))))))))
          : (c <= 2045 || (c < 2558
            ? (c < 2451
              ? (c < 2200
                ? (c < 2144
                  ? (c < 2112
                    ? (c >= 2048 && c <= 2093)
                    : c <= 2139)
                  : (c <= 2154 || (c < 2185
                    ? (c >= 2160 && c <= 2183)
                    : c <= 2190)))
                : (c <= 2273 || (c < 2417
                  ? (c < 2406
                    ? (c >= 2275 && c <= 2403)
                    : c <= 2415)
                  : (c <= 2435 || (c < 2447
                    ? (c >= 2437 && c <= 2444)
                    : c <= 2448)))))
              : (c <= 2472 || (c < 2507
                ? (c < 2486
                  ? (c < 2482
                    ? (c >= 2474 && c <= 2480)
                    : c <= 2482)
                  : (c <= 2489 || (c < 2503
                    ? (c >= 2492 && c <= 2500)
                    : c <= 2504)))
                : (c <= 2510 || (c < 2527
                  ? (c < 2524
                    ? c == 2519
                    : c <= 2525)
                  : (c <= 2531 || (c < 2556
                    ? (c >= 2534 && c <= 2545)
                    : c <= 2556)))))))
            : (c <= 2558 || (c < 2635
              ? (c < 2610
                ? (c < 2575
                  ? (c < 2565
                    ? (c >= 2561 && c <= 2563)
                    : c <= 2570)
                  : (c <= 2576 || (c < 2602
                    ? (c >= 2579 && c <= 2600)
                    : c <= 2608)))
                : (c <= 2611 || (c < 2620
                  ? (c < 2616
                    ? (c >= 2613 && c <= 2614)
                    : c <= 2617)
                  : (c <= 2620 || (c < 2631
                    ? (c >= 2622 && c <= 2626)
                    : c <= 2632)))))
              : (c <= 2637 || (c < 2693
                ? (c < 2654
                  ? (c < 2649
                    ? c == 2641
                    : c <= 2652)
                  : (c <= 2654 || (c < 2689
                    ? (c >= 2662 && c <= 2677)
                    : c <= 2691)))
                : (c <= 2701 || (c < 2730
                  ? (c < 2707
                    ? (c >= 2703 && c <= 2705)
                    : c <= 2728)
                  : (c <= 2736 || (c < 2741
                    ? (c >= 2738 && c <= 2739)
                    : c <= 2745)))))))))))
        : (c <= 2757 || (c < 3168
          ? (c < 2958
            ? (c < 2866
              ? (c < 2809
                ? (c < 2768
                  ? (c < 2763
                    ? (c >= 2759 && c <= 2761)
                    : c <= 2765)
                  : (c <= 2768 || (c < 2790
                    ? (c >= 2784 && c <= 2787)
                    : c <= 2799)))
                : (c <= 2815 || (c < 2831
                  ? (c < 2821
                    ? (c >= 2817 && c <= 2819)
                    : c <= 2828)
                  : (c <= 2832 || (c < 2858
                    ? (c >= 2835 && c <= 2856)
                    : c <= 2864)))))
              : (c <= 2867 || (c < 2908
                ? (c < 2887
                  ? (c < 2876
                    ? (c >= 2869 && c <= 2873)
                    : c <= 2884)
                  : (c <= 2888 || (c < 2901
                    ? (c >= 2891 && c <= 2893)
                    : c <= 2903)))
                : (c <= 2909 || (c < 2929
                  ? (c < 2918
                    ? (c >= 2911 && c <= 2915)
                    : c <= 2927)
                  : (c <= 2929 || (c < 2949
                    ? (c >= 2946 && c <= 2947)
                    : c <= 2954)))))))
            : (c <= 2960 || (c < 3031
              ? (c < 2984
                ? (c < 2972
                  ? (c < 2969
                    ? (c >= 2962 && c <= 2965)
                    : c <= 2970)
                  : (c <= 2972 || (c < 2979
                    ? (c >= 2974 && c <= 2975)
                    : c <= 2980)))
                : (c <= 2986 || (c < 3014
                  ? (c < 3006
                    ? (c >= 2990 && c <= 3001)
                    : c <= 3010)
                  : (c <= 3016 || (c < 3024
                    ? (c >= 3018 && c <= 3021)
                    : c <= 3024)))))
              : (c <= 3031 || (c < 3132
                ? (c < 3086
                  ? (c < 3072
                    ? (c >= 3046 && c <= 3055)
                    : c <= 3084)
                  : (c <= 3088 || (c < 3114
                    ? (c >= 3090 && c <= 3112)
                    : c <= 3129)))
                : (c <= 3140 || (c < 3157
                  ? (c < 3146
                    ? (c >= 3142 && c <= 3144)
                    : c <= 3149)
                  : (c <= 3158 || (c < 3165
                    ? (c >= 3160 && c <= 3162)
                    : c <= 3165)))))))))
          : (c <= 3171 || (c < 3450
            ? (c < 3293
              ? (c < 3242
                ? (c < 3205
                  ? (c < 3200
                    ? (c >= 3174 && c <= 3183)
                    : c <= 3203)
                  : (c <= 3212 || (c < 3218
                    ? (c >= 3214 && c <= 3216)
                    : c <= 3240)))
                : (c <= 3251 || (c < 3270
                  ? (c < 3260
                    ? (c >= 3253 && c <= 3257)
                    : c <= 3268)
                  : (c <= 3272 || (c < 3285
                    ? (c >= 3274 && c <= 3277)
                    : c <= 3286)))))
              : (c <= 3294 || (c < 3346
                ? (c < 3313
                  ? (c < 3302
                    ? (c >= 3296 && c <= 3299)
                    : c <= 3311)
                  : (c <= 3314 || (c < 3342
                    ? (c >= 3328 && c <= 3340)
                    : c <= 3344)))
                : (c <= 3396 || (c < 3412
                  ? (c < 3402
                    ? (c >= 3398 && c <= 3400)
                    : c <= 3406)
                  : (c <= 3415 || (c < 3430
                    ? (c >= 3423 && c <= 3427)
                    : c <= 3439)))))))
            : (c <= 3455 || (c < 3570
              ? (c < 3520
                ? (c < 3482
                  ? (c < 3461
                    ? (c >= 3457 && c <= 3459)
                    : c <= 3478)
                  : (c <= 3505 || (c < 3517
                    ? (c >= 3507 && c <= 3515)
                    : c <= 3517)))
                : (c <= 3526 || (c < 3542
                  ? (c < 3535
                    ? c == 3530
                    : c <= 3540)
                  : (c <= 3542 || (c < 3558
                    ? (c >= 3544 && c <= 3551)
                    : c <= 3567)))))
              : (c <= 3571 || (c < 3718
                ? (c < 3664
                  ? (c < 3648
                    ? (c >= 3585 && c <= 3642)
                    : c <= 3662)
                  : (c <= 3673 || (c < 3716
                    ? (c >= 3713 && c <= 3714)
                    : c <= 3716)))
                : (c <= 3722 || (c < 3751
                  ? (c < 3749
                    ? (c >= 3724 && c <= 3747)
                    : c <= 3749)
                  : (c <= 3773 || (c >= 3776 && c <= 3780)))))))))))))
      : (c <= 3782 || (c < 8025
        ? (c < 5888
          ? (c < 4688
            ? (c < 3953
              ? (c < 3872
                ? (c < 3804
                  ? (c < 3792
                    ? (c >= 3784 && c <= 3789)
                    : c <= 3801)
                  : (c <= 3807 || (c < 3864
                    ? c == 3840
                    : c <= 3865)))
                : (c <= 3881 || (c < 3897
                  ? (c < 3895
                    ? c == 3893
                    : c <= 3895)
                  : (c <= 3897 || (c < 3913
                    ? (c >= 3902 && c <= 3911)
                    : c <= 3948)))))
              : (c <= 3972 || (c < 4256
                ? (c < 4038
                  ? (c < 3993
                    ? (c >= 3974 && c <= 3991)
                    : c <= 4028)
                  : (c <= 4038 || (c < 4176
                    ? (c >= 4096 && c <= 4169)
                    : c <= 4253)))
                : (c <= 4293 || (c < 4304
                  ? (c < 4301
                    ? c == 4295
                    : c <= 4301)
                  : (c <= 4346 || (c < 4682
                    ? (c >= 4348 && c <= 4680)
                    : c <= 4685)))))))
            : (c <= 4694 || (c < 4882
              ? (c < 4786
                ? (c < 4704
                  ? (c < 4698
                    ? c == 4696
                    : c <= 4701)
                  : (c <= 4744 || (c < 4752
                    ? (c >= 4746 && c <= 4749)
                    : c <= 4784)))
                : (c <= 4789 || (c < 4802
                  ? (c < 4800
                    ? (c >= 4792 && c <= 4798)
                    : c <= 4800)
                  : (c <= 4805 || (c < 4824
                    ? (c >= 4808 && c <= 4822)
                    : c <= 4880)))))
              : (c <= 4885 || (c < 5112
                ? (c < 4969
                  ? (c < 4957
                    ? (c >= 4888 && c <= 4954)
                    : c <= 4959)
                  : (c <= 4977 || (c < 5024
                    ? (c >= 4992 && c <= 5007)
                    : c <= 5109)))
                : (c <= 5117 || (c < 5761
                  ? (c < 5743
                    ? (c >= 5121 && c <= 5740)
                    : c <= 5759)
                  : (c <= 5786 || (c < 5870
                    ? (c >= 5792 && c <= 5866)
                    : c <= 5880)))))))))
          : (c <= 5909 || (c < 6688
            ? (c < 6176
              ? (c < 6016
                ? (c < 5984
                  ? (c < 5952
                    ? (c >= 5919 && c <= 5940)
                    : c <= 5971)
                  : (c <= 5996 || (c < 6002
                    ? (c >= 5998 && c <= 6000)
                    : c <= 6003)))
                : (c <= 6099 || (c < 6112
                  ? (c < 6108
                    ? c == 6103
                    : c <= 6109)
                  : (c <= 6121 || (c < 6159
                    ? (c >= 6155 && c <= 6157)
                    : c <= 6169)))))
              : (c <= 6264 || (c < 6470
                ? (c < 6400
                  ? (c < 6320
                    ? (c >= 6272 && c <= 6314)
                    : c <= 6389)
                  : (c <= 6430 || (c < 6448
                    ? (c >= 6432 && c <= 6443)
                    : c <= 6459)))
                : (c <= 6509 || (c < 6576
                  ? (c < 6528
                    ? (c >= 6512 && c <= 6516)
                    : c <= 6571)
                  : (c <= 6601 || (c < 6656
                    ? (c >= 6608 && c <= 6618)
                    : c <= 6683)))))))
            : (c <= 6750 || (c < 7232
              ? (c < 6847
                ? (c < 6800
                  ? (c < 6783
                    ? (c >= 6752 && c <= 6780)
                    : c <= 6793)
                  : (c <= 6809 || (c < 6832
                    ? c == 6823
                    : c <= 6845)))
                : (c <= 6862 || (c < 7019
                  ? (c < 6992
                    ? (c >= 6912 && c <= 6988)
                    : c <= 7001)
                  : (c <= 7027 || (c < 7168
                    ? (c >= 7040 && c <= 7155)
                    : c <= 7223)))))
              : (c <= 7241 || (c < 7380
                ? (c < 7312
                  ? (c < 7296
                    ? (c >= 7245 && c <= 7293)
                    : c <= 7304)
                  : (c <= 7354 || (c < 7376
                    ? (c >= 7357 && c <= 7359)
                    : c <= 7378)))
                : (c <= 7418 || (c < 7968
                  ? (c < 7960
                    ? (c >= 7424 && c <= 7957)
                    : c <= 7965)
                  : (c <= 8005 || (c < 8016
                    ? (c >= 8008 && c <= 8013)
                    : c <= 8023)))))))))))
        : (c <= 8025 || (c < 11720
          ? (c < 8458
            ? (c < 8178
              ? (c < 8126
                ? (c < 8031
                  ? (c < 8029
                    ? c == 8027
                    : c <= 8029)
                  : (c <= 8061 || (c < 8118
                    ? (c >= 8064 && c <= 8116)
                    : c <= 8124)))
                : (c <= 8126 || (c < 8144
                  ? (c < 8134
                    ? (c >= 8130 && c <= 8132)
                    : c <= 8140)
                  : (c <= 8147 || (c < 8160
                    ? (c >= 8150 && c <= 8155)
                    : c <= 8172)))))
              : (c <= 8180 || (c < 8336
                ? (c < 8276
                  ? (c < 8255
                    ? (c >= 8182 && c <= 8188)
                    : c <= 8256)
                  : (c <= 8276 || (c < 8319
                    ? c == 8305
                    : c <= 8319)))
                : (c <= 8348 || (c < 8421
                  ? (c < 8417
                    ? (c >= 8400 && c <= 8412)
                    : c <= 8417)
                  : (c <= 8432 || (c < 8455
                    ? c == 8450
                    : c <= 8455)))))))
            : (c <= 8467 || (c < 11499
              ? (c < 8490
                ? (c < 8484
                  ? (c < 8472
                    ? c == 8469
                    : c <= 8477)
                  : (c <= 8484 || (c < 8488
                    ? c == 8486
                    : c <= 8488)))
                : (c <= 8505 || (c < 8526
                  ? (c < 8517
                    ? (c >= 8508 && c <= 8511)
                    : c <= 8521)
                  : (c <= 8526 || (c < 11264
                    ? (c >= 8544 && c <= 8584)
                    : c <= 11492)))))
              : (c <= 11507 || (c < 11647
                ? (c < 11565
                  ? (c < 11559
                    ? (c >= 11520 && c <= 11557)
                    : c <= 11559)
                  : (c <= 11565 || (c < 11631
                    ? (c >= 11568 && c <= 11623)
                    : c <= 11631)))
                : (c <= 11670 || (c < 11696
                  ? (c < 11688
                    ? (c >= 11680 && c <= 11686)
                    : c <= 11694)
                  : (c <= 11702 || (c < 11712
                    ? (c >= 11704 && c <= 11710)
                    : c <= 11718)))))))))
          : (c <= 11726 || (c < 42623
            ? (c < 12540
              ? (c < 12337
                ? (c < 11744
                  ? (c < 11736
                    ? (c >= 11728 && c <= 11734)
                    : c <= 11742)
                  : (c <= 11775 || (c < 12321
                    ? (c >= 12293 && c <= 12295)
                    : c <= 12335)))
                : (c <= 12341 || (c < 12441
                  ? (c < 12353
                    ? (c >= 12344 && c <= 12348)
                    : c <= 12438)
                  : (c <= 12442 || (c < 12449
                    ? (c >= 12445 && c <= 12447)
                    : c <= 12538)))))
              : (c <= 12543 || (c < 19968
                ? (c < 12704
                  ? (c < 12593
                    ? (c >= 12549 && c <= 12591)
                    : c <= 12686)
                  : (c <= 12735 || (c < 13312
                    ? (c >= 12784 && c <= 12799)
                    : c <= 19903)))
                : (c <= 42124 || (c < 42512
                  ? (c < 42240
                    ? (c >= 42192 && c <= 42237)
                    : c <= 42508)
                  : (c <= 42539 || (c < 42612
                    ? (c >= 42560 && c <= 42607)
                    : c <= 42621)))))))
            : (c <= 42737 || (c < 43232
              ? (c < 42965
                ? (c < 42891
                  ? (c < 42786
                    ? (c >= 42775 && c <= 42783)
                    : c <= 42888)
                  : (c <= 42954 || (c < 42963
                    ? (c >= 42960 && c <= 42961)
                    : c <= 42963)))
                : (c <= 42969 || (c < 43072
                  ? (c < 43052
                    ? (c >= 42994 && c <= 43047)
                    : c <= 43052)
                  : (c <= 43123 || (c < 43216
                    ? (c >= 43136 && c <= 43205)
                    : c <= 43225)))))
              : (c <= 43255 || (c < 43471
                ? (c < 43312
                  ? (c < 43261
                    ? c == 43259
                    : c <= 43309)
                  : (c <= 43347 || (c < 43392
                    ? (c >= 43360 && c <= 43388)
                    : c <= 43456)))
                : (c <= 43481 || (c < 43584
                  ? (c < 43520
                    ? (c >= 43488 && c <= 43518)
                    : c <= 43574)
                  : (c <= 43597 || (c >= 43600 && c <= 43609)))))))))))))))
    : (c <= 43638 || (c < 71453
      ? (c < 67639
        ? (c < 65345
          ? (c < 64312
            ? (c < 43888
              ? (c < 43785
                ? (c < 43744
                  ? (c < 43739
                    ? (c >= 43642 && c <= 43714)
                    : c <= 43741)
                  : (c <= 43759 || (c < 43777
                    ? (c >= 43762 && c <= 43766)
                    : c <= 43782)))
                : (c <= 43790 || (c < 43816
                  ? (c < 43808
                    ? (c >= 43793 && c <= 43798)
                    : c <= 43814)
                  : (c <= 43822 || (c < 43868
                    ? (c >= 43824 && c <= 43866)
                    : c <= 43881)))))
              : (c <= 44010 || (c < 63744
                ? (c < 44032
                  ? (c < 44016
                    ? (c >= 44012 && c <= 44013)
                    : c <= 44025)
                  : (c <= 55203 || (c < 55243
                    ? (c >= 55216 && c <= 55238)
                    : c <= 55291)))
                : (c <= 64109 || (c < 64275
                  ? (c < 64256
                    ? (c >= 64112 && c <= 64217)
                    : c <= 64262)
                  : (c <= 64279 || (c < 64298
                    ? (c >= 64285 && c <= 64296)
                    : c <= 64310)))))))
            : (c <= 64316 || (c < 65075
              ? (c < 64612
                ? (c < 64323
                  ? (c < 64320
                    ? c == 64318
                    : c <= 64321)
                  : (c <= 64324 || (c < 64467
                    ? (c >= 64326 && c <= 64433)
                    : c <= 64605)))
                : (c <= 64829 || (c < 65008
                  ? (c < 64914
                    ? (c >= 64848 && c <= 64911)
                    : c <= 64967)
                  : (c <= 65017 || (c < 65056
                    ? (c >= 65024 && c <= 65039)
                    : c <= 65071)))))
              : (c <= 65076 || (c < 65147
                ? (c < 65139
                  ? (c < 65137
                    ? (c >= 65101 && c <= 65103)
                    : c <= 65137)
                  : (c <= 65139 || (c < 65145
                    ? c == 65143
                    : c <= 65145)))
                : (c <= 65147 || (c < 65296
                  ? (c < 65151
                    ? c == 65149
                    : c <= 65276)
                  : (c <= 65305 || (c < 65343
                    ? (c >= 65313 && c <= 65338)
                    : c <= 65343)))))))))
          : (c <= 65370 || (c < 66513
            ? (c < 65664
              ? (c < 65536
                ? (c < 65482
                  ? (c < 65474
                    ? (c >= 65382 && c <= 65470)
                    : c <= 65479)
                  : (c <= 65487 || (c < 65498
                    ? (c >= 65490 && c <= 65495)
                    : c <= 65500)))
                : (c <= 65547 || (c < 65596
                  ? (c < 65576
                    ? (c >= 65549 && c <= 65574)
                    : c <= 65594)
                  : (c <= 65597 || (c < 65616
                    ? (c >= 65599 && c <= 65613)
                    : c <= 65629)))))
              : (c <= 65786 || (c < 66304
                ? (c < 66176
                  ? (c < 66045
                    ? (c >= 65856 && c <= 65908)
                    : c <= 66045)
                  : (c <= 66204 || (c < 66272
                    ? (c >= 66208 && c <= 66256)
                    : c <= 66272)))
                : (c <= 66335 || (c < 66432
                  ? (c < 66384
                    ? (c >= 66349 && c <= 66378)
                    : c <= 66426)
                  : (c <= 66461 || (c < 66504
                    ? (c >= 66464 && c <= 66499)
                    : c <= 66511)))))))
            : (c <= 66517 || (c < 66979
              ? (c < 66864
                ? (c < 66736
                  ? (c < 66720
                    ? (c >= 66560 && c <= 66717)
                    : c <= 66729)
                  : (c <= 66771 || (c < 66816
                    ? (c >= 66776 && c <= 66811)
                    : c <= 66855)))
                : (c <= 66915 || (c < 66956
                  ? (c < 66940
                    ? (c >= 66928 && c <= 66938)
                    : c <= 66954)
                  : (c <= 66962 || (c < 66967
                    ? (c >= 66964 && c <= 66965)
                    : c <= 66977)))))
              : (c <= 66993 || (c < 67456
                ? (c < 67072
                  ? (c < 67003
                    ? (c >= 66995 && c <= 67001)
                    : c <= 67004)
                  : (c <= 67382 || (c < 67424
                    ? (c >= 67392 && c <= 67413)
                    : c <= 67431)))
                : (c <= 67461 || (c < 67584
                  ? (c < 67506
                    ? (c >= 67463 && c <= 67504)
                    : c <= 67514)
                  : (c <= 67589 || (c < 67594
                    ? c == 67592
                    : c <= 67637)))))))))))
        : (c <= 67640 || (c < 69956
          ? (c < 68448
            ? (c < 68101
              ? (c < 67828
                ? (c < 67680
                  ? (c < 67647
                    ? c == 67644
                    : c <= 67669)
                  : (c <= 67702 || (c < 67808
                    ? (c >= 67712 && c <= 67742)
                    : c <= 67826)))
                : (c <= 67829 || (c < 67968
                  ? (c < 67872
                    ? (c >= 67840 && c <= 67861)
                    : c <= 67897)
                  : (c <= 68023 || (c < 68096
                    ? (c >= 68030 && c <= 68031)
                    : c <= 68099)))))
              : (c <= 68102 || (c < 68192
                ? (c < 68121
                  ? (c < 68117
                    ? (c >= 68108 && c <= 68115)
                    : c <= 68119)
                  : (c <= 68149 || (c < 68159
                    ? (c >= 68152 && c <= 68154)
                    : c <= 68159)))
                : (c <= 68220 || (c < 68297
                  ? (c < 68288
                    ? (c >= 68224 && c <= 68252)
                    : c <= 68295)
                  : (c <= 68326 || (c < 68416
                    ? (c >= 68352 && c <= 68405)
                    : c <= 68437)))))))
            : (c <= 68466 || (c < 69424
              ? (c < 68912
                ? (c < 68736
                  ? (c < 68608
                    ? (c >= 68480 && c <= 68497)
                    : c <= 68680)
                  : (c <= 68786 || (c < 68864
                    ? (c >= 68800 && c <= 68850)
                    : c <= 68903)))
                : (c <= 68921 || (c < 69296
                  ? (c < 69291
                    ? (c >= 69248 && c <= 69289)
                    : c <= 69292)
                  : (c <= 69297 || (c < 69415
                    ? (c >= 69376 && c <= 69404)
                    : c <= 69415)))))
              : (c <= 69456 || (c < 69759
                ? (c < 69600
                  ? (c < 69552
                    ? (c >= 69488 && c <= 69509)
                    : c <= 69572)
                  : (c <= 69622 || (c < 69734
                    ? (c >= 69632 && c <= 69702)
                    : c <= 69749)))
                : (c <= 69818 || (c < 69872
                  ? (c < 69840
                    ? c == 69826
                    : c <= 69864)
                  : (c <= 69881 || (c < 69942
                    ? (c >= 69888 && c <= 69940)
                    : c <= 69951)))))))))
          : (c <= 69959 || (c < 70459
            ? (c < 70282
              ? (c < 70108
                ? (c < 70016
                  ? (c < 70006
                    ? (c >= 69968 && c <= 70003)
                    : c <= 70006)
                  : (c <= 70084 || (c < 70094
                    ? (c >= 70089 && c <= 70092)
                    : c <= 70106)))
                : (c <= 70108 || (c < 70206
                  ? (c < 70163
                    ? (c >= 70144 && c <= 70161)
                    : c <= 70199)
                  : (c <= 70206 || (c < 70280
                    ? (c >= 70272 && c <= 70278)
                    : c <= 70280)))))
              : (c <= 70285 || (c < 70405
                ? (c < 70320
                  ? (c < 70303
                    ? (c >= 70287 && c <= 70301)
                    : c <= 70312)
                  : (c <= 70378 || (c < 70400
                    ? (c >= 70384 && c <= 70393)
                    : c <= 70403)))
                : (c <= 70412 || (c < 70442
                  ? (c < 70419
                    ? (c >= 70415 && c <= 70416)
                    : c <= 70440)
                  : (c <= 70448 || (c < 70453
                    ? (c >= 70450 && c <= 70451)
                    : c <= 70457)))))))
            : (c <= 70468 || (c < 70855
              ? (c < 70502
                ? (c < 70480
                  ? (c < 70475
                    ? (c >= 70471 && c <= 70472)
                    : c <= 70477)
                  : (c <= 70480 || (c < 70493
                    ? c == 70487
                    : c <= 70499)))
                : (c <= 70508 || (c < 70736
                  ? (c < 70656
                    ? (c >= 70512 && c <= 70516)
                    : c <= 70730)
                  : (c <= 70745 || (c < 70784
                    ? (c >= 70750 && c <= 70753)
                    : c <= 70853)))))
              : (c <= 70855 || (c < 71236
                ? (c < 71096
                  ? (c < 71040
                    ? (c >= 70864 && c <= 70873)
                    : c <= 71093)
                  : (c <= 71104 || (c < 71168
                    ? (c >= 71128 && c <= 71133)
                    : c <= 71232)))
                : (c <= 71236 || (c < 71360
                  ? (c < 71296
                    ? (c >= 71248 && c <= 71257)
                    : c <= 71352)
                  : (c <= 71369 || (c >= 71424 && c <= 71450)))))))))))))
      : (c <= 71467 || (c < 119973
        ? (c < 77824
          ? (c < 72760
            ? (c < 72016
              ? (c < 71945
                ? (c < 71680
                  ? (c < 71488
                    ? (c >= 71472 && c <= 71481)
                    : c <= 71494)
                  : (c <= 71738 || (c < 71935
                    ? (c >= 71840 && c <= 71913)
                    : c <= 71942)))
                : (c <= 71945 || (c < 71960
                  ? (c < 71957
                    ? (c >= 71948 && c <= 71955)
                    : c <= 71958)
                  : (c <= 71989 || (c < 71995
                    ? (c >= 71991 && c <= 71992)
                    : c <= 72003)))))
              : (c <= 72025 || (c < 72263
                ? (c < 72154
                  ? (c < 72106
                    ? (c >= 72096 && c <= 72103)
                    : c <= 72151)
                  : (c <= 72161 || (c < 72192
                    ? (c >= 72163 && c <= 72164)
                    : c <= 72254)))
                : (c <= 72263 || (c < 72368
                  ? (c < 72349
                    ? (c >= 72272 && c <= 72345)
                    : c <= 72349)
                  : (c <= 72440 || (c < 72714
                    ? (c >= 72704 && c <= 72712)
                    : c <= 72758)))))))
            : (c <= 72768 || (c < 73056
              ? (c < 72968
                ? (c < 72850
                  ? (c < 72818
                    ? (c >= 72784 && c <= 72793)
                    : c <= 72847)
                  : (c <= 72871 || (c < 72960
                    ? (c >= 72873 && c <= 72886)
                    : c <= 72966)))
                : (c <= 72969 || (c < 73020
                  ? (c < 73018
                    ? (c >= 72971 && c <= 73014)
                    : c <= 73018)
                  : (c <= 73021 || (c < 73040
                    ? (c >= 73023 && c <= 73031)
                    : c <= 73049)))))
              : (c <= 73061 || (c < 73440
                ? (c < 73104
                  ? (c < 73066
                    ? (c >= 73063 && c <= 73064)
                    : c <= 73102)
                  : (c <= 73105 || (c < 73120
                    ? (c >= 73107 && c <= 73112)
                    : c <= 73129)))
                : (c <= 73462 || (c < 74752
                  ? (c < 73728
                    ? c == 73648
                    : c <= 74649)
                  : (c <= 74862 || (c < 77712
                    ? (c >= 74880 && c <= 75075)
                    : c <= 77808)))))))))
          : (c <= 78894 || (c < 110576
            ? (c < 93027
              ? (c < 92864
                ? (c < 92736
                  ? (c < 92160
                    ? (c >= 82944 && c <= 83526)
                    : c <= 92728)
                  : (c <= 92766 || (c < 92784
                    ? (c >= 92768 && c <= 92777)
                    : c <= 92862)))
                : (c <= 92873 || (c < 92928
                  ? (c < 92912
                    ? (c >= 92880 && c <= 92909)
                    : c <= 92916)
                  : (c <= 92982 || (c < 93008
                    ? (c >= 92992 && c <= 92995)
                    : c <= 93017)))))
              : (c <= 93047 || (c < 94176
                ? (c < 93952
                  ? (c < 93760
                    ? (c >= 93053 && c <= 93071)
                    : c <= 93823)
                  : (c <= 94026 || (c < 94095
                    ? (c >= 94031 && c <= 94087)
                    : c <= 94111)))
                : (c <= 94177 || (c < 94208
                  ? (c < 94192
                    ? (c >= 94179 && c <= 94180)
                    : c <= 94193)
                  : (c <= 100343 || (c < 101632
                    ? (c >= 100352 && c <= 101589)
                    : c <= 101640)))))))
            : (c <= 110579 || (c < 118528
              ? (c < 110960
                ? (c < 110592
                  ? (c < 110589
                    ? (c >= 110581 && c <= 110587)
                    : c <= 110590)
                  : (c <= 110882 || (c < 110948
                    ? (c >= 110928 && c <= 110930)
                    : c <= 110951)))
                : (c <= 111355 || (c < 113792
                  ? (c < 113776
                    ? (c >= 113664 && c <= 113770)
                    : c <= 113788)
                  : (c <= 113800 || (c < 113821
                    ? (c >= 113808 && c <= 113817)
                    : c <= 113822)))))
              : (c <= 118573 || (c < 119210
                ? (c < 119149
                  ? (c < 119141
                    ? (c >= 118576 && c <= 118598)
                    : c <= 119145)
                  : (c <= 119154 || (c < 119173
                    ? (c >= 119163 && c <= 119170)
                    : c <= 119179)))
                : (c <= 119213 || (c < 119894
                  ? (c < 119808
                    ? (c >= 119362 && c <= 119364)
                    : c <= 119892)
                  : (c <= 119964 || (c < 119970
                    ? (c >= 119966 && c <= 119967)
                    : c <= 119970)))))))))))
        : (c <= 119974 || (c < 124912
          ? (c < 120746
            ? (c < 120134
              ? (c < 120071
                ? (c < 119995
                  ? (c < 119982
                    ? (c >= 119977 && c <= 119980)
                    : c <= 119993)
                  : (c <= 119995 || (c < 120005
                    ? (c >= 119997 && c <= 120003)
                    : c <= 120069)))
                : (c <= 120074 || (c < 120094
                  ? (c < 120086
                    ? (c >= 120077 && c <= 120084)
                    : c <= 120092)
                  : (c <= 120121 || (c < 120128
                    ? (c >= 120123 && c <= 120126)
                    : c <= 120132)))))
              : (c <= 120134 || (c < 120572
                ? (c < 120488
                  ? (c < 120146
                    ? (c >= 120138 && c <= 120144)
                    : c <= 120485)
                  : (c <= 120512 || (c < 120540
                    ? (c >= 120514 && c <= 120538)
                    : c <= 120570)))
                : (c <= 120596 || (c < 120656
                  ? (c < 120630
                    ? (c >= 120598 && c <= 120628)
                    : c <= 120654)
                  : (c <= 120686 || (c < 120714
                    ? (c >= 120688 && c <= 120712)
                    : c <= 120744)))))))
            : (c <= 120770 || (c < 122907
              ? (c < 121476
                ? (c < 121344
                  ? (c < 120782
                    ? (c >= 120772 && c <= 120779)
                    : c <= 120831)
                  : (c <= 121398 || (c < 121461
                    ? (c >= 121403 && c <= 121452)
                    : c <= 121461)))
                : (c <= 121476 || (c < 122624
                  ? (c < 121505
                    ? (c >= 121499 && c <= 121503)
                    : c <= 121519)
                  : (c <= 122654 || (c < 122888
                    ? (c >= 122880 && c <= 122886)
                    : c <= 122904)))))
              : (c <= 122913 || (c < 123214
                ? (c < 123136
                  ? (c < 122918
                    ? (c >= 122915 && c <= 122916)
                    : c <= 122922)
                  : (c <= 123180 || (c < 123200
                    ? (c >= 123184 && c <= 123197)
                    : c <= 123209)))
                : (c <= 123214 || (c < 124896
                  ? (c < 123584
                    ? (c >= 123536 && c <= 123566)
                    : c <= 123641)
                  : (c <= 124902 || (c < 124909
                    ? (c >= 124904 && c <= 124907)
                    : c <= 124910)))))))))
          : (c <= 124926 || (c < 126557
            ? (c < 126521
              ? (c < 126469
                ? (c < 125184
                  ? (c < 125136
                    ? (c >= 124928 && c <= 125124)
                    : c <= 125142)
                  : (c <= 125259 || (c < 126464
                    ? (c >= 125264 && c <= 125273)
                    : c <= 126467)))
                : (c <= 126495 || (c < 126503
                  ? (c < 126500
                    ? (c >= 126497 && c <= 126498)
                    : c <= 126500)
                  : (c <= 126503 || (c < 126516
                    ? (c >= 126505 && c <= 126514)
                    : c <= 126519)))))
              : (c <= 126521 || (c < 126541
                ? (c < 126535
                  ? (c < 126530
                    ? c == 126523
                    : c <= 126530)
                  : (c <= 126535 || (c < 126539
                    ? c == 126537
                    : c <= 126539)))
                : (c <= 126543 || (c < 126551
                  ? (c < 126548
                    ? (c >= 126545 && c <= 126546)
                    : c <= 126548)
                  : (c <= 126551 || (c < 126555
                    ? c == 126553
                    : c <= 126555)))))))
            : (c <= 126557 || (c < 126629
              ? (c < 126580
                ? (c < 126564
                  ? (c < 126561
                    ? c == 126559
                    : c <= 126562)
                  : (c <= 126564 || (c < 126572
                    ? (c >= 126567 && c <= 126570)
                    : c <= 126578)))
                : (c <= 126583 || (c < 126592
                  ? (c < 126590
                    ? (c >= 126585 && c <= 126588)
                    : c <= 126590)
                  : (c <= 126601 || (c < 126625
                    ? (c >= 126603 && c <= 126619)
                    : c <= 126627)))))
              : (c <= 126633 || (c < 178208
                ? (c < 131072
                  ? (c < 130032
                    ? (c >= 126635 && c <= 126651)
                    : c <= 130041)
                  : (c <= 173791 || (c < 177984
                    ? (c >= 173824 && c <= 177976)
                    : c <= 178205)))
                : (c <= 183969 || (c < 196608
                  ? (c < 194560
                    ? (c >= 183984 && c <= 191456)
                    : c <= 195101)
                  : (c <= 201546 || (c >= 917760 && c <= 917999)))))))))))))))));
}

static inline bool sym_name_character_set_6(int32_t c) {
  return (c < 43616
    ? (c < 3782
      ? (c < 2748
        ? (c < 2045
          ? (c < 1015
            ? (c < 710
              ? (c < 181
                ? (c < '_'
                  ? (c < 'A'
                    ? (c >= '0' && c <= '9')
                    : c <= 'Z')
                  : (c <= '_' || (c < 170
                    ? (c >= 'b' && c <= 'z')
                    : c <= 170)))
                : (c <= 181 || (c < 192
                  ? (c < 186
                    ? c == 183
                    : c <= 186)
                  : (c <= 214 || (c < 248
                    ? (c >= 216 && c <= 246)
                    : c <= 705)))))
              : (c <= 721 || (c < 891
                ? (c < 750
                  ? (c < 748
                    ? (c >= 736 && c <= 740)
                    : c <= 748)
                  : (c <= 750 || (c < 886
                    ? (c >= 768 && c <= 884)
                    : c <= 887)))
                : (c <= 893 || (c < 908
                  ? (c < 902
                    ? c == 895
                    : c <= 906)
                  : (c <= 908 || (c < 931
                    ? (c >= 910 && c <= 929)
                    : c <= 1013)))))))
            : (c <= 1153 || (c < 1519
              ? (c < 1425
                ? (c < 1329
                  ? (c < 1162
                    ? (c >= 1155 && c <= 1159)
                    : c <= 1327)
                  : (c <= 1366 || (c < 1376
                    ? c == 1369
                    : c <= 1416)))
                : (c <= 1469 || (c < 1476
                  ? (c < 1473
                    ? c == 1471
                    : c <= 1474)
                  : (c <= 1477 || (c < 1488
                    ? c == 1479
                    : c <= 1514)))))
              : (c <= 1522 || (c < 1770
                ? (c < 1646
                  ? (c < 1568
                    ? (c >= 1552 && c <= 1562)
                    : c <= 1641)
                  : (c <= 1747 || (c < 1759
                    ? (c >= 1749 && c <= 1756)
                    : c <= 1768)))
                : (c <= 1788 || (c < 1869
                  ? (c < 1808
                    ? c == 1791
                    : c <= 1866)
                  : (c <= 1969 || (c < 2042
                    ? (c >= 1984 && c <= 2037)
                    : c <= 2042)))))))))
          : (c <= 2045 || (c < 2558
            ? (c < 2451
              ? (c < 2200
                ? (c < 2144
                  ? (c < 2112
                    ? (c >= 2048 && c <= 2093)
                    : c <= 2139)
                  : (c <= 2154 || (c < 2185
                    ? (c >= 2160 && c <= 2183)
                    : c <= 2190)))
                : (c <= 2273 || (c < 2417
                  ? (c < 2406
                    ? (c >= 2275 && c <= 2403)
                    : c <= 2415)
                  : (c <= 2435 || (c < 2447
                    ? (c >= 2437 && c <= 2444)
                    : c <= 2448)))))
              : (c <= 2472 || (c < 2507
                ? (c < 2486
                  ? (c < 2482
                    ? (c >= 2474 && c <= 2480)
                    : c <= 2482)
                  : (c <= 2489 || (c < 2503
                    ? (c >= 2492 && c <= 2500)
                    : c <= 2504)))
                : (c <= 2510 || (c < 2527
                  ? (c < 2524
                    ? c == 2519
                    : c <= 2525)
                  : (c <= 2531 || (c < 2556
                    ? (c >= 2534 && c <= 2545)
                    : c <= 2556)))))))
            : (c <= 2558 || (c < 2635
              ? (c < 2610
                ? (c < 2575
                  ? (c < 2565
                    ? (c >= 2561 && c <= 2563)
                    : c <= 2570)
                  : (c <= 2576 || (c < 2602
                    ? (c >= 2579 && c <= 2600)
                    : c <= 2608)))
                : (c <= 2611 || (c < 2620
                  ? (c < 2616
                    ? (c >= 2613 && c <= 2614)
                    : c <= 2617)
                  : (c <= 2620 || (c < 2631
                    ? (c >= 2622 && c <= 2626)
                    : c <= 2632)))))
              : (c <= 2637 || (c < 2693
                ? (c < 2654
                  ? (c < 2649
                    ? c == 2641
                    : c <= 2652)
                  : (c <= 2654 || (c < 2689
                    ? (c >= 2662 && c <= 2677)
                    : c <= 2691)))
                : (c <= 2701 || (c < 2730
                  ? (c < 2707
                    ? (c >= 2703 && c <= 2705)
                    : c <= 2728)
                  : (c <= 2736 || (c < 2741
                    ? (c >= 2738 && c <= 2739)
                    : c <= 2745)))))))))))
        : (c <= 2757 || (c < 3168
          ? (c < 2958
            ? (c < 2866
              ? (c < 2809
                ? (c < 2768
                  ? (c < 2763
                    ? (c >= 2759 && c <= 2761)
                    : c <= 2765)
                  : (c <= 2768 || (c < 2790
                    ? (c >= 2784 && c <= 2787)
                    : c <= 2799)))
                : (c <= 2815 || (c < 2831
                  ? (c < 2821
                    ? (c >= 2817 && c <= 2819)
                    : c <= 2828)
                  : (c <= 2832 || (c < 2858
                    ? (c >= 2835 && c <= 2856)
                    : c <= 2864)))))
              : (c <= 2867 || (c < 2908
                ? (c < 2887
                  ? (c < 2876
                    ? (c >= 2869 && c <= 2873)
                    : c <= 2884)
                  : (c <= 2888 || (c < 2901
                    ? (c >= 2891 && c <= 2893)
                    : c <= 2903)))
                : (c <= 2909 || (c < 2929
                  ? (c < 2918
                    ? (c >= 2911 && c <= 2915)
                    : c <= 2927)
                  : (c <= 2929 || (c < 2949
                    ? (c >= 2946 && c <= 2947)
                    : c <= 2954)))))))
            : (c <= 2960 || (c < 3031
              ? (c < 2984
                ? (c < 2972
                  ? (c < 2969
                    ? (c >= 2962 && c <= 2965)
                    : c <= 2970)
                  : (c <= 2972 || (c < 2979
                    ? (c >= 2974 && c <= 2975)
                    : c <= 2980)))
                : (c <= 2986 || (c < 3014
                  ? (c < 3006
                    ? (c >= 2990 && c <= 3001)
                    : c <= 3010)
                  : (c <= 3016 || (c < 3024
                    ? (c >= 3018 && c <= 3021)
                    : c <= 3024)))))
              : (c <= 3031 || (c < 3132
                ? (c < 3086
                  ? (c < 3072
                    ? (c >= 3046 && c <= 3055)
                    : c <= 3084)
                  : (c <= 3088 || (c < 3114
                    ? (c >= 3090 && c <= 3112)
                    : c <= 3129)))
                : (c <= 3140 || (c < 3157
                  ? (c < 3146
                    ? (c >= 3142 && c <= 3144)
                    : c <= 3149)
                  : (c <= 3158 || (c < 3165
                    ? (c >= 3160 && c <= 3162)
                    : c <= 3165)))))))))
          : (c <= 3171 || (c < 3450
            ? (c < 3293
              ? (c < 3242
                ? (c < 3205
                  ? (c < 3200
                    ? (c >= 3174 && c <= 3183)
                    : c <= 3203)
                  : (c <= 3212 || (c < 3218
                    ? (c >= 3214 && c <= 3216)
                    : c <= 3240)))
                : (c <= 3251 || (c < 3270
                  ? (c < 3260
                    ? (c >= 3253 && c <= 3257)
                    : c <= 3268)
                  : (c <= 3272 || (c < 3285
                    ? (c >= 3274 && c <= 3277)
                    : c <= 3286)))))
              : (c <= 3294 || (c < 3346
                ? (c < 3313
                  ? (c < 3302
                    ? (c >= 3296 && c <= 3299)
                    : c <= 3311)
                  : (c <= 3314 || (c < 3342
                    ? (c >= 3328 && c <= 3340)
                    : c <= 3344)))
                : (c <= 3396 || (c < 3412
                  ? (c < 3402
                    ? (c >= 3398 && c <= 3400)
                    : c <= 3406)
                  : (c <= 3415 || (c < 3430
                    ? (c >= 3423 && c <= 3427)
                    : c <= 3439)))))))
            : (c <= 3455 || (c < 3570
              ? (c < 3520
                ? (c < 3482
                  ? (c < 3461
                    ? (c >= 3457 && c <= 3459)
                    : c <= 3478)
                  : (c <= 3505 || (c < 3517
                    ? (c >= 3507 && c <= 3515)
                    : c <= 3517)))
                : (c <= 3526 || (c < 3542
                  ? (c < 3535
                    ? c == 3530
                    : c <= 3540)
                  : (c <= 3542 || (c < 3558
                    ? (c >= 3544 && c <= 3551)
                    : c <= 3567)))))
              : (c <= 3571 || (c < 3718
                ? (c < 3664
                  ? (c < 3648
                    ? (c >= 3585 && c <= 3642)
                    : c <= 3662)
                  : (c <= 3673 || (c < 3716
                    ? (c >= 3713 && c <= 3714)
                    : c <= 3716)))
                : (c <= 3722 || (c < 3751
                  ? (c < 3749
                    ? (c >= 3724 && c <= 3747)
                    : c <= 3749)
                  : (c <= 3773 || (c >= 3776 && c <= 3780)))))))))))))
      : (c <= 3782 || (c < 8025
        ? (c < 5888
          ? (c < 4688
            ? (c < 3953
              ? (c < 3872
                ? (c < 3804
                  ? (c < 3792
                    ? (c >= 3784 && c <= 3789)
                    : c <= 3801)
                  : (c <= 3807 || (c < 3864
                    ? c == 3840
                    : c <= 3865)))
                : (c <= 3881 || (c < 3897
                  ? (c < 3895
                    ? c == 3893
                    : c <= 3895)
                  : (c <= 3897 || (c < 3913
                    ? (c >= 3902 && c <= 3911)
                    : c <= 3948)))))
              : (c <= 3972 || (c < 4256
                ? (c < 4038
                  ? (c < 3993
                    ? (c >= 3974 && c <= 3991)
                    : c <= 4028)
                  : (c <= 4038 || (c < 4176
                    ? (c >= 4096 && c <= 4169)
                    : c <= 4253)))
                : (c <= 4293 || (c < 4304
                  ? (c < 4301
                    ? c == 4295
                    : c <= 4301)
                  : (c <= 4346 || (c < 4682
                    ? (c >= 4348 && c <= 4680)
                    : c <= 4685)))))))
            : (c <= 4694 || (c < 4882
              ? (c < 4786
                ? (c < 4704
                  ? (c < 4698
                    ? c == 4696
                    : c <= 4701)
                  : (c <= 4744 || (c < 4752
                    ? (c >= 4746 && c <= 4749)
                    : c <= 4784)))
                : (c <= 4789 || (c < 4802
                  ? (c < 4800
                    ? (c >= 4792 && c <= 4798)
                    : c <= 4800)
                  : (c <= 4805 || (c < 4824
                    ? (c >= 4808 && c <= 4822)
                    : c <= 4880)))))
              : (c <= 4885 || (c < 5112
                ? (c < 4969
                  ? (c < 4957
                    ? (c >= 4888 && c <= 4954)
                    : c <= 4959)
                  : (c <= 4977 || (c < 5024
                    ? (c >= 4992 && c <= 5007)
                    : c <= 5109)))
                : (c <= 5117 || (c < 5761
                  ? (c < 5743
                    ? (c >= 5121 && c <= 5740)
                    : c <= 5759)
                  : (c <= 5786 || (c < 5870
                    ? (c >= 5792 && c <= 5866)
                    : c <= 5880)))))))))
          : (c <= 5909 || (c < 6688
            ? (c < 6176
              ? (c < 6016
                ? (c < 5984
                  ? (c < 5952
                    ? (c >= 5919 && c <= 5940)
                    : c <= 5971)
                  : (c <= 5996 || (c < 6002
                    ? (c >= 5998 && c <= 6000)
                    : c <= 6003)))
                : (c <= 6099 || (c < 6112
                  ? (c < 6108
                    ? c == 6103
                    : c <= 6109)
                  : (c <= 6121 || (c < 6159
                    ? (c >= 6155 && c <= 6157)
                    : c <= 6169)))))
              : (c <= 6264 || (c < 6470
                ? (c < 6400
                  ? (c < 6320
                    ? (c >= 6272 && c <= 6314)
                    : c <= 6389)
                  : (c <= 6430 || (c < 6448
                    ? (c >= 6432 && c <= 6443)
                    : c <= 6459)))
                : (c <= 6509 || (c < 6576
                  ? (c < 6528
                    ? (c >= 6512 && c <= 6516)
                    : c <= 6571)
                  : (c <= 6601 || (c < 6656
                    ? (c >= 6608 && c <= 6618)
                    : c <= 6683)))))))
            : (c <= 6750 || (c < 7232
              ? (c < 6847
                ? (c < 6800
                  ? (c < 6783
                    ? (c >= 6752 && c <= 6780)
                    : c <= 6793)
                  : (c <= 6809 || (c < 6832
                    ? c == 6823
                    : c <= 6845)))
                : (c <= 6862 || (c < 7019
                  ? (c < 6992
                    ? (c >= 6912 && c <= 6988)
                    : c <= 7001)
                  : (c <= 7027 || (c < 7168
                    ? (c >= 7040 && c <= 7155)
                    : c <= 7223)))))
              : (c <= 7241 || (c < 7380
                ? (c < 7312
                  ? (c < 7296
                    ? (c >= 7245 && c <= 7293)
                    : c <= 7304)
                  : (c <= 7354 || (c < 7376
                    ? (c >= 7357 && c <= 7359)
                    : c <= 7378)))
                : (c <= 7418 || (c < 7968
                  ? (c < 7960
                    ? (c >= 7424 && c <= 7957)
                    : c <= 7965)
                  : (c <= 8005 || (c < 8016
                    ? (c >= 8008 && c <= 8013)
                    : c <= 8023)))))))))))
        : (c <= 8025 || (c < 11720
          ? (c < 8458
            ? (c < 8178
              ? (c < 8126
                ? (c < 8031
                  ? (c < 8029
                    ? c == 8027
                    : c <= 8029)
                  : (c <= 8061 || (c < 8118
                    ? (c >= 8064 && c <= 8116)
                    : c <= 8124)))
                : (c <= 8126 || (c < 8144
                  ? (c < 8134
                    ? (c >= 8130 && c <= 8132)
                    : c <= 8140)
                  : (c <= 8147 || (c < 8160
                    ? (c >= 8150 && c <= 8155)
                    : c <= 8172)))))
              : (c <= 8180 || (c < 8336
                ? (c < 8276
                  ? (c < 8255
                    ? (c >= 8182 && c <= 8188)
                    : c <= 8256)
                  : (c <= 8276 || (c < 8319
                    ? c == 8305
                    : c <= 8319)))
                : (c <= 8348 || (c < 8421
                  ? (c < 8417
                    ? (c >= 8400 && c <= 8412)
                    : c <= 8417)
                  : (c <= 8432 || (c < 8455
                    ? c == 8450
                    : c <= 8455)))))))
            : (c <= 8467 || (c < 11499
              ? (c < 8490
                ? (c < 8484
                  ? (c < 8472
                    ? c == 8469
                    : c <= 8477)
                  : (c <= 8484 || (c < 8488
                    ? c == 8486
                    : c <= 8488)))
                : (c <= 8505 || (c < 8526
                  ? (c < 8517
                    ? (c >= 8508 && c <= 8511)
                    : c <= 8521)
                  : (c <= 8526 || (c < 11264
                    ? (c >= 8544 && c <= 8584)
                    : c <= 11492)))))
              : (c <= 11507 || (c < 11647
                ? (c < 11565
                  ? (c < 11559
                    ? (c >= 11520 && c <= 11557)
                    : c <= 11559)
                  : (c <= 11565 || (c < 11631
                    ? (c >= 11568 && c <= 11623)
                    : c <= 11631)))
                : (c <= 11670 || (c < 11696
                  ? (c < 11688
                    ? (c >= 11680 && c <= 11686)
                    : c <= 11694)
                  : (c <= 11702 || (c < 11712
                    ? (c >= 11704 && c <= 11710)
                    : c <= 11718)))))))))
          : (c <= 11726 || (c < 42623
            ? (c < 12540
              ? (c < 12337
                ? (c < 11744
                  ? (c < 11736
                    ? (c >= 11728 && c <= 11734)
                    : c <= 11742)
                  : (c <= 11775 || (c < 12321
                    ? (c >= 12293 && c <= 12295)
                    : c <= 12335)))
                : (c <= 12341 || (c < 12441
                  ? (c < 12353
                    ? (c >= 12344 && c <= 12348)
                    : c <= 12438)
                  : (c <= 12442 || (c < 12449
                    ? (c >= 12445 && c <= 12447)
                    : c <= 12538)))))
              : (c <= 12543 || (c < 19968
                ? (c < 12704
                  ? (c < 12593
                    ? (c >= 12549 && c <= 12591)
                    : c <= 12686)
                  : (c <= 12735 || (c < 13312
                    ? (c >= 12784 && c <= 12799)
                    : c <= 19903)))
                : (c <= 42124 || (c < 42512
                  ? (c < 42240
                    ? (c >= 42192 && c <= 42237)
                    : c <= 42508)
                  : (c <= 42539 || (c < 42612
                    ? (c >= 42560 && c <= 42607)
                    : c <= 42621)))))))
            : (c <= 42737 || (c < 43232
              ? (c < 42965
                ? (c < 42891
                  ? (c < 42786
                    ? (c >= 42775 && c <= 42783)
                    : c <= 42888)
                  : (c <= 42954 || (c < 42963
                    ? (c >= 42960 && c <= 42961)
                    : c <= 42963)))
                : (c <= 42969 || (c < 43072
                  ? (c < 43052
                    ? (c >= 42994 && c <= 43047)
                    : c <= 43052)
                  : (c <= 43123 || (c < 43216
                    ? (c >= 43136 && c <= 43205)
                    : c <= 43225)))))
              : (c <= 43255 || (c < 43471
                ? (c < 43312
                  ? (c < 43261
                    ? c == 43259
                    : c <= 43309)
                  : (c <= 43347 || (c < 43392
                    ? (c >= 43360 && c <= 43388)
                    : c <= 43456)))
                : (c <= 43481 || (c < 43584
                  ? (c < 43520
                    ? (c >= 43488 && c <= 43518)
                    : c <= 43574)
                  : (c <= 43597 || (c >= 43600 && c <= 43609)))))))))))))))
    : (c <= 43638 || (c < 71453
      ? (c < 67639
        ? (c < 65345
          ? (c < 64312
            ? (c < 43888
              ? (c < 43785
                ? (c < 43744
                  ? (c < 43739
                    ? (c >= 43642 && c <= 43714)
                    : c <= 43741)
                  : (c <= 43759 || (c < 43777
                    ? (c >= 43762 && c <= 43766)
                    : c <= 43782)))
                : (c <= 43790 || (c < 43816
                  ? (c < 43808
                    ? (c >= 43793 && c <= 43798)
                    : c <= 43814)
                  : (c <= 43822 || (c < 43868
                    ? (c >= 43824 && c <= 43866)
                    : c <= 43881)))))
              : (c <= 44010 || (c < 63744
                ? (c < 44032
                  ? (c < 44016
                    ? (c >= 44012 && c <= 44013)
                    : c <= 44025)
                  : (c <= 55203 || (c < 55243
                    ? (c >= 55216 && c <= 55238)
                    : c <= 55291)))
                : (c <= 64109 || (c < 64275
                  ? (c < 64256
                    ? (c >= 64112 && c <= 64217)
                    : c <= 64262)
                  : (c <= 64279 || (c < 64298
                    ? (c >= 64285 && c <= 64296)
                    : c <= 64310)))))))
            : (c <= 64316 || (c < 65075
              ? (c < 64612
                ? (c < 64323
                  ? (c < 64320
                    ? c == 64318
                    : c <= 64321)
                  : (c <= 64324 || (c < 64467
                    ? (c >= 64326 && c <= 64433)
                    : c <= 64605)))
                : (c <= 64829 || (c < 65008
                  ? (c < 64914
                    ? (c >= 64848 && c <= 64911)
                    : c <= 64967)
                  : (c <= 65017 || (c < 65056
                    ? (c >= 65024 && c <= 65039)
                    : c <= 65071)))))
              : (c <= 65076 || (c < 65147
                ? (c < 65139
                  ? (c < 65137
                    ? (c >= 65101 && c <= 65103)
                    : c <= 65137)
                  : (c <= 65139 || (c < 65145
                    ? c == 65143
                    : c <= 65145)))
                : (c <= 65147 || (c < 65296
                  ? (c < 65151
                    ? c == 65149
                    : c <= 65276)
                  : (c <= 65305 || (c < 65343
                    ? (c >= 65313 && c <= 65338)
                    : c <= 65343)))))))))
          : (c <= 65370 || (c < 66513
            ? (c < 65664
              ? (c < 65536
                ? (c < 65482
                  ? (c < 65474
                    ? (c >= 65382 && c <= 65470)
                    : c <= 65479)
                  : (c <= 65487 || (c < 65498
                    ? (c >= 65490 && c <= 65495)
                    : c <= 65500)))
                : (c <= 65547 || (c < 65596
                  ? (c < 65576
                    ? (c >= 65549 && c <= 65574)
                    : c <= 65594)
                  : (c <= 65597 || (c < 65616
                    ? (c >= 65599 && c <= 65613)
                    : c <= 65629)))))
              : (c <= 65786 || (c < 66304
                ? (c < 66176
                  ? (c < 66045
                    ? (c >= 65856 && c <= 65908)
                    : c <= 66045)
                  : (c <= 66204 || (c < 66272
                    ? (c >= 66208 && c <= 66256)
                    : c <= 66272)))
                : (c <= 66335 || (c < 66432
                  ? (c < 66384
                    ? (c >= 66349 && c <= 66378)
                    : c <= 66426)
                  : (c <= 66461 || (c < 66504
                    ? (c >= 66464 && c <= 66499)
                    : c <= 66511)))))))
            : (c <= 66517 || (c < 66979
              ? (c < 66864
                ? (c < 66736
                  ? (c < 66720
                    ? (c >= 66560 && c <= 66717)
                    : c <= 66729)
                  : (c <= 66771 || (c < 66816
                    ? (c >= 66776 && c <= 66811)
                    : c <= 66855)))
                : (c <= 66915 || (c < 66956
                  ? (c < 66940
                    ? (c >= 66928 && c <= 66938)
                    : c <= 66954)
                  : (c <= 66962 || (c < 66967
                    ? (c >= 66964 && c <= 66965)
                    : c <= 66977)))))
              : (c <= 66993 || (c < 67456
                ? (c < 67072
                  ? (c < 67003
                    ? (c >= 66995 && c <= 67001)
                    : c <= 67004)
                  : (c <= 67382 || (c < 67424
                    ? (c >= 67392 && c <= 67413)
                    : c <= 67431)))
                : (c <= 67461 || (c < 67584
                  ? (c < 67506
                    ? (c >= 67463 && c <= 67504)
                    : c <= 67514)
                  : (c <= 67589 || (c < 67594
                    ? c == 67592
                    : c <= 67637)))))))))))
        : (c <= 67640 || (c < 69956
          ? (c < 68448
            ? (c < 68101
              ? (c < 67828
                ? (c < 67680
                  ? (c < 67647
                    ? c == 67644
                    : c <= 67669)
                  : (c <= 67702 || (c < 67808
                    ? (c >= 67712 && c <= 67742)
                    : c <= 67826)))
                : (c <= 67829 || (c < 67968
                  ? (c < 67872
                    ? (c >= 67840 && c <= 67861)
                    : c <= 67897)
                  : (c <= 68023 || (c < 68096
                    ? (c >= 68030 && c <= 68031)
                    : c <= 68099)))))
              : (c <= 68102 || (c < 68192
                ? (c < 68121
                  ? (c < 68117
                    ? (c >= 68108 && c <= 68115)
                    : c <= 68119)
                  : (c <= 68149 || (c < 68159
                    ? (c >= 68152 && c <= 68154)
                    : c <= 68159)))
                : (c <= 68220 || (c < 68297
                  ? (c < 68288
                    ? (c >= 68224 && c <= 68252)
                    : c <= 68295)
                  : (c <= 68326 || (c < 68416
                    ? (c >= 68352 && c <= 68405)
                    : c <= 68437)))))))
            : (c <= 68466 || (c < 69424
              ? (c < 68912
                ? (c < 68736
                  ? (c < 68608
                    ? (c >= 68480 && c <= 68497)
                    : c <= 68680)
                  : (c <= 68786 || (c < 68864
                    ? (c >= 68800 && c <= 68850)
                    : c <= 68903)))
                : (c <= 68921 || (c < 69296
                  ? (c < 69291
                    ? (c >= 69248 && c <= 69289)
                    : c <= 69292)
                  : (c <= 69297 || (c < 69415
                    ? (c >= 69376 && c <= 69404)
                    : c <= 69415)))))
              : (c <= 69456 || (c < 69759
                ? (c < 69600
                  ? (c < 69552
                    ? (c >= 69488 && c <= 69509)
                    : c <= 69572)
                  : (c <= 69622 || (c < 69734
                    ? (c >= 69632 && c <= 69702)
                    : c <= 69749)))
                : (c <= 69818 || (c < 69872
                  ? (c < 69840
                    ? c == 69826
                    : c <= 69864)
                  : (c <= 69881 || (c < 69942
                    ? (c >= 69888 && c <= 69940)
                    : c <= 69951)))))))))
          : (c <= 69959 || (c < 70459
            ? (c < 70282
              ? (c < 70108
                ? (c < 70016
                  ? (c < 70006
                    ? (c >= 69968 && c <= 70003)
                    : c <= 70006)
                  : (c <= 70084 || (c < 70094
                    ? (c >= 70089 && c <= 70092)
                    : c <= 70106)))
                : (c <= 70108 || (c < 70206
                  ? (c < 70163
                    ? (c >= 70144 && c <= 70161)
                    : c <= 70199)
                  : (c <= 70206 || (c < 70280
                    ? (c >= 70272 && c <= 70278)
                    : c <= 70280)))))
              : (c <= 70285 || (c < 70405
                ? (c < 70320
                  ? (c < 70303
                    ? (c >= 70287 && c <= 70301)
                    : c <= 70312)
                  : (c <= 70378 || (c < 70400
                    ? (c >= 70384 && c <= 70393)
                    : c <= 70403)))
                : (c <= 70412 || (c < 70442
                  ? (c < 70419
                    ? (c >= 70415 && c <= 70416)
                    : c <= 70440)
                  : (c <= 70448 || (c < 70453
                    ? (c >= 70450 && c <= 70451)
                    : c <= 70457)))))))
            : (c <= 70468 || (c < 70855
              ? (c < 70502
                ? (c < 70480
                  ? (c < 70475
                    ? (c >= 70471 && c <= 70472)
                    : c <= 70477)
                  : (c <= 70480 || (c < 70493
                    ? c == 70487
                    : c <= 70499)))
                : (c <= 70508 || (c < 70736
                  ? (c < 70656
                    ? (c >= 70512 && c <= 70516)
                    : c <= 70730)
                  : (c <= 70745 || (c < 70784
                    ? (c >= 70750 && c <= 70753)
                    : c <= 70853)))))
              : (c <= 70855 || (c < 71236
                ? (c < 71096
                  ? (c < 71040
                    ? (c >= 70864 && c <= 70873)
                    : c <= 71093)
                  : (c <= 71104 || (c < 71168
                    ? (c >= 71128 && c <= 71133)
                    : c <= 71232)))
                : (c <= 71236 || (c < 71360
                  ? (c < 71296
                    ? (c >= 71248 && c <= 71257)
                    : c <= 71352)
                  : (c <= 71369 || (c >= 71424 && c <= 71450)))))))))))))
      : (c <= 71467 || (c < 119973
        ? (c < 77824
          ? (c < 72760
            ? (c < 72016
              ? (c < 71945
                ? (c < 71680
                  ? (c < 71488
                    ? (c >= 71472 && c <= 71481)
                    : c <= 71494)
                  : (c <= 71738 || (c < 71935
                    ? (c >= 71840 && c <= 71913)
                    : c <= 71942)))
                : (c <= 71945 || (c < 71960
                  ? (c < 71957
                    ? (c >= 71948 && c <= 71955)
                    : c <= 71958)
                  : (c <= 71989 || (c < 71995
                    ? (c >= 71991 && c <= 71992)
                    : c <= 72003)))))
              : (c <= 72025 || (c < 72263
                ? (c < 72154
                  ? (c < 72106
                    ? (c >= 72096 && c <= 72103)
                    : c <= 72151)
                  : (c <= 72161 || (c < 72192
                    ? (c >= 72163 && c <= 72164)
                    : c <= 72254)))
                : (c <= 72263 || (c < 72368
                  ? (c < 72349
                    ? (c >= 72272 && c <= 72345)
                    : c <= 72349)
                  : (c <= 72440 || (c < 72714
                    ? (c >= 72704 && c <= 72712)
                    : c <= 72758)))))))
            : (c <= 72768 || (c < 73056
              ? (c < 72968
                ? (c < 72850
                  ? (c < 72818
                    ? (c >= 72784 && c <= 72793)
                    : c <= 72847)
                  : (c <= 72871 || (c < 72960
                    ? (c >= 72873 && c <= 72886)
                    : c <= 72966)))
                : (c <= 72969 || (c < 73020
                  ? (c < 73018
                    ? (c >= 72971 && c <= 73014)
                    : c <= 73018)
                  : (c <= 73021 || (c < 73040
                    ? (c >= 73023 && c <= 73031)
                    : c <= 73049)))))
              : (c <= 73061 || (c < 73440
                ? (c < 73104
                  ? (c < 73066
                    ? (c >= 73063 && c <= 73064)
                    : c <= 73102)
                  : (c <= 73105 || (c < 73120
                    ? (c >= 73107 && c <= 73112)
                    : c <= 73129)))
                : (c <= 73462 || (c < 74752
                  ? (c < 73728
                    ? c == 73648
                    : c <= 74649)
                  : (c <= 74862 || (c < 77712
                    ? (c >= 74880 && c <= 75075)
                    : c <= 77808)))))))))
          : (c <= 78894 || (c < 110576
            ? (c < 93027
              ? (c < 92864
                ? (c < 92736
                  ? (c < 92160
                    ? (c >= 82944 && c <= 83526)
                    : c <= 92728)
                  : (c <= 92766 || (c < 92784
                    ? (c >= 92768 && c <= 92777)
                    : c <= 92862)))
                : (c <= 92873 || (c < 92928
                  ? (c < 92912
                    ? (c >= 92880 && c <= 92909)
                    : c <= 92916)
                  : (c <= 92982 || (c < 93008
                    ? (c >= 92992 && c <= 92995)
                    : c <= 93017)))))
              : (c <= 93047 || (c < 94176
                ? (c < 93952
                  ? (c < 93760
                    ? (c >= 93053 && c <= 93071)
                    : c <= 93823)
                  : (c <= 94026 || (c < 94095
                    ? (c >= 94031 && c <= 94087)
                    : c <= 94111)))
                : (c <= 94177 || (c < 94208
                  ? (c < 94192
                    ? (c >= 94179 && c <= 94180)
                    : c <= 94193)
                  : (c <= 100343 || (c < 101632
                    ? (c >= 100352 && c <= 101589)
                    : c <= 101640)))))))
            : (c <= 110579 || (c < 118528
              ? (c < 110960
                ? (c < 110592
                  ? (c < 110589
                    ? (c >= 110581 && c <= 110587)
                    : c <= 110590)
                  : (c <= 110882 || (c < 110948
                    ? (c >= 110928 && c <= 110930)
                    : c <= 110951)))
                : (c <= 111355 || (c < 113792
                  ? (c < 113776
                    ? (c >= 113664 && c <= 113770)
                    : c <= 113788)
                  : (c <= 113800 || (c < 113821
                    ? (c >= 113808 && c <= 113817)
                    : c <= 113822)))))
              : (c <= 118573 || (c < 119210
                ? (c < 119149
                  ? (c < 119141
                    ? (c >= 118576 && c <= 118598)
                    : c <= 119145)
                  : (c <= 119154 || (c < 119173
                    ? (c >= 119163 && c <= 119170)
                    : c <= 119179)))
                : (c <= 119213 || (c < 119894
                  ? (c < 119808
                    ? (c >= 119362 && c <= 119364)
                    : c <= 119892)
                  : (c <= 119964 || (c < 119970
                    ? (c >= 119966 && c <= 119967)
                    : c <= 119970)))))))))))
        : (c <= 119974 || (c < 124912
          ? (c < 120746
            ? (c < 120134
              ? (c < 120071
                ? (c < 119995
                  ? (c < 119982
                    ? (c >= 119977 && c <= 119980)
                    : c <= 119993)
                  : (c <= 119995 || (c < 120005
                    ? (c >= 119997 && c <= 120003)
                    : c <= 120069)))
                : (c <= 120074 || (c < 120094
                  ? (c < 120086
                    ? (c >= 120077 && c <= 120084)
                    : c <= 120092)
                  : (c <= 120121 || (c < 120128
                    ? (c >= 120123 && c <= 120126)
                    : c <= 120132)))))
              : (c <= 120134 || (c < 120572
                ? (c < 120488
                  ? (c < 120146
                    ? (c >= 120138 && c <= 120144)
                    : c <= 120485)
                  : (c <= 120512 || (c < 120540
                    ? (c >= 120514 && c <= 120538)
                    : c <= 120570)))
                : (c <= 120596 || (c < 120656
                  ? (c < 120630
                    ? (c >= 120598 && c <= 120628)
                    : c <= 120654)
                  : (c <= 120686 || (c < 120714
                    ? (c >= 120688 && c <= 120712)
                    : c <= 120744)))))))
            : (c <= 120770 || (c < 122907
              ? (c < 121476
                ? (c < 121344
                  ? (c < 120782
                    ? (c >= 120772 && c <= 120779)
                    : c <= 120831)
                  : (c <= 121398 || (c < 121461
                    ? (c >= 121403 && c <= 121452)
                    : c <= 121461)))
                : (c <= 121476 || (c < 122624
                  ? (c < 121505
                    ? (c >= 121499 && c <= 121503)
                    : c <= 121519)
                  : (c <= 122654 || (c < 122888
                    ? (c >= 122880 && c <= 122886)
                    : c <= 122904)))))
              : (c <= 122913 || (c < 123214
                ? (c < 123136
                  ? (c < 122918
                    ? (c >= 122915 && c <= 122916)
                    : c <= 122922)
                  : (c <= 123180 || (c < 123200
                    ? (c >= 123184 && c <= 123197)
                    : c <= 123209)))
                : (c <= 123214 || (c < 124896
                  ? (c < 123584
                    ? (c >= 123536 && c <= 123566)
                    : c <= 123641)
                  : (c <= 124902 || (c < 124909
                    ? (c >= 124904 && c <= 124907)
                    : c <= 124910)))))))))
          : (c <= 124926 || (c < 126557
            ? (c < 126521
              ? (c < 126469
                ? (c < 125184
                  ? (c < 125136
                    ? (c >= 124928 && c <= 125124)
                    : c <= 125142)
                  : (c <= 125259 || (c < 126464
                    ? (c >= 125264 && c <= 125273)
                    : c <= 126467)))
                : (c <= 126495 || (c < 126503
                  ? (c < 126500
                    ? (c >= 126497 && c <= 126498)
                    : c <= 126500)
                  : (c <= 126503 || (c < 126516
                    ? (c >= 126505 && c <= 126514)
                    : c <= 126519)))))
              : (c <= 126521 || (c < 126541
                ? (c < 126535
                  ? (c < 126530
                    ? c == 126523
                    : c <= 126530)
                  : (c <= 126535 || (c < 126539
                    ? c == 126537
                    : c <= 126539)))
                : (c <= 126543 || (c < 126551
                  ? (c < 126548
                    ? (c >= 126545 && c <= 126546)
                    : c <= 126548)
                  : (c <= 126551 || (c < 126555
                    ? c == 126553
                    : c <= 126555)))))))
            : (c <= 126557 || (c < 126629
              ? (c < 126580
                ? (c < 126564
                  ? (c < 126561
                    ? c == 126559
                    : c <= 126562)
                  : (c <= 126564 || (c < 126572
                    ? (c >= 126567 && c <= 126570)
                    : c <= 126578)))
                : (c <= 126583 || (c < 126592
                  ? (c < 126590
                    ? (c >= 126585 && c <= 126588)
                    : c <= 126590)
                  : (c <= 126601 || (c < 126625
                    ? (c >= 126603 && c <= 126619)
                    : c <= 126627)))))
              : (c <= 126633 || (c < 178208
                ? (c < 131072
                  ? (c < 130032
                    ? (c >= 126635 && c <= 126651)
                    : c <= 130041)
                  : (c <= 173791 || (c < 177984
                    ? (c >= 173824 && c <= 177976)
                    : c <= 178205)))
                : (c <= 183969 || (c < 196608
                  ? (c < 194560
                    ? (c >= 183984 && c <= 191456)
                    : c <= 195101)
                  : (c <= 201546 || (c >= 917760 && c <= 917999)))))))))))))))));
}

static inline bool sym_name_character_set_7(int32_t c) {
  return (c < 43642
    ? (c < 3792
      ? (c < 2763
        ? (c < 2112
          ? (c < 1162
            ? (c < 748
              ? (c < 186
                ? (c < 170
                  ? (c < 'a'
                    ? (c >= 'A' && c <= 'Z')
                    : c <= 'z')
                  : (c <= 170 || (c < 183
                    ? c == 181
                    : c <= 183)))
                : (c <= 186 || (c < 248
                  ? (c < 216
                    ? (c >= 192 && c <= 214)
                    : c <= 246)
                  : (c <= 705 || (c < 736
                    ? (c >= 710 && c <= 721)
                    : c <= 740)))))
              : (c <= 748 || (c < 902
                ? (c < 886
                  ? (c < 768
                    ? c == 750
                    : c <= 884)
                  : (c <= 887 || (c < 895
                    ? (c >= 891 && c <= 893)
                    : c <= 895)))
                : (c <= 906 || (c < 931
                  ? (c < 910
                    ? c == 908
                    : c <= 929)
                  : (c <= 1013 || (c < 1155
                    ? (c >= 1015 && c <= 1153)
                    : c <= 1159)))))))
            : (c <= 1327 || (c < 1568
              ? (c < 1473
                ? (c < 1376
                  ? (c < 1369
                    ? (c >= 1329 && c <= 1366)
                    : c <= 1369)
                  : (c <= 1416 || (c < 1471
                    ? (c >= 1425 && c <= 1469)
                    : c <= 1471)))
                : (c <= 1474 || (c < 1488
                  ? (c < 1479
                    ? (c >= 1476 && c <= 1477)
                    : c <= 1479)
                  : (c <= 1514 || (c < 1552
                    ? (c >= 1519 && c <= 1522)
                    : c <= 1562)))))
              : (c <= 1641 || (c < 1808
                ? (c < 1759
                  ? (c < 1749
                    ? (c >= 1646 && c <= 1747)
                    : c <= 1756)
                  : (c <= 1768 || (c < 1791
                    ? (c >= 1770 && c <= 1788)
                    : c <= 1791)))
                : (c <= 1866 || (c < 2042
                  ? (c < 1984
                    ? (c >= 1869 && c <= 1969)
                    : c <= 2037)
                  : (c <= 2042 || (c < 2048
                    ? c == 2045
                    : c <= 2093)))))))))
          : (c <= 2139 || (c < 2565
            ? (c < 2482
              ? (c < 2406
                ? (c < 2185
                  ? (c < 2160
                    ? (c >= 2144 && c <= 2154)
                    : c <= 2183)
                  : (c <= 2190 || (c < 2275
                    ? (c >= 2200 && c <= 2273)
                    : c <= 2403)))
                : (c <= 2415 || (c < 2447
                  ? (c < 2437
                    ? (c >= 2417 && c <= 2435)
                    : c <= 2444)
                  : (c <= 2448 || (c < 2474
                    ? (c >= 2451 && c <= 2472)
                    : c <= 2480)))))
              : (c <= 2482 || (c < 2524
                ? (c < 2503
                  ? (c < 2492
                    ? (c >= 2486 && c <= 2489)
                    : c <= 2500)
                  : (c <= 2504 || (c < 2519
                    ? (c >= 2507 && c <= 2510)
                    : c <= 2519)))
                : (c <= 2525 || (c < 2556
                  ? (c < 2534
                    ? (c >= 2527 && c <= 2531)
                    : c <= 2545)
                  : (c <= 2556 || (c < 2561
                    ? c == 2558
                    : c <= 2563)))))))
            : (c <= 2570 || (c < 2649
              ? (c < 2616
                ? (c < 2602
                  ? (c < 2579
                    ? (c >= 2575 && c <= 2576)
                    : c <= 2600)
                  : (c <= 2608 || (c < 2613
                    ? (c >= 2610 && c <= 2611)
                    : c <= 2614)))
                : (c <= 2617 || (c < 2631
                  ? (c < 2622
                    ? c == 2620
                    : c <= 2626)
                  : (c <= 2632 || (c < 2641
                    ? (c >= 2635 && c <= 2637)
                    : c <= 2641)))))
              : (c <= 2652 || (c < 2707
                ? (c < 2689
                  ? (c < 2662
                    ? c == 2654
                    : c <= 2677)
                  : (c <= 2691 || (c < 2703
                    ? (c >= 2693 && c <= 2701)
                    : c <= 2705)))
                : (c <= 2728 || (c < 2741
                  ? (c < 2738
                    ? (c >= 2730 && c <= 2736)
                    : c <= 2739)
                  : (c <= 2745 || (c < 2759
                    ? (c >= 2748 && c <= 2757)
                    : c <= 2761)))))))))))
        : (c <= 2765 || (c < 3200
          ? (c < 2969
            ? (c < 2876
              ? (c < 2821
                ? (c < 2790
                  ? (c < 2784
                    ? c == 2768
                    : c <= 2787)
                  : (c <= 2799 || (c < 2817
                    ? (c >= 2809 && c <= 2815)
                    : c <= 2819)))
                : (c <= 2828 || (c < 2858
                  ? (c < 2835
                    ? (c >= 2831 && c <= 2832)
                    : c <= 2856)
                  : (c <= 2864 || (c < 2869
                    ? (c >= 2866 && c <= 2867)
                    : c <= 2873)))))
              : (c <= 2884 || (c < 2918
                ? (c < 2901
                  ? (c < 2891
                    ? (c >= 2887 && c <= 2888)
                    : c <= 2893)
                  : (c <= 2903 || (c < 2911
                    ? (c >= 2908 && c <= 2909)
                    : c <= 2915)))
                : (c <= 2927 || (c < 2949
                  ? (c < 2946
                    ? c == 2929
                    : c <= 2947)
                  : (c <= 2954 || (c < 2962
                    ? (c >= 2958 && c <= 2960)
                    : c <= 2965)))))))
            : (c <= 2970 || (c < 3072
              ? (c < 3006
                ? (c < 2979
                  ? (c < 2974
                    ? c == 2972
                    : c <= 2975)
                  : (c <= 2980 || (c < 2990
                    ? (c >= 2984 && c <= 2986)
                    : c <= 3001)))
                : (c <= 3010 || (c < 3024
                  ? (c < 3018
                    ? (c >= 3014 && c <= 3016)
                    : c <= 3021)
                  : (c <= 3024 || (c < 3046
                    ? c == 3031
                    : c <= 3055)))))
              : (c <= 3084 || (c < 3146
                ? (c < 3114
                  ? (c < 3090
                    ? (c >= 3086 && c <= 3088)
                    : c <= 3112)
                  : (c <= 3129 || (c < 3142
                    ? (c >= 3132 && c <= 3140)
                    : c <= 3144)))
                : (c <= 3149 || (c < 3165
                  ? (c < 3160
                    ? (c >= 3157 && c <= 3158)
                    : c <= 3162)
                  : (c <= 3165 || (c < 3174
                    ? (c >= 3168 && c <= 3171)
                    : c <= 3183)))))))))
          : (c <= 3203 || (c < 3461
            ? (c < 3302
              ? (c < 3260
                ? (c < 3218
                  ? (c < 3214
                    ? (c >= 3205 && c <= 3212)
                    : c <= 3216)
                  : (c <= 3240 || (c < 3253
                    ? (c >= 3242 && c <= 3251)
                    : c <= 3257)))
                : (c <= 3268 || (c < 3285
                  ? (c < 3274
                    ? (c >= 3270 && c <= 3272)
                    : c <= 3277)
                  : (c <= 3286 || (c < 3296
                    ? (c >= 3293 && c <= 3294)
                    : c <= 3299)))))
              : (c <= 3311 || (c < 3402
                ? (c < 3342
                  ? (c < 3328
                    ? (c >= 3313 && c <= 3314)
                    : c <= 3340)
                  : (c <= 3344 || (c < 3398
                    ? (c >= 3346 && c <= 3396)
                    : c <= 3400)))
                : (c <= 3406 || (c < 3430
                  ? (c < 3423
                    ? (c >= 3412 && c <= 3415)
                    : c <= 3427)
                  : (c <= 3439 || (c < 3457
                    ? (c >= 3450 && c <= 3455)
                    : c <= 3459)))))))
            : (c <= 3478 || (c < 3648
              ? (c < 3535
                ? (c < 3517
                  ? (c < 3507
                    ? (c >= 3482 && c <= 3505)
                    : c <= 3515)
                  : (c <= 3517 || (c < 3530
                    ? (c >= 3520 && c <= 3526)
                    : c <= 3530)))
                : (c <= 3540 || (c < 3558
                  ? (c < 3544
                    ? c == 3542
                    : c <= 3551)
                  : (c <= 3567 || (c < 3585
                    ? (c >= 3570 && c <= 3571)
                    : c <= 3642)))))
              : (c <= 3662 || (c < 3749
                ? (c < 3716
                  ? (c < 3713
                    ? (c >= 3664 && c <= 3673)
                    : c <= 3714)
                  : (c <= 3716 || (c < 3724
                    ? (c >= 3718 && c <= 3722)
                    : c <= 3747)))
                : (c <= 3749 || (c < 3782
                  ? (c < 3776
                    ? (c >= 3751 && c <= 3773)
                    : c <= 3780)
                  : (c <= 3782 || (c >= 3784 && c <= 3789)))))))))))))
      : (c <= 3801 || (c < 8027
        ? (c < 5952
          ? (c < 4698
            ? (c < 3993
              ? (c < 3895
                ? (c < 3864
                  ? (c < 3840
                    ? (c >= 3804 && c <= 3807)
                    : c <= 3840)
                  : (c <= 3865 || (c < 3893
                    ? (c >= 3872 && c <= 3881)
                    : c <= 3893)))
                : (c <= 3895 || (c < 3913
                  ? (c < 3902
                    ? c == 3897
                    : c <= 3911)
                  : (c <= 3948 || (c < 3974
                    ? (c >= 3953 && c <= 3972)
                    : c <= 3991)))))
              : (c <= 4028 || (c < 4301
                ? (c < 4176
                  ? (c < 4096
                    ? c == 4038
                    : c <= 4169)
                  : (c <= 4253 || (c < 4295
                    ? (c >= 4256 && c <= 4293)
                    : c <= 4295)))
                : (c <= 4301 || (c < 4682
                  ? (c < 4348
                    ? (c >= 4304 && c <= 4346)
                    : c <= 4680)
                  : (c <= 4685 || (c < 4696
                    ? (c >= 4688 && c <= 4694)
                    : c <= 4696)))))))
            : (c <= 4701 || (c < 4957
              ? (c < 4800
                ? (c < 4752
                  ? (c < 4746
                    ? (c >= 4704 && c <= 4744)
                    : c <= 4749)
                  : (c <= 4784 || (c < 4792
                    ? (c >= 4786 && c <= 4789)
                    : c <= 4798)))
                : (c <= 4800 || (c < 4824
                  ? (c < 4808
                    ? (c >= 4802 && c <= 4805)
                    : c <= 4822)
                  : (c <= 4880 || (c < 4888
                    ? (c >= 4882 && c <= 4885)
                    : c <= 4954)))))
              : (c <= 4959 || (c < 5743
                ? (c < 5024
                  ? (c < 4992
                    ? (c >= 4969 && c <= 4977)
                    : c <= 5007)
                  : (c <= 5109 || (c < 5121
                    ? (c >= 5112 && c <= 5117)
                    : c <= 5740)))
                : (c <= 5759 || (c < 5870
                  ? (c < 5792
                    ? (c >= 5761 && c <= 5786)
                    : c <= 5866)
                  : (c <= 5880 || (c < 5919
                    ? (c >= 5888 && c <= 5909)
                    : c <= 5940)))))))))
          : (c <= 5971 || (c < 6783
            ? (c < 6320
              ? (c < 6108
                ? (c < 6002
                  ? (c < 5998
                    ? (c >= 5984 && c <= 5996)
                    : c <= 6000)
                  : (c <= 6003 || (c < 6103
                    ? (c >= 6016 && c <= 6099)
                    : c <= 6103)))
                : (c <= 6109 || (c < 6159
                  ? (c < 6155
                    ? (c >= 6112 && c <= 6121)
                    : c <= 6157)
                  : (c <= 6169 || (c < 6272
                    ? (c >= 6176 && c <= 6264)
                    : c <= 6314)))))
              : (c <= 6389 || (c < 6528
                ? (c < 6448
                  ? (c < 6432
                    ? (c >= 6400 && c <= 6430)
                    : c <= 6443)
                  : (c <= 6459 || (c < 6512
                    ? (c >= 6470 && c <= 6509)
                    : c <= 6516)))
                : (c <= 6571 || (c < 6656
                  ? (c < 6608
                    ? (c >= 6576 && c <= 6601)
                    : c <= 6618)
                  : (c <= 6683 || (c < 6752
                    ? (c >= 6688 && c <= 6750)
                    : c <= 6780)))))))
            : (c <= 6793 || (c < 7296
              ? (c < 6992
                ? (c < 6832
                  ? (c < 6823
                    ? (c >= 6800 && c <= 6809)
                    : c <= 6823)
                  : (c <= 6845 || (c < 6912
                    ? (c >= 6847 && c <= 6862)
                    : c <= 6988)))
                : (c <= 7001 || (c < 7168
                  ? (c < 7040
                    ? (c >= 7019 && c <= 7027)
                    : c <= 7155)
                  : (c <= 7223 || (c < 7245
                    ? (c >= 7232 && c <= 7241)
                    : c <= 7293)))))
              : (c <= 7304 || (c < 7960
                ? (c < 7376
                  ? (c < 7357
                    ? (c >= 7312 && c <= 7354)
                    : c <= 7359)
                  : (c <= 7378 || (c < 7424
                    ? (c >= 7380 && c <= 7418)
                    : c <= 7957)))
                : (c <= 7965 || (c < 8016
                  ? (c < 8008
                    ? (c >= 7968 && c <= 8005)
                    : c <= 8013)
                  : (c <= 8023 || c == 8025))))))))))
        : (c <= 8027 || (c < 11728
          ? (c < 8469
            ? (c < 8182
              ? (c < 8130
                ? (c < 8064
                  ? (c < 8031
                    ? c == 8029
                    : c <= 8061)
                  : (c <= 8116 || (c < 8126
                    ? (c >= 8118 && c <= 8124)
                    : c <= 8126)))
                : (c <= 8132 || (c < 8150
                  ? (c < 8144
                    ? (c >= 8134 && c <= 8140)
                    : c <= 8147)
                  : (c <= 8155 || (c < 8178
                    ? (c >= 8160 && c <= 8172)
                    : c <= 8180)))))
              : (c <= 8188 || (c < 8400
                ? (c < 8305
                  ? (c < 8276
                    ? (c >= 8255 && c <= 8256)
                    : c <= 8276)
                  : (c <= 8305 || (c < 8336
                    ? c == 8319
                    : c <= 8348)))
                : (c <= 8412 || (c < 8450
                  ? (c < 8421
                    ? c == 8417
                    : c <= 8432)
                  : (c <= 8450 || (c < 8458
                    ? c == 8455
                    : c <= 8467)))))))
            : (c <= 8469 || (c < 11520
              ? (c < 8508
                ? (c < 8486
                  ? (c < 8484
                    ? (c >= 8472 && c <= 8477)
                    : c <= 8484)
                  : (c <= 8486 || (c < 8490
                    ? c == 8488
                    : c <= 8505)))
                : (c <= 8511 || (c < 8544
                  ? (c < 8526
                    ? (c >= 8517 && c <= 8521)
                    : c <= 8526)
                  : (c <= 8584 || (c < 11499
                    ? (c >= 11264 && c <= 11492)
                    : c <= 11507)))))
              : (c <= 11557 || (c < 11680
                ? (c < 11568
                  ? (c < 11565
                    ? c == 11559
                    : c <= 11565)
                  : (c <= 11623 || (c < 11647
                    ? c == 11631
                    : c <= 11670)))
                : (c <= 11686 || (c < 11704
                  ? (c < 11696
                    ? (c >= 11688 && c <= 11694)
                    : c <= 11702)
                  : (c <= 11710 || (c < 11720
                    ? (c >= 11712 && c <= 11718)
                    : c <= 11726)))))))))
          : (c <= 11734 || (c < 42775
            ? (c < 12549
              ? (c < 12344
                ? (c < 12293
                  ? (c < 11744
                    ? (c >= 11736 && c <= 11742)
                    : c <= 11775)
                  : (c <= 12295 || (c < 12337
                    ? (c >= 12321 && c <= 12335)
                    : c <= 12341)))
                : (c <= 12348 || (c < 12445
                  ? (c < 12441
                    ? (c >= 12353 && c <= 12438)
                    : c <= 12442)
                  : (c <= 12447 || (c < 12540
                    ? (c >= 12449 && c <= 12538)
                    : c <= 12543)))))
              : (c <= 12591 || (c < 42192
                ? (c < 12784
                  ? (c < 12704
                    ? (c >= 12593 && c <= 12686)
                    : c <= 12735)
                  : (c <= 12799 || (c < 19968
                    ? (c >= 13312 && c <= 19903)
                    : c <= 42124)))
                : (c <= 42237 || (c < 42560
                  ? (c < 42512
                    ? (c >= 42240 && c <= 42508)
                    : c <= 42539)
                  : (c <= 42607 || (c < 42623
                    ? (c >= 42612 && c <= 42621)
                    : c <= 42737)))))))
            : (c <= 42783 || (c < 43259
              ? (c < 42994
                ? (c < 42960
                  ? (c < 42891
                    ? (c >= 42786 && c <= 42888)
                    : c <= 42954)
                  : (c <= 42961 || (c < 42965
                    ? c == 42963
                    : c <= 42969)))
                : (c <= 43047 || (c < 43136
                  ? (c < 43072
                    ? c == 43052
                    : c <= 43123)
                  : (c <= 43205 || (c < 43232
                    ? (c >= 43216 && c <= 43225)
                    : c <= 43255)))))
              : (c <= 43259 || (c < 43488
                ? (c < 43360
                  ? (c < 43312
                    ? (c >= 43261 && c <= 43309)
                    : c <= 43347)
                  : (c <= 43388 || (c < 43471
                    ? (c >= 43392 && c <= 43456)
                    : c <= 43481)))
                : (c <= 43518 || (c < 43600
                  ? (c < 43584
                    ? (c >= 43520 && c <= 43574)
                    : c <= 43597)
                  : (c <= 43609 || (c >= 43616 && c <= 43638)))))))))))))))
    : (c <= 43714 || (c < 71472
      ? (c < 67644
        ? (c < 65382
          ? (c < 64318
            ? (c < 44012
              ? (c < 43793
                ? (c < 43762
                  ? (c < 43744
                    ? (c >= 43739 && c <= 43741)
                    : c <= 43759)
                  : (c <= 43766 || (c < 43785
                    ? (c >= 43777 && c <= 43782)
                    : c <= 43790)))
                : (c <= 43798 || (c < 43824
                  ? (c < 43816
                    ? (c >= 43808 && c <= 43814)
                    : c <= 43822)
                  : (c <= 43866 || (c < 43888
                    ? (c >= 43868 && c <= 43881)
                    : c <= 44010)))))
              : (c <= 44013 || (c < 64112
                ? (c < 55216
                  ? (c < 44032
                    ? (c >= 44016 && c <= 44025)
                    : c <= 55203)
                  : (c <= 55238 || (c < 63744
                    ? (c >= 55243 && c <= 55291)
                    : c <= 64109)))
                : (c <= 64217 || (c < 64285
                  ? (c < 64275
                    ? (c >= 64256 && c <= 64262)
                    : c <= 64279)
                  : (c <= 64296 || (c < 64312
                    ? (c >= 64298 && c <= 64310)
                    : c <= 64316)))))))
            : (c <= 64318 || (c < 65101
              ? (c < 64848
                ? (c < 64326
                  ? (c < 64323
                    ? (c >= 64320 && c <= 64321)
                    : c <= 64324)
                  : (c <= 64433 || (c < 64612
                    ? (c >= 64467 && c <= 64605)
                    : c <= 64829)))
                : (c <= 64911 || (c < 65024
                  ? (c < 65008
                    ? (c >= 64914 && c <= 64967)
                    : c <= 65017)
                  : (c <= 65039 || (c < 65075
                    ? (c >= 65056 && c <= 65071)
                    : c <= 65076)))))
              : (c <= 65103 || (c < 65149
                ? (c < 65143
                  ? (c < 65139
                    ? c == 65137
                    : c <= 65139)
                  : (c <= 65143 || (c < 65147
                    ? c == 65145
                    : c <= 65147)))
                : (c <= 65149 || (c < 65313
                  ? (c < 65296
                    ? (c >= 65151 && c <= 65276)
                    : c <= 65305)
                  : (c <= 65338 || (c < 65345
                    ? c == 65343
                    : c <= 65370)))))))))
          : (c <= 65470 || (c < 66560
            ? (c < 65856
              ? (c < 65549
                ? (c < 65490
                  ? (c < 65482
                    ? (c >= 65474 && c <= 65479)
                    : c <= 65487)
                  : (c <= 65495 || (c < 65536
                    ? (c >= 65498 && c <= 65500)
                    : c <= 65547)))
                : (c <= 65574 || (c < 65599
                  ? (c < 65596
                    ? (c >= 65576 && c <= 65594)
                    : c <= 65597)
                  : (c <= 65613 || (c < 65664
                    ? (c >= 65616 && c <= 65629)
                    : c <= 65786)))))
              : (c <= 65908 || (c < 66349
                ? (c < 66208
                  ? (c < 66176
                    ? c == 66045
                    : c <= 66204)
                  : (c <= 66256 || (c < 66304
                    ? c == 66272
                    : c <= 66335)))
                : (c <= 66378 || (c < 66464
                  ? (c < 66432
                    ? (c >= 66384 && c <= 66426)
                    : c <= 66461)
                  : (c <= 66499 || (c < 66513
                    ? (c >= 66504 && c <= 66511)
                    : c <= 66517)))))))
            : (c <= 66717 || (c < 66995
              ? (c < 66928
                ? (c < 66776
                  ? (c < 66736
                    ? (c >= 66720 && c <= 66729)
                    : c <= 66771)
                  : (c <= 66811 || (c < 66864
                    ? (c >= 66816 && c <= 66855)
                    : c <= 66915)))
                : (c <= 66938 || (c < 66964
                  ? (c < 66956
                    ? (c >= 66940 && c <= 66954)
                    : c <= 66962)
                  : (c <= 66965 || (c < 66979
                    ? (c >= 66967 && c <= 66977)
                    : c <= 66993)))))
              : (c <= 67001 || (c < 67463
                ? (c < 67392
                  ? (c < 67072
                    ? (c >= 67003 && c <= 67004)
                    : c <= 67382)
                  : (c <= 67413 || (c < 67456
                    ? (c >= 67424 && c <= 67431)
                    : c <= 67461)))
                : (c <= 67504 || (c < 67592
                  ? (c < 67584
                    ? (c >= 67506 && c <= 67514)
                    : c <= 67589)
                  : (c <= 67592 || (c < 67639
                    ? (c >= 67594 && c <= 67637)
                    : c <= 67640)))))))))))
        : (c <= 67644 || (c < 69968
          ? (c < 68480
            ? (c < 68108
              ? (c < 67840
                ? (c < 67712
                  ? (c < 67680
                    ? (c >= 67647 && c <= 67669)
                    : c <= 67702)
                  : (c <= 67742 || (c < 67828
                    ? (c >= 67808 && c <= 67826)
                    : c <= 67829)))
                : (c <= 67861 || (c < 68030
                  ? (c < 67968
                    ? (c >= 67872 && c <= 67897)
                    : c <= 68023)
                  : (c <= 68031 || (c < 68101
                    ? (c >= 68096 && c <= 68099)
                    : c <= 68102)))))
              : (c <= 68115 || (c < 68224
                ? (c < 68152
                  ? (c < 68121
                    ? (c >= 68117 && c <= 68119)
                    : c <= 68149)
                  : (c <= 68154 || (c < 68192
                    ? c == 68159
                    : c <= 68220)))
                : (c <= 68252 || (c < 68352
                  ? (c < 68297
                    ? (c >= 68288 && c <= 68295)
                    : c <= 68326)
                  : (c <= 68405 || (c < 68448
                    ? (c >= 68416 && c <= 68437)
                    : c <= 68466)))))))
            : (c <= 68497 || (c < 69488
              ? (c < 69248
                ? (c < 68800
                  ? (c < 68736
                    ? (c >= 68608 && c <= 68680)
                    : c <= 68786)
                  : (c <= 68850 || (c < 68912
                    ? (c >= 68864 && c <= 68903)
                    : c <= 68921)))
                : (c <= 69289 || (c < 69376
                  ? (c < 69296
                    ? (c >= 69291 && c <= 69292)
                    : c <= 69297)
                  : (c <= 69404 || (c < 69424
                    ? c == 69415
                    : c <= 69456)))))
              : (c <= 69509 || (c < 69826
                ? (c < 69632
                  ? (c < 69600
                    ? (c >= 69552 && c <= 69572)
                    : c <= 69622)
                  : (c <= 69702 || (c < 69759
                    ? (c >= 69734 && c <= 69749)
                    : c <= 69818)))
                : (c <= 69826 || (c < 69888
                  ? (c < 69872
                    ? (c >= 69840 && c <= 69864)
                    : c <= 69881)
                  : (c <= 69940 || (c < 69956
                    ? (c >= 69942 && c <= 69951)
                    : c <= 69959)))))))))
          : (c <= 70003 || (c < 70471
            ? (c < 70287
              ? (c < 70144
                ? (c < 70089
                  ? (c < 70016
                    ? c == 70006
                    : c <= 70084)
                  : (c <= 70092 || (c < 70108
                    ? (c >= 70094 && c <= 70106)
                    : c <= 70108)))
                : (c <= 70161 || (c < 70272
                  ? (c < 70206
                    ? (c >= 70163 && c <= 70199)
                    : c <= 70206)
                  : (c <= 70278 || (c < 70282
                    ? c == 70280
                    : c <= 70285)))))
              : (c <= 70301 || (c < 70415
                ? (c < 70384
                  ? (c < 70320
                    ? (c >= 70303 && c <= 70312)
                    : c <= 70378)
                  : (c <= 70393 || (c < 70405
                    ? (c >= 70400 && c <= 70403)
                    : c <= 70412)))
                : (c <= 70416 || (c < 70450
                  ? (c < 70442
                    ? (c >= 70419 && c <= 70440)
                    : c <= 70448)
                  : (c <= 70451 || (c < 70459
                    ? (c >= 70453 && c <= 70457)
                    : c <= 70468)))))))
            : (c <= 70472 || (c < 70864
              ? (c < 70512
                ? (c < 70487
                  ? (c < 70480
                    ? (c >= 70475 && c <= 70477)
                    : c <= 70480)
                  : (c <= 70487 || (c < 70502
                    ? (c >= 70493 && c <= 70499)
                    : c <= 70508)))
                : (c <= 70516 || (c < 70750
                  ? (c < 70736
                    ? (c >= 70656 && c <= 70730)
                    : c <= 70745)
                  : (c <= 70753 || (c < 70855
                    ? (c >= 70784 && c <= 70853)
                    : c <= 70855)))))
              : (c <= 70873 || (c < 71248
                ? (c < 71128
                  ? (c < 71096
                    ? (c >= 71040 && c <= 71093)
                    : c <= 71104)
                  : (c <= 71133 || (c < 71236
                    ? (c >= 71168 && c <= 71232)
                    : c <= 71236)))
                : (c <= 71257 || (c < 71424
                  ? (c < 71360
                    ? (c >= 71296 && c <= 71352)
                    : c <= 71369)
                  : (c <= 71450 || (c >= 71453 && c <= 71467)))))))))))))
      : (c <= 71481 || (c < 119973
        ? (c < 82944
          ? (c < 72784
            ? (c < 72096
              ? (c < 71948
                ? (c < 71840
                  ? (c < 71680
                    ? (c >= 71488 && c <= 71494)
                    : c <= 71738)
                  : (c <= 71913 || (c < 71945
                    ? (c >= 71935 && c <= 71942)
                    : c <= 71945)))
                : (c <= 71955 || (c < 71991
                  ? (c < 71960
                    ? (c >= 71957 && c <= 71958)
                    : c <= 71989)
                  : (c <= 71992 || (c < 72016
                    ? (c >= 71995 && c <= 72003)
                    : c <= 72025)))))
              : (c <= 72103 || (c < 72272
                ? (c < 72163
                  ? (c < 72154
                    ? (c >= 72106 && c <= 72151)
                    : c <= 72161)
                  : (c <= 72164 || (c < 72263
                    ? (c >= 72192 && c <= 72254)
                    : c <= 72263)))
                : (c <= 72345 || (c < 72704
                  ? (c < 72368
                    ? c == 72349
                    : c <= 72440)
                  : (c <= 72712 || (c < 72760
                    ? (c >= 72714 && c <= 72758)
                    : c <= 72768)))))))
            : (c <= 72793 || (c < 73063
              ? (c < 72971
                ? (c < 72873
                  ? (c < 72850
                    ? (c >= 72818 && c <= 72847)
                    : c <= 72871)
                  : (c <= 72886 || (c < 72968
                    ? (c >= 72960 && c <= 72966)
                    : c <= 72969)))
                : (c <= 73014 || (c < 73023
                  ? (c < 73020
                    ? c == 73018
                    : c <= 73021)
                  : (c <= 73031 || (c < 73056
                    ? (c >= 73040 && c <= 73049)
                    : c <= 73061)))))
              : (c <= 73064 || (c < 73648
                ? (c < 73107
                  ? (c < 73104
                    ? (c >= 73066 && c <= 73102)
                    : c <= 73105)
                  : (c <= 73112 || (c < 73440
                    ? (c >= 73120 && c <= 73129)
                    : c <= 73462)))
                : (c <= 73648 || (c < 74880
                  ? (c < 74752
                    ? (c >= 73728 && c <= 74649)
                    : c <= 74862)
                  : (c <= 75075 || (c < 77824
                    ? (c >= 77712 && c <= 77808)
                    : c <= 78894)))))))))
          : (c <= 83526 || (c < 110581
            ? (c < 93053
              ? (c < 92880
                ? (c < 92768
                  ? (c < 92736
                    ? (c >= 92160 && c <= 92728)
                    : c <= 92766)
                  : (c <= 92777 || (c < 92864
                    ? (c >= 92784 && c <= 92862)
                    : c <= 92873)))
                : (c <= 92909 || (c < 92992
                  ? (c < 92928
                    ? (c >= 92912 && c <= 92916)
                    : c <= 92982)
                  : (c <= 92995 || (c < 93027
                    ? (c >= 93008 && c <= 93017)
                    : c <= 93047)))))
              : (c <= 93071 || (c < 94179
                ? (c < 94031
                  ? (c < 93952
                    ? (c >= 93760 && c <= 93823)
                    : c <= 94026)
                  : (c <= 94087 || (c < 94176
                    ? (c >= 94095 && c <= 94111)
                    : c <= 94177)))
                : (c <= 94180 || (c < 100352
                  ? (c < 94208
                    ? (c >= 94192 && c <= 94193)
                    : c <= 100343)
                  : (c <= 101589 || (c < 110576
                    ? (c >= 101632 && c <= 101640)
                    : c <= 110579)))))))
            : (c <= 110587 || (c < 118576
              ? (c < 113664
                ? (c < 110928
                  ? (c < 110592
                    ? (c >= 110589 && c <= 110590)
                    : c <= 110882)
                  : (c <= 110930 || (c < 110960
                    ? (c >= 110948 && c <= 110951)
                    : c <= 111355)))
                : (c <= 113770 || (c < 113808
                  ? (c < 113792
                    ? (c >= 113776 && c <= 113788)
                    : c <= 113800)
                  : (c <= 113817 || (c < 118528
                    ? (c >= 113821 && c <= 113822)
                    : c <= 118573)))))
              : (c <= 118598 || (c < 119362
                ? (c < 119163
                  ? (c < 119149
                    ? (c >= 119141 && c <= 119145)
                    : c <= 119154)
                  : (c <= 119170 || (c < 119210
                    ? (c >= 119173 && c <= 119179)
                    : c <= 119213)))
                : (c <= 119364 || (c < 119966
                  ? (c < 119894
                    ? (c >= 119808 && c <= 119892)
                    : c <= 119964)
                  : (c <= 119967 || c == 119970))))))))))
        : (c <= 119974 || (c < 124912
          ? (c < 120746
            ? (c < 120134
              ? (c < 120071
                ? (c < 119995
                  ? (c < 119982
                    ? (c >= 119977 && c <= 119980)
                    : c <= 119993)
                  : (c <= 119995 || (c < 120005
                    ? (c >= 119997 && c <= 120003)
                    : c <= 120069)))
                : (c <= 120074 || (c < 120094
                  ? (c < 120086
                    ? (c >= 120077 && c <= 120084)
                    : c <= 120092)
                  : (c <= 120121 || (c < 120128
                    ? (c >= 120123 && c <= 120126)
                    : c <= 120132)))))
              : (c <= 120134 || (c < 120572
                ? (c < 120488
                  ? (c < 120146
                    ? (c >= 120138 && c <= 120144)
                    : c <= 120485)
                  : (c <= 120512 || (c < 120540
                    ? (c >= 120514 && c <= 120538)
                    : c <= 120570)))
                : (c <= 120596 || (c < 120656
                  ? (c < 120630
                    ? (c >= 120598 && c <= 120628)
                    : c <= 120654)
                  : (c <= 120686 || (c < 120714
                    ? (c >= 120688 && c <= 120712)
                    : c <= 120744)))))))
            : (c <= 120770 || (c < 122907
              ? (c < 121476
                ? (c < 121344
                  ? (c < 120782
                    ? (c >= 120772 && c <= 120779)
                    : c <= 120831)
                  : (c <= 121398 || (c < 121461
                    ? (c >= 121403 && c <= 121452)
                    : c <= 121461)))
                : (c <= 121476 || (c < 122624
                  ? (c < 121505
                    ? (c >= 121499 && c <= 121503)
                    : c <= 121519)
                  : (c <= 122654 || (c < 122888
                    ? (c >= 122880 && c <= 122886)
                    : c <= 122904)))))
              : (c <= 122913 || (c < 123214
                ? (c < 123136
                  ? (c < 122918
                    ? (c >= 122915 && c <= 122916)
                    : c <= 122922)
                  : (c <= 123180 || (c < 123200
                    ? (c >= 123184 && c <= 123197)
                    : c <= 123209)))
                : (c <= 123214 || (c < 124896
                  ? (c < 123584
                    ? (c >= 123536 && c <= 123566)
                    : c <= 123641)
                  : (c <= 124902 || (c < 124909
                    ? (c >= 124904 && c <= 124907)
                    : c <= 124910)))))))))
          : (c <= 124926 || (c < 126557
            ? (c < 126521
              ? (c < 126469
                ? (c < 125184
                  ? (c < 125136
                    ? (c >= 124928 && c <= 125124)
                    : c <= 125142)
                  : (c <= 125259 || (c < 126464
                    ? (c >= 125264 && c <= 125273)
                    : c <= 126467)))
                : (c <= 126495 || (c < 126503
                  ? (c < 126500
                    ? (c >= 126497 && c <= 126498)
                    : c <= 126500)
                  : (c <= 126503 || (c < 126516
                    ? (c >= 126505 && c <= 126514)
                    : c <= 126519)))))
              : (c <= 126521 || (c < 126541
                ? (c < 126535
                  ? (c < 126530
                    ? c == 126523
                    : c <= 126530)
                  : (c <= 126535 || (c < 126539
                    ? c == 126537
                    : c <= 126539)))
                : (c <= 126543 || (c < 126551
                  ? (c < 126548
                    ? (c >= 126545 && c <= 126546)
                    : c <= 126548)
                  : (c <= 126551 || (c < 126555
                    ? c == 126553
                    : c <= 126555)))))))
            : (c <= 126557 || (c < 126629
              ? (c < 126580
                ? (c < 126564
                  ? (c < 126561
                    ? c == 126559
                    : c <= 126562)
                  : (c <= 126564 || (c < 126572
                    ? (c >= 126567 && c <= 126570)
                    : c <= 126578)))
                : (c <= 126583 || (c < 126592
                  ? (c < 126590
                    ? (c >= 126585 && c <= 126588)
                    : c <= 126590)
                  : (c <= 126601 || (c < 126625
                    ? (c >= 126603 && c <= 126619)
                    : c <= 126627)))))
              : (c <= 126633 || (c < 178208
                ? (c < 131072
                  ? (c < 130032
                    ? (c >= 126635 && c <= 126651)
                    : c <= 130041)
                  : (c <= 173791 || (c < 177984
                    ? (c >= 173824 && c <= 177976)
                    : c <= 178205)))
                : (c <= 183969 || (c < 196608
                  ? (c < 194560
                    ? (c >= 183984 && c <= 191456)
                    : c <= 195101)
                  : (c <= 201546 || (c >= 917760 && c <= 917999)))))))))))))))));
}

static bool ts_lex(TSLexer *lexer, TSStateId state) {
  START_LEXER();
  eof = lexer->eof(lexer);
  switch (state) {
    case 0:
      if (eof) ADVANCE(100);
      if (lookahead == '!') ADVANCE(108);
      if (lookahead == '"') ADVANCE(150);
      if (lookahead == '&') ADVANCE(110);
      if (lookahead == '\'') ADVANCE(149);
      if (lookahead == '(') ADVANCE(119);
      if (lookahead == ')') ADVANCE(120);
      if (lookahead == '*') ADVANCE(106);
      if (lookahead == '+') ADVANCE(116);
      if (lookahead == ',') ADVANCE(102);
      if (lookahead == '-') ADVANCE(117);
      if (lookahead == '.') ADVANCE(139);
      if (lookahead == '/') ADVANCE(118);
      if (lookahead == '0') ADVANCE(121);
      if (lookahead == '<') ADVANCE(114);
      if (lookahead == '=') ADVANCE(11);
      if (lookahead == '>') ADVANCE(113);
      if (lookahead == 'S') ADVANCE(170);
      if (lookahead == 'T') ADVANCE(175);
      if (lookahead == '[') ADVANCE(104);
      if (lookahead == '\\') SKIP(96)
      if (lookahead == ']') ADVANCE(107);
      if (lookahead == '_') ADVANCE(208);
      if (lookahead == 'a') ADVANCE(185);
      if (lookahead == 'f') ADVANCE(179);
      if (lookahead == 'g') ADVANCE(196);
      if (lookahead == 'n') ADVANCE(204);
      if (lookahead == 's') ADVANCE(201);
      if (lookahead == 't') ADVANCE(207);
      if (lookahead == '{') ADVANCE(101);
      if (lookahead == '|') ADVANCE(109);
      if (lookahead == '}') ADVANCE(103);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(0)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(122);
      if (sym_name_character_set_1(lookahead)) ADVANCE(209);
      END_STATE();
    case 1:
      if (lookahead == '\n') SKIP(5)
      END_STATE();
    case 2:
      if (lookahead == '\n') SKIP(5)
      if (lookahead == '\r') SKIP(1)
      END_STATE();
    case 3:
      if (lookahead == '\n') SKIP(6)
      END_STATE();
    case 4:
      if (lookahead == '\n') SKIP(6)
      if (lookahead == '\r') SKIP(3)
      END_STATE();
    case 5:
      if (lookahead == '!') ADVANCE(108);
      if (lookahead == '"') ADVANCE(150);
      if (lookahead == '&') ADVANCE(110);
      if (lookahead == '\'') ADVANCE(149);
      if (lookahead == '(') ADVANCE(119);
      if (lookahead == ')') ADVANCE(120);
      if (lookahead == '*') ADVANCE(106);
      if (lookahead == '+') ADVANCE(116);
      if (lookahead == ',') ADVANCE(102);
      if (lookahead == '-') ADVANCE(117);
      if (lookahead == '.') ADVANCE(138);
      if (lookahead == '/') ADVANCE(118);
      if (lookahead == '0') ADVANCE(121);
      if (lookahead == '<') ADVANCE(114);
      if (lookahead == '=') ADVANCE(11);
      if (lookahead == '>') ADVANCE(113);
      if (lookahead == '[') ADVANCE(104);
      if (lookahead == '\\') SKIP(2)
      if (lookahead == ']') ADVANCE(107);
      if (lookahead == '{') ADVANCE(101);
      if (lookahead == '|') ADVANCE(109);
      if (lookahead == '}') ADVANCE(103);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(5)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(122);
      if (sym_name_character_set_2(lookahead)) ADVANCE(209);
      END_STATE();
    case 6:
      if (lookahead == '*') ADVANCE(106);
      if (lookahead == '.') ADVANCE(10);
      if (lookahead == '/') ADVANCE(7);
      if (lookahead == '0') ADVANCE(210);
      if (lookahead == '\\') SKIP(4)
      if (lookahead == ']') ADVANCE(107);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(6)
      if (('1' <= lookahead && lookahead <= '9') ||
          lookahead == '_') ADVANCE(211);
      END_STATE();
    case 7:
      if (lookahead == '*') ADVANCE(9);
      if (lookahead == '/') ADVANCE(135);
      END_STATE();
    case 8:
      if (lookahead == '*') ADVANCE(8);
      if (lookahead == '/') ADVANCE(133);
      if (lookahead != 0) ADVANCE(9);
      END_STATE();
    case 9:
      if (lookahead == '*') ADVANCE(8);
      if (lookahead != 0) ADVANCE(9);
      END_STATE();
    case 10:
      if (lookahead == '.') ADVANCE(105);
      END_STATE();
    case 11:
      if (lookahead == '=') ADVANCE(115);
      if (lookahead == '>') ADVANCE(111);
      END_STATE();
    case 12:
      if (lookahead == '>') ADVANCE(112);
      END_STATE();
    case 13:
      if (lookahead == 'a') ADVANCE(65);
      END_STATE();
    case 14:
      if (lookahead == 'a') ADVANCE(47);
      END_STATE();
    case 15:
      if (lookahead == 'a') ADVANCE(36);
      END_STATE();
    case 16:
      if (lookahead == 'a') ADVANCE(48);
      END_STATE();
    case 17:
      if (lookahead == 'a') ADVANCE(38);
      END_STATE();
    case 18:
      if (lookahead == 'a') ADVANCE(41);
      END_STATE();
    case 19:
      if (lookahead == 'a') ADVANCE(69);
      END_STATE();
    case 20:
      if (lookahead == 'c') ADVANCE(61);
      END_STATE();
    case 21:
      if (lookahead == 'c') ADVANCE(13);
      END_STATE();
    case 22:
      if (lookahead == 'c') ADVANCE(81);
      END_STATE();
    case 23:
      if (lookahead == 'c') ADVANCE(63);
      END_STATE();
    case 24:
      if (lookahead == 'c') ADVANCE(64);
      END_STATE();
    case 25:
      if (lookahead == 'c') ADVANCE(19);
      END_STATE();
    case 26:
      if (lookahead == 'd') ADVANCE(35);
      END_STATE();
    case 27:
      if (lookahead == 'd') ADVANCE(42);
      END_STATE();
    case 28:
      if (lookahead == 'e') ADVANCE(86);
      END_STATE();
    case 29:
      if (lookahead == 'e') ADVANCE(44);
      END_STATE();
    case 30:
      if (lookahead == 'e') ADVANCE(45);
      END_STATE();
    case 31:
      if (lookahead == 'e') ADVANCE(46);
      END_STATE();
    case 32:
      if (lookahead == 'e') ADVANCE(87);
      END_STATE();
    case 33:
      if (lookahead == 'e') ADVANCE(88);
      END_STATE();
    case 34:
      if (lookahead == 'f') ADVANCE(85);
      END_STATE();
    case 35:
      if (lookahead == 'i') ADVANCE(54);
      END_STATE();
    case 36:
      if (lookahead == 'i') ADVANCE(55);
      END_STATE();
    case 37:
      if (lookahead == 'i') ADVANCE(76);
      END_STATE();
    case 38:
      if (lookahead == 'i') ADVANCE(56);
      END_STATE();
    case 39:
      if (lookahead == 'i') ADVANCE(79);
      END_STATE();
    case 40:
      if (lookahead == 'i') ADVANCE(62);
      END_STATE();
    case 41:
      if (lookahead == 'i') ADVANCE(57);
      END_STATE();
    case 42:
      if (lookahead == 'i') ADVANCE(58);
      END_STATE();
    case 43:
      if (lookahead == 'l') ADVANCE(28);
      END_STATE();
    case 44:
      if (lookahead == 'l') ADVANCE(141);
      END_STATE();
    case 45:
      if (lookahead == 'l') ADVANCE(140);
      END_STATE();
    case 46:
      if (lookahead == 'l') ADVANCE(142);
      END_STATE();
    case 47:
      if (lookahead == 'l') ADVANCE(37);
      END_STATE();
    case 48:
      if (lookahead == 'l') ADVANCE(39);
      END_STATE();
    case 49:
      if (lookahead == 'l') ADVANCE(32);
      END_STATE();
    case 50:
      if (lookahead == 'l') ADVANCE(33);
      END_STATE();
    case 51:
      if (lookahead == 'n') ADVANCE(70);
      END_STATE();
    case 52:
      if (lookahead == 'n') ADVANCE(145);
      END_STATE();
    case 53:
      if (lookahead == 'n') ADVANCE(22);
      END_STATE();
    case 54:
      if (lookahead == 'n') ADVANCE(14);
      END_STATE();
    case 55:
      if (lookahead == 'n') ADVANCE(78);
      END_STATE();
    case 56:
      if (lookahead == 'n') ADVANCE(80);
      END_STATE();
    case 57:
      if (lookahead == 'n') ADVANCE(82);
      END_STATE();
    case 58:
      if (lookahead == 'n') ADVANCE(16);
      END_STATE();
    case 59:
      if (lookahead == 'n') ADVANCE(74);
      END_STATE();
    case 60:
      if (lookahead == 'n') ADVANCE(75);
      END_STATE();
    case 61:
      if (lookahead == 'o') ADVANCE(51);
      END_STATE();
    case 62:
      if (lookahead == 'o') ADVANCE(52);
      END_STATE();
    case 63:
      if (lookahead == 'o') ADVANCE(59);
      END_STATE();
    case 64:
      if (lookahead == 'o') ADVANCE(60);
      END_STATE();
    case 65:
      if (lookahead == 'r') ADVANCE(26);
      END_STATE();
    case 66:
      if (lookahead == 'r') ADVANCE(15);
      END_STATE();
    case 67:
      if (lookahead == 'r') ADVANCE(17);
      END_STATE();
    case 68:
      if (lookahead == 'r') ADVANCE(18);
      END_STATE();
    case 69:
      if (lookahead == 'r') ADVANCE(27);
      END_STATE();
    case 70:
      if (lookahead == 's') ADVANCE(77);
      END_STATE();
    case 71:
      if (lookahead == 's') ADVANCE(146);
      END_STATE();
    case 72:
      if (lookahead == 's') ADVANCE(147);
      END_STATE();
    case 73:
      if (lookahead == 's') ADVANCE(148);
      END_STATE();
    case 74:
      if (lookahead == 's') ADVANCE(83);
      END_STATE();
    case 75:
      if (lookahead == 's') ADVANCE(84);
      END_STATE();
    case 76:
      if (lookahead == 't') ADVANCE(89);
      END_STATE();
    case 77:
      if (lookahead == 't') ADVANCE(66);
      END_STATE();
    case 78:
      if (lookahead == 't') ADVANCE(71);
      END_STATE();
    case 79:
      if (lookahead == 't') ADVANCE(90);
      END_STATE();
    case 80:
      if (lookahead == 't') ADVANCE(72);
      END_STATE();
    case 81:
      if (lookahead == 't') ADVANCE(40);
      END_STATE();
    case 82:
      if (lookahead == 't') ADVANCE(73);
      END_STATE();
    case 83:
      if (lookahead == 't') ADVANCE(67);
      END_STATE();
    case 84:
      if (lookahead == 't') ADVANCE(68);
      END_STATE();
    case 85:
      if (lookahead == 'u') ADVANCE(53);
      END_STATE();
    case 86:
      if (lookahead == 'v') ADVANCE(29);
      END_STATE();
    case 87:
      if (lookahead == 'v') ADVANCE(30);
      END_STATE();
    case 88:
      if (lookahead == 'v') ADVANCE(31);
      END_STATE();
    case 89:
      if (lookahead == 'y') ADVANCE(143);
      END_STATE();
    case 90:
      if (lookahead == 'y') ADVANCE(144);
      END_STATE();
    case 91:
      if (lookahead == '+' ||
          lookahead == '-') ADVANCE(92);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(132);
      END_STATE();
    case 92:
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(132);
      END_STATE();
    case 93:
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(125);
      END_STATE();
    case 94:
      if (lookahead != 0 &&
          lookahead != '\r') ADVANCE(135);
      if (lookahead == '\r') ADVANCE(137);
      END_STATE();
    case 95:
      if (eof) ADVANCE(100);
      if (lookahead == '\n') SKIP(0)
      END_STATE();
    case 96:
      if (eof) ADVANCE(100);
      if (lookahead == '\n') SKIP(0)
      if (lookahead == '\r') SKIP(95)
      END_STATE();
    case 97:
      if (eof) ADVANCE(100);
      if (lookahead == '\n') SKIP(99)
      END_STATE();
    case 98:
      if (eof) ADVANCE(100);
      if (lookahead == '\n') SKIP(99)
      if (lookahead == '\r') SKIP(97)
      END_STATE();
    case 99:
      if (eof) ADVANCE(100);
      if (lookahead == '!') ADVANCE(108);
      if (lookahead == '"') ADVANCE(150);
      if (lookahead == '&') ADVANCE(110);
      if (lookahead == '\'') ADVANCE(149);
      if (lookahead == '(') ADVANCE(119);
      if (lookahead == ')') ADVANCE(120);
      if (lookahead == '*') ADVANCE(106);
      if (lookahead == '+') ADVANCE(116);
      if (lookahead == ',') ADVANCE(102);
      if (lookahead == '-') ADVANCE(117);
      if (lookahead == '.') ADVANCE(138);
      if (lookahead == '/') ADVANCE(118);
      if (lookahead == '0') ADVANCE(121);
      if (lookahead == '<') ADVANCE(114);
      if (lookahead == '=') ADVANCE(11);
      if (lookahead == '>') ADVANCE(113);
      if (lookahead == 'S') ADVANCE(170);
      if (lookahead == 'T') ADVANCE(175);
      if (lookahead == '[') ADVANCE(104);
      if (lookahead == '\\') SKIP(98)
      if (lookahead == ']') ADVANCE(107);
      if (lookahead == 'a') ADVANCE(185);
      if (lookahead == 'f') ADVANCE(179);
      if (lookahead == 'g') ADVANCE(196);
      if (lookahead == 'n') ADVANCE(204);
      if (lookahead == 's') ADVANCE(201);
      if (lookahead == 't') ADVANCE(207);
      if (lookahead == '{') ADVANCE(101);
      if (lookahead == '|') ADVANCE(109);
      if (lookahead == '}') ADVANCE(103);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(99)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(122);
      if (sym_name_character_set_3(lookahead)) ADVANCE(209);
      END_STATE();
    case 100:
      ACCEPT_TOKEN(ts_builtin_sym_end);
      END_STATE();
    case 101:
      ACCEPT_TOKEN(anon_sym_LBRACE);
      END_STATE();
    case 102:
      ACCEPT_TOKEN(anon_sym_COMMA);
      END_STATE();
    case 103:
      ACCEPT_TOKEN(anon_sym_RBRACE);
      END_STATE();
    case 104:
      ACCEPT_TOKEN(anon_sym_LBRACK);
      END_STATE();
    case 105:
      ACCEPT_TOKEN(anon_sym_DOT_DOT);
      END_STATE();
    case 106:
      ACCEPT_TOKEN(anon_sym_STAR);
      END_STATE();
    case 107:
      ACCEPT_TOKEN(anon_sym_RBRACK);
      END_STATE();
    case 108:
      ACCEPT_TOKEN(anon_sym_BANG);
      END_STATE();
    case 109:
      ACCEPT_TOKEN(anon_sym_PIPE);
      END_STATE();
    case 110:
      ACCEPT_TOKEN(anon_sym_AMP);
      END_STATE();
    case 111:
      ACCEPT_TOKEN(anon_sym_EQ_GT);
      END_STATE();
    case 112:
      ACCEPT_TOKEN(anon_sym_LT_EQ_GT);
      END_STATE();
    case 113:
      ACCEPT_TOKEN(anon_sym_GT);
      END_STATE();
    case 114:
      ACCEPT_TOKEN(anon_sym_LT);
      if (lookahead == '=') ADVANCE(12);
      END_STATE();
    case 115:
      ACCEPT_TOKEN(anon_sym_EQ_EQ);
      END_STATE();
    case 116:
      ACCEPT_TOKEN(anon_sym_PLUS);
      END_STATE();
    case 117:
      ACCEPT_TOKEN(anon_sym_DASH);
      END_STATE();
    case 118:
      ACCEPT_TOKEN(anon_sym_SLASH);
      if (lookahead == '*') ADVANCE(9);
      if (lookahead == '/') ADVANCE(135);
      END_STATE();
    case 119:
      ACCEPT_TOKEN(anon_sym_LPAREN);
      END_STATE();
    case 120:
      ACCEPT_TOKEN(anon_sym_RPAREN);
      END_STATE();
    case 121:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(130);
      if (lookahead == '_') ADVANCE(122);
      if (lookahead == 'X' ||
          lookahead == 'x') ADVANCE(93);
      if (lookahead == 'E' ||
          lookahead == 'P' ||
          lookahead == 'e' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(122);
      END_STATE();
    case 122:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(130);
      if (lookahead == '_') ADVANCE(122);
      if (lookahead == 'E' ||
          lookahead == 'P' ||
          lookahead == 'e' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(122);
      END_STATE();
    case 123:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(128);
      if (lookahead == '_') ADVANCE(125);
      if (lookahead == '+' ||
          lookahead == '-') ADVANCE(92);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(123);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(91);
      if (('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(125);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(124);
      END_STATE();
    case 124:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(128);
      if (lookahead == '_') ADVANCE(125);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(123);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(91);
      if (('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(125);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(124);
      END_STATE();
    case 125:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(128);
      if (lookahead == '_') ADVANCE(125);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(123);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(125);
      END_STATE();
    case 126:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '+' ||
          lookahead == '-') ADVANCE(92);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(126);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(127);
      if (('A' <= lookahead && lookahead <= 'F') ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(129);
      END_STATE();
    case 127:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(126);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(127);
      if (('A' <= lookahead && lookahead <= 'F') ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(129);
      END_STATE();
    case 128:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(126);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(129);
      END_STATE();
    case 129:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(126);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(129);
      END_STATE();
    case 130:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'P' ||
          lookahead == 'e' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(131);
      END_STATE();
    case 131:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'P' ||
          lookahead == 'e' ||
          lookahead == 'p') ADVANCE(91);
      if (('0' <= lookahead && lookahead <= '9') ||
          lookahead == '_') ADVANCE(131);
      END_STATE();
    case 132:
      ACCEPT_TOKEN(sym_number);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(132);
      END_STATE();
    case 133:
      ACCEPT_TOKEN(sym_comment);
      END_STATE();
    case 134:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead == '"') ADVANCE(135);
      if (lookahead == '\\') ADVANCE(94);
      if (lookahead != 0 &&
          lookahead != '\n') ADVANCE(134);
      END_STATE();
    case 135:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead == '\\') ADVANCE(94);
      if (lookahead != 0 &&
          lookahead != '\n') ADVANCE(135);
      END_STATE();
    case 136:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '"' &&
          lookahead != '\\') ADVANCE(155);
      END_STATE();
    case 137:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead != 0 &&
          lookahead != '\\') ADVANCE(135);
      if (lookahead == '\\') ADVANCE(94);
      END_STATE();
    case 138:
      ACCEPT_TOKEN(anon_sym_DOT);
      END_STATE();
    case 139:
      ACCEPT_TOKEN(anon_sym_DOT);
      if (lookahead == '.') ADVANCE(105);
      END_STATE();
    case 140:
      ACCEPT_TOKEN(anon_sym_SMT_DASHlevel);
      END_STATE();
    case 141:
      ACCEPT_TOKEN(anon_sym_SAT_DASHlevel);
      END_STATE();
    case 142:
      ACCEPT_TOKEN(anon_sym_TYPE_DASHlevel);
      END_STATE();
    case 143:
      ACCEPT_TOKEN(anon_sym_group_DASHcardinality);
      END_STATE();
    case 144:
      ACCEPT_TOKEN(anon_sym_feature_DASHcardinality);
      END_STATE();
    case 145:
      ACCEPT_TOKEN(anon_sym_aggregate_DASHfunction);
      END_STATE();
    case 146:
      ACCEPT_TOKEN(anon_sym_type_DASHconstraints);
      END_STATE();
    case 147:
      ACCEPT_TOKEN(anon_sym_string_DASHconstraints);
      END_STATE();
    case 148:
      ACCEPT_TOKEN(anon_sym_numeric_DASHconstraints);
      END_STATE();
    case 149:
      ACCEPT_TOKEN(anon_sym_SQUOTE);
      END_STATE();
    case 150:
      ACCEPT_TOKEN(anon_sym_DQUOTE);
      END_STATE();
    case 151:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead == '*') ADVANCE(153);
      if (lookahead == '/') ADVANCE(134);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '"' &&
          lookahead != '\\') ADVANCE(155);
      END_STATE();
    case 152:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead == '*') ADVANCE(152);
      if (lookahead == '/') ADVANCE(136);
      if (lookahead == '\n' ||
          lookahead == '"' ||
          lookahead == '\\') ADVANCE(9);
      if (lookahead != 0) ADVANCE(153);
      END_STATE();
    case 153:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead == '*') ADVANCE(152);
      if (lookahead == '\n' ||
          lookahead == '"' ||
          lookahead == '\\') ADVANCE(9);
      if (lookahead != 0) ADVANCE(153);
      END_STATE();
    case 154:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead == '/') ADVANCE(151);
      if (lookahead == '\t' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) ADVANCE(154);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '"' &&
          lookahead != '\\') ADVANCE(155);
      END_STATE();
    case 155:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '"' &&
          lookahead != '\\') ADVANCE(155);
      END_STATE();
    case 156:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead == '*') ADVANCE(158);
      if (lookahead == '/') ADVANCE(160);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(160);
      END_STATE();
    case 157:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead == '*') ADVANCE(157);
      if (lookahead == '/') ADVANCE(160);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(158);
      END_STATE();
    case 158:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead == '*') ADVANCE(157);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(158);
      END_STATE();
    case 159:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead == '/') ADVANCE(156);
      if (lookahead == '\t' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) ADVANCE(159);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(160);
      END_STATE();
    case 160:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(160);
      END_STATE();
    case 161:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(43);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 162:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(20);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 163:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(34);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 164:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(21);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 165:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(49);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 166:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(50);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 167:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(23);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 168:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(25);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 169:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(24);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 170:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'A') ADVANCE(173);
      if (lookahead == 'M') ADVANCE(174);
      if (sym_name_character_set_5(lookahead)) ADVANCE(209);
      END_STATE();
    case 171:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'E') ADVANCE(166);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 172:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'P') ADVANCE(171);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 173:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'T') ADVANCE(161);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 174:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'T') ADVANCE(165);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 175:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'Y') ADVANCE(172);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 176:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'a') ADVANCE(202);
      if (sym_name_character_set_6(lookahead)) ADVANCE(209);
      END_STATE();
    case 177:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'a') ADVANCE(203);
      if (sym_name_character_set_6(lookahead)) ADVANCE(209);
      END_STATE();
    case 178:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'c') ADVANCE(169);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 179:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(176);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 180:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(162);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 181:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(187);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 182:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(198);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 183:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(163);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 184:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(168);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 185:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'g') ADVANCE(186);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 186:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'g') ADVANCE(199);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 187:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'g') ADVANCE(177);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 188:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'g') ADVANCE(167);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 189:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'i') ADVANCE(192);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 190:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'i') ADVANCE(178);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 191:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'm') ADVANCE(182);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 192:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'n') ADVANCE(188);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 193:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'o') ADVANCE(205);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 194:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'p') ADVANCE(180);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 195:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'p') ADVANCE(164);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 196:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'r') ADVANCE(193);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 197:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'r') ADVANCE(189);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 198:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'r') ADVANCE(190);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 199:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'r') ADVANCE(181);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 200:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'r') ADVANCE(184);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 201:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 't') ADVANCE(197);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 202:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 't') ADVANCE(206);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 203:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 't') ADVANCE(183);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 204:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'u') ADVANCE(191);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 205:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'u') ADVANCE(195);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 206:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'u') ADVANCE(200);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 207:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'y') ADVANCE(194);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 208:
      ACCEPT_TOKEN(sym_name);
      if (('0' <= lookahead && lookahead <= '9') ||
          lookahead == '_') ADVANCE(208);
      if (sym_name_character_set_7(lookahead)) ADVANCE(209);
      END_STATE();
    case 209:
      ACCEPT_TOKEN(sym_name);
      if (sym_name_character_set_4(lookahead)) ADVANCE(209);
      END_STATE();
    case 210:
      ACCEPT_TOKEN(sym_int);
      END_STATE();
    case 211:
      ACCEPT_TOKEN(sym_int);
      if (('0' <= lookahead && lookahead <= '9') ||
          lookahead == '_') ADVANCE(211);
      END_STATE();
    default:
      return false;
  }
}

static bool ts_lex_keywords(TSLexer *lexer, TSStateId state) {
  START_LEXER();
  eof = lexer->eof(lexer);
  switch (state) {
    case 0:
      if (lookahead == 'B') ADVANCE(1);
      if (lookahead == 'I') ADVANCE(2);
      if (lookahead == 'R') ADVANCE(3);
      if (lookahead == 'S') ADVANCE(4);
      if (lookahead == '\\') SKIP(5)
      if (lookahead == 'a') ADVANCE(6);
      if (lookahead == 'c') ADVANCE(7);
      if (lookahead == 'f') ADVANCE(8);
      if (lookahead == 'i') ADVANCE(9);
      if (lookahead == 'm') ADVANCE(10);
      if (lookahead == 'n') ADVANCE(11);
      if (lookahead == 'o') ADVANCE(12);
      if (lookahead == 't') ADVANCE(13);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(0)
      END_STATE();
    case 1:
      if (lookahead == 'o') ADVANCE(14);
      END_STATE();
    case 2:
      if (lookahead == 'n') ADVANCE(15);
      END_STATE();
    case 3:
      if (lookahead == 'e') ADVANCE(16);
      END_STATE();
    case 4:
      if (lookahead == 't') ADVANCE(17);
      END_STATE();
    case 5:
      if (lookahead == '\n') SKIP(0)
      if (lookahead == '\r') SKIP(18)
      END_STATE();
    case 6:
      if (lookahead == 'l') ADVANCE(19);
      if (lookahead == 's') ADVANCE(20);
      END_STATE();
    case 7:
      if (lookahead == 'a') ADVANCE(21);
      if (lookahead == 'o') ADVANCE(22);
      END_STATE();
    case 8:
      if (lookahead == 'a') ADVANCE(23);
      if (lookahead == 'e') ADVANCE(24);
      END_STATE();
    case 9:
      if (lookahead == 'm') ADVANCE(25);
      if (lookahead == 'n') ADVANCE(26);
      END_STATE();
    case 10:
      if (lookahead == 'a') ADVANCE(27);
      END_STATE();
    case 11:
      if (lookahead == 'a') ADVANCE(28);
      END_STATE();
    case 12:
      if (lookahead == 'p') ADVANCE(29);
      if (lookahead == 'r') ADVANCE(30);
      END_STATE();
    case 13:
      if (lookahead == 'r') ADVANCE(31);
      END_STATE();
    case 14:
      if (lookahead == 'o') ADVANCE(32);
      END_STATE();
    case 15:
      if (lookahead == 't') ADVANCE(33);
      END_STATE();
    case 16:
      if (lookahead == 'a') ADVANCE(34);
      END_STATE();
    case 17:
      if (lookahead == 'r') ADVANCE(35);
      END_STATE();
    case 18:
      if (lookahead == '\n') SKIP(0)
      END_STATE();
    case 19:
      if (lookahead == 't') ADVANCE(36);
      END_STATE();
    case 20:
      ACCEPT_TOKEN(anon_sym_as);
      END_STATE();
    case 21:
      if (lookahead == 'r') ADVANCE(37);
      END_STATE();
    case 22:
      if (lookahead == 'n') ADVANCE(38);
      END_STATE();
    case 23:
      if (lookahead == 'l') ADVANCE(39);
      END_STATE();
    case 24:
      if (lookahead == 'a') ADVANCE(40);
      END_STATE();
    case 25:
      if (lookahead == 'p') ADVANCE(41);
      END_STATE();
    case 26:
      if (lookahead == 'c') ADVANCE(42);
      END_STATE();
    case 27:
      if (lookahead == 'n') ADVANCE(43);
      END_STATE();
    case 28:
      if (lookahead == 'm') ADVANCE(44);
      END_STATE();
    case 29:
      if (lookahead == 't') ADVANCE(45);
      END_STATE();
    case 30:
      ACCEPT_TOKEN(anon_sym_or);
      END_STATE();
    case 31:
      if (lookahead == 'u') ADVANCE(46);
      END_STATE();
    case 32:
      if (lookahead == 'l') ADVANCE(47);
      END_STATE();
    case 33:
      if (lookahead == 'e') ADVANCE(48);
      END_STATE();
    case 34:
      if (lookahead == 'l') ADVANCE(49);
      END_STATE();
    case 35:
      if (lookahead == 'i') ADVANCE(50);
      END_STATE();
    case 36:
      if (lookahead == 'e') ADVANCE(51);
      END_STATE();
    case 37:
      if (lookahead == 'd') ADVANCE(52);
      END_STATE();
    case 38:
      if (lookahead == 's') ADVANCE(53);
      END_STATE();
    case 39:
      if (lookahead == 's') ADVANCE(54);
      END_STATE();
    case 40:
      if (lookahead == 't') ADVANCE(55);
      END_STATE();
    case 41:
      if (lookahead == 'o') ADVANCE(56);
      END_STATE();
    case 42:
      if (lookahead == 'l') ADVANCE(57);
      END_STATE();
    case 43:
      if (lookahead == 'd') ADVANCE(58);
      END_STATE();
    case 44:
      if (lookahead == 'e') ADVANCE(59);
      END_STATE();
    case 45:
      if (lookahead == 'i') ADVANCE(60);
      END_STATE();
    case 46:
      if (lookahead == 'e') ADVANCE(61);
      END_STATE();
    case 47:
      if (lookahead == 'e') ADVANCE(62);
      END_STATE();
    case 48:
      if (lookahead == 'g') ADVANCE(63);
      END_STATE();
    case 49:
      ACCEPT_TOKEN(anon_sym_Real);
      END_STATE();
    case 50:
      if (lookahead == 'n') ADVANCE(64);
      END_STATE();
    case 51:
      if (lookahead == 'r') ADVANCE(65);
      END_STATE();
    case 52:
      if (lookahead == 'i') ADVANCE(66);
      END_STATE();
    case 53:
      if (lookahead == 't') ADVANCE(67);
      END_STATE();
    case 54:
      if (lookahead == 'e') ADVANCE(68);
      END_STATE();
    case 55:
      if (lookahead == 'u') ADVANCE(69);
      END_STATE();
    case 56:
      if (lookahead == 'r') ADVANCE(70);
      END_STATE();
    case 57:
      if (lookahead == 'u') ADVANCE(71);
      END_STATE();
    case 58:
      if (lookahead == 'a') ADVANCE(72);
      END_STATE();
    case 59:
      if (lookahead == 's') ADVANCE(73);
      END_STATE();
    case 60:
      if (lookahead == 'o') ADVANCE(74);
      END_STATE();
    case 61:
      ACCEPT_TOKEN(anon_sym_true);
      END_STATE();
    case 62:
      if (lookahead == 'a') ADVANCE(75);
      END_STATE();
    case 63:
      if (lookahead == 'e') ADVANCE(76);
      END_STATE();
    case 64:
      if (lookahead == 'g') ADVANCE(77);
      END_STATE();
    case 65:
      if (lookahead == 'n') ADVANCE(78);
      END_STATE();
    case 66:
      if (lookahead == 'n') ADVANCE(79);
      END_STATE();
    case 67:
      if (lookahead == 'r') ADVANCE(80);
      END_STATE();
    case 68:
      ACCEPT_TOKEN(anon_sym_false);
      END_STATE();
    case 69:
      if (lookahead == 'r') ADVANCE(81);
      END_STATE();
    case 70:
      if (lookahead == 't') ADVANCE(82);
      END_STATE();
    case 71:
      if (lookahead == 'd') ADVANCE(83);
      END_STATE();
    case 72:
      if (lookahead == 't') ADVANCE(84);
      END_STATE();
    case 73:
      if (lookahead == 'p') ADVANCE(85);
      END_STATE();
    case 74:
      if (lookahead == 'n') ADVANCE(86);
      END_STATE();
    case 75:
      if (lookahead == 'n') ADVANCE(87);
      END_STATE();
    case 76:
      if (lookahead == 'r') ADVANCE(88);
      END_STATE();
    case 77:
      ACCEPT_TOKEN(anon_sym_String);
      END_STATE();
    case 78:
      if (lookahead == 'a') ADVANCE(89);
      END_STATE();
    case 79:
      if (lookahead == 'a') ADVANCE(90);
      END_STATE();
    case 80:
      if (lookahead == 'a') ADVANCE(91);
      END_STATE();
    case 81:
      if (lookahead == 'e') ADVANCE(92);
      END_STATE();
    case 82:
      if (lookahead == 's') ADVANCE(93);
      END_STATE();
    case 83:
      if (lookahead == 'e') ADVANCE(94);
      END_STATE();
    case 84:
      if (lookahead == 'o') ADVANCE(95);
      END_STATE();
    case 85:
      if (lookahead == 'a') ADVANCE(96);
      END_STATE();
    case 86:
      if (lookahead == 'a') ADVANCE(97);
      END_STATE();
    case 87:
      ACCEPT_TOKEN(anon_sym_Boolean);
      END_STATE();
    case 88:
      ACCEPT_TOKEN(anon_sym_Integer);
      END_STATE();
    case 89:
      if (lookahead == 't') ADVANCE(98);
      END_STATE();
    case 90:
      if (lookahead == 'l') ADVANCE(99);
      END_STATE();
    case 91:
      if (lookahead == 'i') ADVANCE(100);
      END_STATE();
    case 92:
      if (lookahead == 's') ADVANCE(101);
      END_STATE();
    case 93:
      ACCEPT_TOKEN(sym_imports);
      END_STATE();
    case 94:
      ACCEPT_TOKEN(sym_include);
      END_STATE();
    case 95:
      if (lookahead == 'r') ADVANCE(102);
      END_STATE();
    case 96:
      if (lookahead == 'c') ADVANCE(103);
      END_STATE();
    case 97:
      if (lookahead == 'l') ADVANCE(104);
      END_STATE();
    case 98:
      if (lookahead == 'i') ADVANCE(105);
      END_STATE();
    case 99:
      if (lookahead == 'i') ADVANCE(106);
      END_STATE();
    case 100:
      if (lookahead == 'n') ADVANCE(107);
      END_STATE();
    case 101:
      ACCEPT_TOKEN(sym_features);
      END_STATE();
    case 102:
      if (lookahead == 'y') ADVANCE(108);
      END_STATE();
    case 103:
      if (lookahead == 'e') ADVANCE(109);
      END_STATE();
    case 104:
      ACCEPT_TOKEN(anon_sym_optional);
      END_STATE();
    case 105:
      if (lookahead == 'v') ADVANCE(110);
      END_STATE();
    case 106:
      if (lookahead == 't') ADVANCE(111);
      END_STATE();
    case 107:
      if (lookahead == 't') ADVANCE(112);
      END_STATE();
    case 108:
      ACCEPT_TOKEN(anon_sym_mandatory);
      END_STATE();
    case 109:
      ACCEPT_TOKEN(anon_sym_namespace);
      END_STATE();
    case 110:
      if (lookahead == 'e') ADVANCE(113);
      END_STATE();
    case 111:
      if (lookahead == 'y') ADVANCE(114);
      END_STATE();
    case 112:
      ACCEPT_TOKEN(anon_sym_constraint);
      if (lookahead == 's') ADVANCE(115);
      END_STATE();
    case 113:
      ACCEPT_TOKEN(anon_sym_alternative);
      END_STATE();
    case 114:
      ACCEPT_TOKEN(anon_sym_cardinality);
      END_STATE();
    case 115:
      ACCEPT_TOKEN(anon_sym_constraints);
      END_STATE();
    default:
      return false;
  }
}

static const TSLexMode ts_lex_modes[STATE_COUNT] = {
  [0] = {.lex_state = 0, .external_lex_state = 1},
  [1] = {.lex_state = 99, .external_lex_state = 2},
  [2] = {.lex_state = 99, .external_lex_state = 2},
  [3] = {.lex_state = 99, .external_lex_state = 3},
  [4] = {.lex_state = 99, .external_lex_state = 3},
  [5] = {.lex_state = 99, .external_lex_state = 3},
  [6] = {.lex_state = 99, .external_lex_state = 3},
  [7] = {.lex_state = 99, .external_lex_state = 3},
  [8] = {.lex_state = 99, .external_lex_state = 3},
  [9] = {.lex_state = 99, .external_lex_state = 3},
  [10] = {.lex_state = 99, .external_lex_state = 2},
  [11] = {.lex_state = 99, .external_lex_state = 3},
  [12] = {.lex_state = 99, .external_lex_state = 3},
  [13] = {.lex_state = 99, .external_lex_state = 3},
  [14] = {.lex_state = 99, .external_lex_state = 3},
  [15] = {.lex_state = 99, .external_lex_state = 3},
  [16] = {.lex_state = 99, .external_lex_state = 3},
  [17] = {.lex_state = 99, .external_lex_state = 3},
  [18] = {.lex_state = 99, .external_lex_state = 3},
  [19] = {.lex_state = 99, .external_lex_state = 3},
  [20] = {.lex_state = 99, .external_lex_state = 3},
  [21] = {.lex_state = 99, .external_lex_state = 4},
  [22] = {.lex_state = 99, .external_lex_state = 4},
  [23] = {.lex_state = 99, .external_lex_state = 4},
  [24] = {.lex_state = 99, .external_lex_state = 4},
  [25] = {.lex_state = 99, .external_lex_state = 5},
  [26] = {.lex_state = 99, .external_lex_state = 4},
  [27] = {.lex_state = 99, .external_lex_state = 5},
  [28] = {.lex_state = 99, .external_lex_state = 5},
  [29] = {.lex_state = 99, .external_lex_state = 4},
  [30] = {.lex_state = 99, .external_lex_state = 5},
  [31] = {.lex_state = 99, .external_lex_state = 4},
  [32] = {.lex_state = 99, .external_lex_state = 4},
  [33] = {.lex_state = 99, .external_lex_state = 5},
  [34] = {.lex_state = 99, .external_lex_state = 6},
  [35] = {.lex_state = 99, .external_lex_state = 5},
  [36] = {.lex_state = 99, .external_lex_state = 4},
  [37] = {.lex_state = 99, .external_lex_state = 5},
  [38] = {.lex_state = 99, .external_lex_state = 5},
  [39] = {.lex_state = 99, .external_lex_state = 5},
  [40] = {.lex_state = 99, .external_lex_state = 2},
  [41] = {.lex_state = 99, .external_lex_state = 2},
  [42] = {.lex_state = 99, .external_lex_state = 2},
  [43] = {.lex_state = 99, .external_lex_state = 3},
  [44] = {.lex_state = 99, .external_lex_state = 3},
  [45] = {.lex_state = 99, .external_lex_state = 2},
  [46] = {.lex_state = 99, .external_lex_state = 3},
  [47] = {.lex_state = 99, .external_lex_state = 3},
  [48] = {.lex_state = 99, .external_lex_state = 2},
  [49] = {.lex_state = 99, .external_lex_state = 3},
  [50] = {.lex_state = 99, .external_lex_state = 3},
  [51] = {.lex_state = 99, .external_lex_state = 2},
  [52] = {.lex_state = 99, .external_lex_state = 2},
  [53] = {.lex_state = 99, .external_lex_state = 2},
  [54] = {.lex_state = 99, .external_lex_state = 3},
  [55] = {.lex_state = 99, .external_lex_state = 3},
  [56] = {.lex_state = 5, .external_lex_state = 7},
  [57] = {.lex_state = 5, .external_lex_state = 8},
  [58] = {.lex_state = 5, .external_lex_state = 7},
  [59] = {.lex_state = 5, .external_lex_state = 8},
  [60] = {.lex_state = 5, .external_lex_state = 8},
  [61] = {.lex_state = 5, .external_lex_state = 8},
  [62] = {.lex_state = 5, .external_lex_state = 2},
  [63] = {.lex_state = 5, .external_lex_state = 2},
  [64] = {.lex_state = 5, .external_lex_state = 2},
  [65] = {.lex_state = 5, .external_lex_state = 6},
  [66] = {.lex_state = 5, .external_lex_state = 8},
  [67] = {.lex_state = 5, .external_lex_state = 9},
  [68] = {.lex_state = 5, .external_lex_state = 9},
  [69] = {.lex_state = 99, .external_lex_state = 6},
  [70] = {.lex_state = 5, .external_lex_state = 6},
  [71] = {.lex_state = 5, .external_lex_state = 9},
  [72] = {.lex_state = 5, .external_lex_state = 6},
  [73] = {.lex_state = 5, .external_lex_state = 9},
  [74] = {.lex_state = 5, .external_lex_state = 9},
  [75] = {.lex_state = 5, .external_lex_state = 9},
  [76] = {.lex_state = 5, .external_lex_state = 9},
  [77] = {.lex_state = 5, .external_lex_state = 9},
  [78] = {.lex_state = 99, .external_lex_state = 6},
  [79] = {.lex_state = 5, .external_lex_state = 8},
  [80] = {.lex_state = 5, .external_lex_state = 2},
  [81] = {.lex_state = 5, .external_lex_state = 2},
  [82] = {.lex_state = 5, .external_lex_state = 2},
  [83] = {.lex_state = 5, .external_lex_state = 2},
  [84] = {.lex_state = 5, .external_lex_state = 2},
  [85] = {.lex_state = 5, .external_lex_state = 2},
  [86] = {.lex_state = 5, .external_lex_state = 2},
  [87] = {.lex_state = 5, .external_lex_state = 2},
  [88] = {.lex_state = 5, .external_lex_state = 2},
  [89] = {.lex_state = 5, .external_lex_state = 2},
  [90] = {.lex_state = 5, .external_lex_state = 2},
  [91] = {.lex_state = 5, .external_lex_state = 2},
  [92] = {.lex_state = 5, .external_lex_state = 2},
  [93] = {.lex_state = 5, .external_lex_state = 2},
  [94] = {.lex_state = 5, .external_lex_state = 2},
  [95] = {.lex_state = 5, .external_lex_state = 2},
  [96] = {.lex_state = 5, .external_lex_state = 2},
  [97] = {.lex_state = 5, .external_lex_state = 2},
  [98] = {.lex_state = 5, .external_lex_state = 2},
  [99] = {.lex_state = 5, .external_lex_state = 2},
  [100] = {.lex_state = 5, .external_lex_state = 2},
  [101] = {.lex_state = 5, .external_lex_state = 2},
  [102] = {.lex_state = 5, .external_lex_state = 2},
  [103] = {.lex_state = 5, .external_lex_state = 2},
  [104] = {.lex_state = 5, .external_lex_state = 2},
  [105] = {.lex_state = 5, .external_lex_state = 2},
  [106] = {.lex_state = 5, .external_lex_state = 2},
  [107] = {.lex_state = 5, .external_lex_state = 2},
  [108] = {.lex_state = 5, .external_lex_state = 6},
  [109] = {.lex_state = 5, .external_lex_state = 6},
  [110] = {.lex_state = 5, .external_lex_state = 2},
  [111] = {.lex_state = 5, .external_lex_state = 2},
  [112] = {.lex_state = 5, .external_lex_state = 2},
  [113] = {.lex_state = 5, .external_lex_state = 2},
  [114] = {.lex_state = 5, .external_lex_state = 7},
  [115] = {.lex_state = 5, .external_lex_state = 9},
  [116] = {.lex_state = 5, .external_lex_state = 9},
  [117] = {.lex_state = 5, .external_lex_state = 8},
  [118] = {.lex_state = 5, .external_lex_state = 8},
  [119] = {.lex_state = 5, .external_lex_state = 7},
  [120] = {.lex_state = 5, .external_lex_state = 6},
  [121] = {.lex_state = 5, .external_lex_state = 6},
  [122] = {.lex_state = 99, .external_lex_state = 2},
  [123] = {.lex_state = 5, .external_lex_state = 6},
  [124] = {.lex_state = 5, .external_lex_state = 6},
  [125] = {.lex_state = 5, .external_lex_state = 6},
  [126] = {.lex_state = 99, .external_lex_state = 9},
  [127] = {.lex_state = 99, .external_lex_state = 8},
  [128] = {.lex_state = 5, .external_lex_state = 6},
  [129] = {.lex_state = 99, .external_lex_state = 7},
  [130] = {.lex_state = 99, .external_lex_state = 7},
  [131] = {.lex_state = 99, .external_lex_state = 9},
  [132] = {.lex_state = 99, .external_lex_state = 8},
  [133] = {.lex_state = 99, .external_lex_state = 8},
  [134] = {.lex_state = 99, .external_lex_state = 7},
  [135] = {.lex_state = 99, .external_lex_state = 8},
  [136] = {.lex_state = 99, .external_lex_state = 7},
  [137] = {.lex_state = 99, .external_lex_state = 9},
  [138] = {.lex_state = 99, .external_lex_state = 9},
  [139] = {.lex_state = 5, .external_lex_state = 6},
  [140] = {.lex_state = 5, .external_lex_state = 6},
  [141] = {.lex_state = 5, .external_lex_state = 6},
  [142] = {.lex_state = 5, .external_lex_state = 6},
  [143] = {.lex_state = 0, .external_lex_state = 9},
  [144] = {.lex_state = 5, .external_lex_state = 6},
  [145] = {.lex_state = 5, .external_lex_state = 6},
  [146] = {.lex_state = 99, .external_lex_state = 8},
  [147] = {.lex_state = 0, .external_lex_state = 9},
  [148] = {.lex_state = 99, .external_lex_state = 9},
  [149] = {.lex_state = 5, .external_lex_state = 6},
  [150] = {.lex_state = 5, .external_lex_state = 6},
  [151] = {.lex_state = 5, .external_lex_state = 6},
  [152] = {.lex_state = 0, .external_lex_state = 8},
  [153] = {.lex_state = 5, .external_lex_state = 6},
  [154] = {.lex_state = 5, .external_lex_state = 6},
  [155] = {.lex_state = 99, .external_lex_state = 7},
  [156] = {.lex_state = 5, .external_lex_state = 6},
  [157] = {.lex_state = 99, .external_lex_state = 9},
  [158] = {.lex_state = 0, .external_lex_state = 9},
  [159] = {.lex_state = 99, .external_lex_state = 8},
  [160] = {.lex_state = 5, .external_lex_state = 6},
  [161] = {.lex_state = 0, .external_lex_state = 9},
  [162] = {.lex_state = 5, .external_lex_state = 6},
  [163] = {.lex_state = 0, .external_lex_state = 9},
  [164] = {.lex_state = 0, .external_lex_state = 7},
  [165] = {.lex_state = 0, .external_lex_state = 9},
  [166] = {.lex_state = 0, .external_lex_state = 9},
  [167] = {.lex_state = 0, .external_lex_state = 9},
  [168] = {.lex_state = 0, .external_lex_state = 9},
  [169] = {.lex_state = 0, .external_lex_state = 8},
  [170] = {.lex_state = 0, .external_lex_state = 8},
  [171] = {.lex_state = 0, .external_lex_state = 8},
  [172] = {.lex_state = 0, .external_lex_state = 9},
  [173] = {.lex_state = 0, .external_lex_state = 9},
  [174] = {.lex_state = 0, .external_lex_state = 9},
  [175] = {.lex_state = 0, .external_lex_state = 9},
  [176] = {.lex_state = 0, .external_lex_state = 9},
  [177] = {.lex_state = 0, .external_lex_state = 7},
  [178] = {.lex_state = 0, .external_lex_state = 8},
  [179] = {.lex_state = 0, .external_lex_state = 8},
  [180] = {.lex_state = 0, .external_lex_state = 9},
  [181] = {.lex_state = 0, .external_lex_state = 9},
  [182] = {.lex_state = 0, .external_lex_state = 8},
  [183] = {.lex_state = 0, .external_lex_state = 8},
  [184] = {.lex_state = 0, .external_lex_state = 9},
  [185] = {.lex_state = 0, .external_lex_state = 7},
  [186] = {.lex_state = 0, .external_lex_state = 8},
  [187] = {.lex_state = 0, .external_lex_state = 9},
  [188] = {.lex_state = 0, .external_lex_state = 8},
  [189] = {.lex_state = 0, .external_lex_state = 8},
  [190] = {.lex_state = 0, .external_lex_state = 7},
  [191] = {.lex_state = 0, .external_lex_state = 7},
  [192] = {.lex_state = 0, .external_lex_state = 8},
  [193] = {.lex_state = 0, .external_lex_state = 8},
  [194] = {.lex_state = 0, .external_lex_state = 7},
  [195] = {.lex_state = 0, .external_lex_state = 8},
  [196] = {.lex_state = 0, .external_lex_state = 8},
  [197] = {.lex_state = 0, .external_lex_state = 7},
  [198] = {.lex_state = 0, .external_lex_state = 7},
  [199] = {.lex_state = 0, .external_lex_state = 8},
  [200] = {.lex_state = 0, .external_lex_state = 7},
  [201] = {.lex_state = 0, .external_lex_state = 7},
  [202] = {.lex_state = 0, .external_lex_state = 7},
  [203] = {.lex_state = 0, .external_lex_state = 7},
  [204] = {.lex_state = 0, .external_lex_state = 7},
  [205] = {.lex_state = 0, .external_lex_state = 7},
  [206] = {.lex_state = 0, .external_lex_state = 7},
  [207] = {.lex_state = 0, .external_lex_state = 9},
  [208] = {.lex_state = 0, .external_lex_state = 9},
  [209] = {.lex_state = 0, .external_lex_state = 9},
  [210] = {.lex_state = 0, .external_lex_state = 9},
  [211] = {.lex_state = 5, .external_lex_state = 7},
  [212] = {.lex_state = 5, .external_lex_state = 7},
  [213] = {.lex_state = 5, .external_lex_state = 7},
  [214] = {.lex_state = 5, .external_lex_state = 7},
  [215] = {.lex_state = 5, .external_lex_state = 7},
  [216] = {.lex_state = 5, .external_lex_state = 7},
  [217] = {.lex_state = 5, .external_lex_state = 7},
  [218] = {.lex_state = 5, .external_lex_state = 7},
  [219] = {.lex_state = 5, .external_lex_state = 7},
  [220] = {.lex_state = 5, .external_lex_state = 7},
  [221] = {.lex_state = 5, .external_lex_state = 7},
  [222] = {.lex_state = 5, .external_lex_state = 7},
  [223] = {.lex_state = 5, .external_lex_state = 2},
  [224] = {.lex_state = 5, .external_lex_state = 6},
  [225] = {.lex_state = 5, .external_lex_state = 6},
  [226] = {.lex_state = 5, .external_lex_state = 6},
  [227] = {.lex_state = 5, .external_lex_state = 6},
  [228] = {.lex_state = 5, .external_lex_state = 6},
  [229] = {.lex_state = 5, .external_lex_state = 6},
  [230] = {.lex_state = 5, .external_lex_state = 6},
  [231] = {.lex_state = 5, .external_lex_state = 2},
  [232] = {.lex_state = 5, .external_lex_state = 2},
  [233] = {.lex_state = 5, .external_lex_state = 2},
  [234] = {.lex_state = 5, .external_lex_state = 6},
  [235] = {.lex_state = 5, .external_lex_state = 2},
  [236] = {.lex_state = 5, .external_lex_state = 6},
  [237] = {.lex_state = 5, .external_lex_state = 6},
  [238] = {.lex_state = 5, .external_lex_state = 6},
  [239] = {.lex_state = 0, .external_lex_state = 9},
  [240] = {.lex_state = 5, .external_lex_state = 6},
  [241] = {.lex_state = 5, .external_lex_state = 6},
  [242] = {.lex_state = 0, .external_lex_state = 8},
  [243] = {.lex_state = 0, .external_lex_state = 7},
  [244] = {.lex_state = 5, .external_lex_state = 6},
  [245] = {.lex_state = 0, .external_lex_state = 7},
  [246] = {.lex_state = 5, .external_lex_state = 6},
  [247] = {.lex_state = 0, .external_lex_state = 9},
  [248] = {.lex_state = 0, .external_lex_state = 9},
  [249] = {.lex_state = 0, .external_lex_state = 7},
  [250] = {.lex_state = 5, .external_lex_state = 6},
  [251] = {.lex_state = 0, .external_lex_state = 7},
  [252] = {.lex_state = 0, .external_lex_state = 7},
  [253] = {.lex_state = 0, .external_lex_state = 8},
  [254] = {.lex_state = 0, .external_lex_state = 9},
  [255] = {.lex_state = 0, .external_lex_state = 7},
  [256] = {.lex_state = 5, .external_lex_state = 6},
  [257] = {.lex_state = 0, .external_lex_state = 8},
  [258] = {.lex_state = 0, .external_lex_state = 8},
  [259] = {.lex_state = 5, .external_lex_state = 6},
  [260] = {.lex_state = 0, .external_lex_state = 6},
  [261] = {.lex_state = 0, .external_lex_state = 7},
  [262] = {.lex_state = 0, .external_lex_state = 7},
  [263] = {.lex_state = 0, .external_lex_state = 8},
  [264] = {.lex_state = 0, .external_lex_state = 9},
  [265] = {.lex_state = 0, .external_lex_state = 6},
  [266] = {.lex_state = 0, .external_lex_state = 8},
  [267] = {.lex_state = 0, .external_lex_state = 7},
  [268] = {.lex_state = 0, .external_lex_state = 8},
  [269] = {.lex_state = 0, .external_lex_state = 7},
  [270] = {.lex_state = 0, .external_lex_state = 8},
  [271] = {.lex_state = 0, .external_lex_state = 7},
  [272] = {.lex_state = 6, .external_lex_state = 2},
  [273] = {.lex_state = 6, .external_lex_state = 2},
  [274] = {.lex_state = 0, .external_lex_state = 7},
  [275] = {.lex_state = 0, .external_lex_state = 7},
  [276] = {.lex_state = 0, .external_lex_state = 8},
  [277] = {.lex_state = 0, .external_lex_state = 2},
  [278] = {.lex_state = 0, .external_lex_state = 7},
  [279] = {.lex_state = 0, .external_lex_state = 8},
  [280] = {.lex_state = 0, .external_lex_state = 7},
  [281] = {.lex_state = 0, .external_lex_state = 7},
  [282] = {.lex_state = 0, .external_lex_state = 7},
  [283] = {.lex_state = 0, .external_lex_state = 7},
  [284] = {.lex_state = 0, .external_lex_state = 8},
  [285] = {.lex_state = 0, .external_lex_state = 2},
  [286] = {.lex_state = 6, .external_lex_state = 8},
  [287] = {.lex_state = 0, .external_lex_state = 7},
  [288] = {.lex_state = 0, .external_lex_state = 8},
  [289] = {.lex_state = 0, .external_lex_state = 7},
  [290] = {.lex_state = 0, .external_lex_state = 8},
  [291] = {.lex_state = 0, .external_lex_state = 8},
  [292] = {.lex_state = 0, .external_lex_state = 8},
  [293] = {.lex_state = 0, .external_lex_state = 8},
  [294] = {.lex_state = 0, .external_lex_state = 7},
  [295] = {.lex_state = 0, .external_lex_state = 8},
  [296] = {.lex_state = 0, .external_lex_state = 7},
  [297] = {.lex_state = 0, .external_lex_state = 7},
  [298] = {.lex_state = 0, .external_lex_state = 7},
  [299] = {.lex_state = 0, .external_lex_state = 2},
  [300] = {.lex_state = 0, .external_lex_state = 2},
  [301] = {.lex_state = 0, .external_lex_state = 2},
  [302] = {.lex_state = 0, .external_lex_state = 2},
  [303] = {.lex_state = 0, .external_lex_state = 2},
  [304] = {.lex_state = 0, .external_lex_state = 8},
  [305] = {.lex_state = 154, .external_lex_state = 2},
  [306] = {.lex_state = 159, .external_lex_state = 2},
  [307] = {.lex_state = 154, .external_lex_state = 2},
  [308] = {.lex_state = 159, .external_lex_state = 2},
  [309] = {.lex_state = 0, .external_lex_state = 2},
  [310] = {.lex_state = 0, .external_lex_state = 8},
  [311] = {.lex_state = 0, .external_lex_state = 2},
  [312] = {.lex_state = 159, .external_lex_state = 2},
  [313] = {.lex_state = 154, .external_lex_state = 2},
  [314] = {.lex_state = 0, .external_lex_state = 2},
  [315] = {.lex_state = 0, .external_lex_state = 2},
  [316] = {.lex_state = 159, .external_lex_state = 2},
  [317] = {.lex_state = 154, .external_lex_state = 2},
  [318] = {.lex_state = 0, .external_lex_state = 2},
};

enum {
  ts_external_token__indent = 0,
  ts_external_token__dedent = 1,
  ts_external_token__newline = 2,
  ts_external_token_comment = 3,
  ts_external_token_RPAREN = 4,
  ts_external_token_RBRACK = 5,
  ts_external_token_RBRACE = 6,
};

static const TSSymbol ts_external_scanner_symbol_map[EXTERNAL_TOKEN_COUNT] = {
  [ts_external_token__indent] = sym__indent,
  [ts_external_token__dedent] = sym__dedent,
  [ts_external_token__newline] = sym__newline,
  [ts_external_token_comment] = sym_comment,
  [ts_external_token_RPAREN] = anon_sym_RPAREN,
  [ts_external_token_RBRACK] = anon_sym_RBRACK,
  [ts_external_token_RBRACE] = anon_sym_RBRACE,
};

static const bool ts_external_scanner_states[10][EXTERNAL_TOKEN_COUNT] = {
  [1] = {
    [ts_external_token__indent] = true,
    [ts_external_token__dedent] = true,
    [ts_external_token__newline] = true,
    [ts_external_token_comment] = true,
    [ts_external_token_RPAREN] = true,
    [ts_external_token_RBRACK] = true,
    [ts_external_token_RBRACE] = true,
  },
  [2] = {
    [ts_external_token_comment] = true,
  },
  [3] = {
    [ts_external_token__dedent] = true,
    [ts_external_token_comment] = true,
  },
  [4] = {
    [ts_external_token__indent] = true,
    [ts_external_token_comment] = true,
  },
  [5] = {
    [ts_external_token__indent] = true,
    [ts_external_token__dedent] = true,
    [ts_external_token_comment] = true,
  },
  [6] = {
    [ts_external_token__newline] = true,
    [ts_external_token_comment] = true,
  },
  [7] = {
    [ts_external_token_comment] = true,
    [ts_external_token_RBRACE] = true,
  },
  [8] = {
    [ts_external_token_comment] = true,
    [ts_external_token_RBRACK] = true,
  },
  [9] = {
    [ts_external_token_comment] = true,
    [ts_external_token_RPAREN] = true,
  },
};

static const uint16_t ts_parse_table[LARGE_STATE_COUNT][SYMBOL_COUNT] = {
  [0] = {
    [ts_builtin_sym_end] = ACTIONS(1),
    [sym_name] = ACTIONS(1),
    [anon_sym_cardinality] = ACTIONS(1),
    [anon_sym_LBRACE] = ACTIONS(1),
    [anon_sym_COMMA] = ACTIONS(1),
    [anon_sym_RBRACE] = ACTIONS(1),
    [anon_sym_as] = ACTIONS(1),
    [anon_sym_namespace] = ACTIONS(1),
    [anon_sym_LBRACK] = ACTIONS(1),
    [anon_sym_DOT_DOT] = ACTIONS(1),
    [anon_sym_STAR] = ACTIONS(1),
    [anon_sym_RBRACK] = ACTIONS(1),
    [anon_sym_constraint] = ACTIONS(1),
    [anon_sym_constraints] = ACTIONS(1),
    [anon_sym_BANG] = ACTIONS(1),
    [anon_sym_PIPE] = ACTIONS(1),
    [anon_sym_AMP] = ACTIONS(1),
    [anon_sym_EQ_GT] = ACTIONS(1),
    [anon_sym_LT_EQ_GT] = ACTIONS(1),
    [anon_sym_GT] = ACTIONS(1),
    [anon_sym_LT] = ACTIONS(1),
    [anon_sym_EQ_EQ] = ACTIONS(1),
    [anon_sym_PLUS] = ACTIONS(1),
    [anon_sym_DASH] = ACTIONS(1),
    [anon_sym_SLASH] = ACTIONS(1),
    [anon_sym_LPAREN] = ACTIONS(1),
    [anon_sym_RPAREN] = ACTIONS(1),
    [anon_sym_true] = ACTIONS(1),
    [anon_sym_false] = ACTIONS(1),
    [sym_number] = ACTIONS(1),
    [sym_comment] = ACTIONS(3),
    [anon_sym_DOT] = ACTIONS(1),
    [anon_sym_or] = ACTIONS(1),
    [anon_sym_alternative] = ACTIONS(1),
    [anon_sym_mandatory] = ACTIONS(1),
    [anon_sym_optional] = ACTIONS(1),
    [anon_sym_SMT_DASHlevel] = ACTIONS(1),
    [anon_sym_SAT_DASHlevel] = ACTIONS(1),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(1),
    [anon_sym_group_DASHcardinality] = ACTIONS(1),
    [anon_sym_feature_DASHcardinality] = ACTIONS(1),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(1),
    [anon_sym_type_DASHconstraints] = ACTIONS(1),
    [anon_sym_string_DASHconstraints] = ACTIONS(1),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(1),
    [anon_sym_Boolean] = ACTIONS(1),
    [anon_sym_Real] = ACTIONS(1),
    [anon_sym_Integer] = ACTIONS(1),
    [anon_sym_String] = ACTIONS(1),
    [anon_sym_SQUOTE] = ACTIONS(1),
    [anon_sym_DQUOTE] = ACTIONS(1),
    [sym_imports] = ACTIONS(1),
    [sym_features] = ACTIONS(1),
    [sym_include] = ACTIONS(1),
    [sym_int] = ACTIONS(1),
    [sym__indent] = ACTIONS(1),
    [sym__dedent] = ACTIONS(1),
    [sym__newline] = ACTIONS(1),
  },
  [1] = {
    [sym_source_file] = STATE(303),
    [sym_blk] = STATE(10),
    [sym__header] = STATE(234),
    [sym_typed_feature] = STATE(234),
    [sym_ref] = STATE(234),
    [sym_namespace] = STATE(234),
    [sym_incomplete_namespace] = STATE(234),
    [sym_incomplete_ref] = STATE(234),
    [sym_cardinality] = STATE(234),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(234),
    [sym_group_mode] = STATE(234),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(234),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(10),
    [ts_builtin_sym_end] = ACTIONS(5),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(33),
    [sym_features] = ACTIONS(33),
    [sym_include] = ACTIONS(33),
  },
  [2] = {
    [sym_blk] = STATE(2),
    [sym__header] = STATE(234),
    [sym_typed_feature] = STATE(234),
    [sym_ref] = STATE(234),
    [sym_namespace] = STATE(234),
    [sym_incomplete_namespace] = STATE(234),
    [sym_incomplete_ref] = STATE(234),
    [sym_cardinality] = STATE(234),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(234),
    [sym_group_mode] = STATE(234),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(234),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(2),
    [ts_builtin_sym_end] = ACTIONS(35),
    [sym_name] = ACTIONS(37),
    [anon_sym_namespace] = ACTIONS(40),
    [anon_sym_LBRACK] = ACTIONS(43),
    [anon_sym_STAR] = ACTIONS(46),
    [anon_sym_constraints] = ACTIONS(49),
    [anon_sym_BANG] = ACTIONS(52),
    [anon_sym_LPAREN] = ACTIONS(55),
    [anon_sym_true] = ACTIONS(58),
    [anon_sym_false] = ACTIONS(58),
    [sym_number] = ACTIONS(61),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(64),
    [anon_sym_alternative] = ACTIONS(64),
    [anon_sym_mandatory] = ACTIONS(64),
    [anon_sym_optional] = ACTIONS(64),
    [anon_sym_SMT_DASHlevel] = ACTIONS(67),
    [anon_sym_SAT_DASHlevel] = ACTIONS(67),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(67),
    [anon_sym_group_DASHcardinality] = ACTIONS(46),
    [anon_sym_feature_DASHcardinality] = ACTIONS(46),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(46),
    [anon_sym_type_DASHconstraints] = ACTIONS(46),
    [anon_sym_string_DASHconstraints] = ACTIONS(46),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(46),
    [anon_sym_SQUOTE] = ACTIONS(70),
    [anon_sym_DQUOTE] = ACTIONS(73),
    [sym_imports] = ACTIONS(76),
    [sym_features] = ACTIONS(76),
    [sym_include] = ACTIONS(76),
  },
  [3] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(37),
    [anon_sym_namespace] = ACTIONS(40),
    [anon_sym_LBRACK] = ACTIONS(43),
    [anon_sym_STAR] = ACTIONS(46),
    [anon_sym_constraints] = ACTIONS(49),
    [anon_sym_BANG] = ACTIONS(52),
    [anon_sym_LPAREN] = ACTIONS(55),
    [anon_sym_true] = ACTIONS(58),
    [anon_sym_false] = ACTIONS(58),
    [sym_number] = ACTIONS(61),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(64),
    [anon_sym_alternative] = ACTIONS(64),
    [anon_sym_mandatory] = ACTIONS(64),
    [anon_sym_optional] = ACTIONS(64),
    [anon_sym_SMT_DASHlevel] = ACTIONS(67),
    [anon_sym_SAT_DASHlevel] = ACTIONS(67),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(67),
    [anon_sym_group_DASHcardinality] = ACTIONS(46),
    [anon_sym_feature_DASHcardinality] = ACTIONS(46),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(46),
    [anon_sym_type_DASHconstraints] = ACTIONS(46),
    [anon_sym_string_DASHconstraints] = ACTIONS(46),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(46),
    [anon_sym_SQUOTE] = ACTIONS(70),
    [anon_sym_DQUOTE] = ACTIONS(73),
    [sym_imports] = ACTIONS(79),
    [sym_features] = ACTIONS(79),
    [sym_include] = ACTIONS(79),
    [sym__dedent] = ACTIONS(35),
  },
  [4] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(84),
  },
  [5] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(86),
  },
  [6] = {
    [sym_blk] = STATE(4),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(4),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(88),
  },
  [7] = {
    [sym_blk] = STATE(5),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(5),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(90),
  },
  [8] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(92),
  },
  [9] = {
    [sym_blk] = STATE(12),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(12),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(94),
  },
  [10] = {
    [sym_blk] = STATE(2),
    [sym__header] = STATE(234),
    [sym_typed_feature] = STATE(234),
    [sym_ref] = STATE(234),
    [sym_namespace] = STATE(234),
    [sym_incomplete_namespace] = STATE(234),
    [sym_incomplete_ref] = STATE(234),
    [sym_cardinality] = STATE(234),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(234),
    [sym_group_mode] = STATE(234),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(234),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(2),
    [ts_builtin_sym_end] = ACTIONS(96),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(33),
    [sym_features] = ACTIONS(33),
    [sym_include] = ACTIONS(33),
  },
  [11] = {
    [sym_blk] = STATE(17),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(17),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(98),
  },
  [12] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(100),
  },
  [13] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(102),
  },
  [14] = {
    [sym_blk] = STATE(19),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(19),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(104),
  },
  [15] = {
    [sym_blk] = STATE(13),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(13),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(106),
  },
  [16] = {
    [sym_blk] = STATE(20),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(20),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(108),
  },
  [17] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(110),
  },
  [18] = {
    [sym_blk] = STATE(8),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(8),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(112),
  },
  [19] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(114),
  },
  [20] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(160),
    [sym_unary_expr] = STATE(149),
    [sym_binary_expr] = STATE(149),
    [sym_nested_expr] = STATE(149),
    [sym_function] = STATE(149),
    [sym_bool] = STATE(149),
    [sym_path] = STATE(128),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(228),
    [sym_minor_lvl] = STATE(228),
    [sym_string] = STATE(149),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(7),
    [anon_sym_namespace] = ACTIONS(9),
    [anon_sym_LBRACK] = ACTIONS(11),
    [anon_sym_STAR] = ACTIONS(13),
    [anon_sym_constraints] = ACTIONS(15),
    [anon_sym_BANG] = ACTIONS(17),
    [anon_sym_LPAREN] = ACTIONS(19),
    [anon_sym_true] = ACTIONS(21),
    [anon_sym_false] = ACTIONS(21),
    [sym_number] = ACTIONS(23),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(25),
    [anon_sym_alternative] = ACTIONS(25),
    [anon_sym_mandatory] = ACTIONS(25),
    [anon_sym_optional] = ACTIONS(25),
    [anon_sym_SMT_DASHlevel] = ACTIONS(27),
    [anon_sym_SAT_DASHlevel] = ACTIONS(27),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(27),
    [anon_sym_group_DASHcardinality] = ACTIONS(13),
    [anon_sym_feature_DASHcardinality] = ACTIONS(13),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(13),
    [anon_sym_type_DASHconstraints] = ACTIONS(13),
    [anon_sym_string_DASHconstraints] = ACTIONS(13),
    [anon_sym_numeric_DASHconstraints] = ACTIONS(13),
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(82),
    [sym_features] = ACTIONS(82),
    [sym_include] = ACTIONS(82),
    [sym__dedent] = ACTIONS(116),
  },
};

static const uint16_t ts_small_parse_table[] = {
  [0] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(122), 1,
      sym__indent,
    ACTIONS(120), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(118), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [40] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(128), 1,
      sym__indent,
    ACTIONS(126), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(124), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [80] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(132), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(130), 18,
      sym__indent,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [118] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(138), 1,
      sym__indent,
    ACTIONS(136), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(134), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [158] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(140), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(142), 18,
      sym__indent,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [196] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(146), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(144), 18,
      sym__indent,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [234] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(148), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(150), 18,
      sym__indent,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [272] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(146), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(144), 18,
      sym__indent,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [310] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(148), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(150), 18,
      sym__indent,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [348] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(132), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(130), 18,
      sym__indent,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [386] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(154), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(152), 18,
      sym__indent,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [424] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(140), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(142), 18,
      sym__indent,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [462] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(154), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(152), 18,
      sym__indent,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [500] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(156), 1,
      sym_name,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(230), 2,
      sym_major_lvl,
      sym_minor_lvl,
    ACTIONS(27), 3,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
    ACTIONS(158), 4,
      anon_sym_cardinality,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(13), 7,
      anon_sym_STAR,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
    ACTIONS(160), 10,
      sym__newline,
      anon_sym_LBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [550] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(162), 1,
      sym__indent,
    ACTIONS(126), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(124), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [590] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(168), 1,
      sym__indent,
    ACTIONS(166), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(164), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [630] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(170), 1,
      sym__indent,
    ACTIONS(166), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(164), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [670] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(172), 1,
      sym__indent,
    ACTIONS(136), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(134), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [710] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(174), 1,
      sym__indent,
    ACTIONS(120), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(118), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [750] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(178), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(176), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [787] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(182), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(180), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [824] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(186), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(184), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [861] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(188), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(190), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [898] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(192), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(194), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [935] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(192), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(194), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [972] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(182), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(180), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1009] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(196), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(198), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1046] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(202), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(200), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1083] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(178), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(176), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1120] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(204), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(206), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1157] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(188), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(190), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1194] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(204), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(206), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1231] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(196), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(198), 17,
      ts_builtin_sym_end,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1268] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(202), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(200), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1305] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(186), 12,
      anon_sym_namespace,
      anon_sym_constraints,
      anon_sym_true,
      anon_sym_false,
      anon_sym_or,
      anon_sym_alternative,
      anon_sym_mandatory,
      anon_sym_optional,
      sym_imports,
      sym_features,
      sym_include,
      sym_name,
    ACTIONS(184), 17,
      sym__dedent,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1342] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(208), 1,
      sym_name,
    ACTIONS(210), 1,
      anon_sym_LBRACE,
    ACTIONS(214), 1,
      anon_sym_LBRACK,
    ACTIONS(216), 1,
      anon_sym_BANG,
    ACTIONS(218), 1,
      anon_sym_LPAREN,
    ACTIONS(222), 1,
      sym_number,
    ACTIONS(224), 1,
      anon_sym_SQUOTE,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    STATE(185), 1,
      sym__expr,
    ACTIONS(212), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(134), 2,
      sym_string_name,
      sym__any_name,
    STATE(281), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(191), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1399] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(230), 1,
      anon_sym_LBRACE,
    ACTIONS(232), 1,
      anon_sym_LBRACK,
    ACTIONS(234), 1,
      anon_sym_RBRACK,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(178), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(276), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1455] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(248), 5,
      anon_sym_LT,
      anon_sym_SLASH,
      anon_sym_true,
      anon_sym_false,
      sym_name,
    ACTIONS(250), 19,
      anon_sym_LBRACE,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_LBRACK,
      anon_sym_STAR,
      anon_sym_BANG,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_LPAREN,
      sym_number,
      anon_sym_DOT,
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1487] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(230), 1,
      anon_sym_LBRACE,
    ACTIONS(232), 1,
      anon_sym_LBRACK,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    ACTIONS(252), 1,
      anon_sym_RBRACK,
    STATE(178), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(276), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1543] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(230), 1,
      anon_sym_LBRACE,
    ACTIONS(232), 1,
      anon_sym_LBRACK,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    ACTIONS(254), 1,
      anon_sym_RBRACK,
    STATE(178), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(276), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1599] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(230), 1,
      anon_sym_LBRACE,
    ACTIONS(232), 1,
      anon_sym_LBRACK,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    ACTIONS(256), 1,
      anon_sym_RBRACK,
    STATE(178), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(276), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1655] = 14,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(230), 1,
      anon_sym_LBRACE,
    ACTIONS(232), 1,
      anon_sym_LBRACK,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(178), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(268), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1708] = 14,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(230), 1,
      anon_sym_LBRACE,
    ACTIONS(232), 1,
      anon_sym_LBRACK,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(178), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(253), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1761] = 14,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(230), 1,
      anon_sym_LBRACE,
    ACTIONS(232), 1,
      anon_sym_LBRACK,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(178), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(276), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1814] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(258), 1,
      sym_name,
    ACTIONS(260), 1,
      anon_sym_cardinality,
    ACTIONS(268), 1,
      anon_sym_DOT,
    STATE(121), 1,
      aux_sym_path_repeat1,
    STATE(226), 1,
      aux_sym_lang_lvl_repeat1,
    ACTIONS(262), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(256), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(264), 3,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(266), 9,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [1860] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    ACTIONS(270), 1,
      anon_sym_RBRACK,
    STATE(199), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1905] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(278), 1,
      anon_sym_RPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1950] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(288), 1,
      anon_sym_RPAREN,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1995] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(290), 1,
      sym_name,
    ACTIONS(292), 1,
      anon_sym_cardinality,
    ACTIONS(294), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(230), 2,
      sym_major_lvl,
      sym_minor_lvl,
    STATE(236), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(27), 3,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
    ACTIONS(13), 7,
      anon_sym_STAR,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
  [2034] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(300), 1,
      anon_sym_LPAREN,
    ACTIONS(296), 5,
      anon_sym_cardinality,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
      sym_name,
    ACTIONS(298), 13,
      sym__newline,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
      anon_sym_DQUOTE,
  [2063] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(302), 1,
      anon_sym_RPAREN,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2108] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(304), 1,
      sym_name,
    STATE(123), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(306), 4,
      anon_sym_cardinality,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(308), 11,
      sym__newline,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [2141] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(310), 1,
      anon_sym_RPAREN,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2186] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(312), 1,
      anon_sym_RPAREN,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2231] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(314), 1,
      anon_sym_RPAREN,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2276] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(316), 1,
      anon_sym_RPAREN,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2321] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(318), 1,
      anon_sym_RPAREN,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2366] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(290), 1,
      sym_name,
    ACTIONS(320), 1,
      anon_sym_cardinality,
    ACTIONS(322), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(230), 2,
      sym_major_lvl,
      sym_minor_lvl,
    STATE(236), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(27), 3,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
    ACTIONS(13), 7,
      anon_sym_STAR,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
  [2405] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    ACTIONS(324), 1,
      anon_sym_RBRACK,
    STATE(199), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2450] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(171), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2492] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      sym_name,
    ACTIONS(17), 1,
      anon_sym_BANG,
    ACTIONS(19), 1,
      anon_sym_LPAREN,
    ACTIONS(23), 1,
      sym_number,
    ACTIONS(29), 1,
      anon_sym_SQUOTE,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    STATE(154), 1,
      sym__expr,
    ACTIONS(21), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(124), 2,
      sym_string_name,
      sym__any_name,
    STATE(149), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2534] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(210), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2576] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(208), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2618] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(186), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2660] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(147), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2702] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(152), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2744] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(175), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2786] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(195), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2828] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(169), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2870] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(170), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2912] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(161), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2954] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(174), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2996] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(173), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3038] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(163), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3080] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(208), 1,
      sym_name,
    ACTIONS(216), 1,
      anon_sym_BANG,
    ACTIONS(218), 1,
      anon_sym_LPAREN,
    ACTIONS(222), 1,
      sym_number,
    ACTIONS(224), 1,
      anon_sym_SQUOTE,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    STATE(194), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(134), 2,
      sym_string_name,
      sym__any_name,
    STATE(191), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3122] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(143), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3164] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(158), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3206] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      sym_name,
    ACTIONS(17), 1,
      anon_sym_BANG,
    ACTIONS(19), 1,
      anon_sym_LPAREN,
    ACTIONS(23), 1,
      sym_number,
    ACTIONS(29), 1,
      anon_sym_SQUOTE,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    STATE(150), 1,
      sym__expr,
    ACTIONS(21), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(124), 2,
      sym_string_name,
      sym__any_name,
    STATE(149), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3248] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      sym_name,
    ACTIONS(17), 1,
      anon_sym_BANG,
    ACTIONS(19), 1,
      anon_sym_LPAREN,
    ACTIONS(23), 1,
      sym_number,
    ACTIONS(29), 1,
      anon_sym_SQUOTE,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    STATE(140), 1,
      sym__expr,
    ACTIONS(21), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(124), 2,
      sym_string_name,
      sym__any_name,
    STATE(149), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3290] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 1,
      sym_name,
    ACTIONS(236), 1,
      anon_sym_BANG,
    ACTIONS(238), 1,
      anon_sym_LPAREN,
    ACTIONS(242), 1,
      sym_number,
    ACTIONS(244), 1,
      anon_sym_SQUOTE,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    STATE(199), 1,
      sym__expr,
    ACTIONS(240), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(135), 2,
      sym_string_name,
      sym__any_name,
    STATE(189), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3332] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      sym_name,
    ACTIONS(17), 1,
      anon_sym_BANG,
    ACTIONS(19), 1,
      anon_sym_LPAREN,
    ACTIONS(23), 1,
      sym_number,
    ACTIONS(29), 1,
      anon_sym_SQUOTE,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    STATE(142), 1,
      sym__expr,
    ACTIONS(21), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(124), 2,
      sym_string_name,
      sym__any_name,
    STATE(149), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3374] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(209), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3416] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(208), 1,
      sym_name,
    ACTIONS(216), 1,
      anon_sym_BANG,
    ACTIONS(218), 1,
      anon_sym_LPAREN,
    ACTIONS(222), 1,
      sym_number,
    ACTIONS(224), 1,
      anon_sym_SQUOTE,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    STATE(205), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(134), 2,
      sym_string_name,
      sym__any_name,
    STATE(191), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3458] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(208), 1,
      sym_name,
    ACTIONS(216), 1,
      anon_sym_BANG,
    ACTIONS(218), 1,
      anon_sym_LPAREN,
    ACTIONS(222), 1,
      sym_number,
    ACTIONS(224), 1,
      anon_sym_SQUOTE,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    STATE(206), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(134), 2,
      sym_string_name,
      sym__any_name,
    STATE(191), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3500] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(208), 1,
      sym_name,
    ACTIONS(216), 1,
      anon_sym_BANG,
    ACTIONS(218), 1,
      anon_sym_LPAREN,
    ACTIONS(222), 1,
      sym_number,
    ACTIONS(224), 1,
      anon_sym_SQUOTE,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    STATE(204), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(134), 2,
      sym_string_name,
      sym__any_name,
    STATE(191), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3542] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(208), 1,
      sym_name,
    ACTIONS(216), 1,
      anon_sym_BANG,
    ACTIONS(218), 1,
      anon_sym_LPAREN,
    ACTIONS(222), 1,
      sym_number,
    ACTIONS(224), 1,
      anon_sym_SQUOTE,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    STATE(203), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(134), 2,
      sym_string_name,
      sym__any_name,
    STATE(191), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3584] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(166), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3626] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(304), 1,
      sym_name,
    STATE(123), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(158), 3,
      anon_sym_cardinality,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(160), 11,
      sym__newline,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [3658] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(248), 5,
      anon_sym_cardinality,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
      sym_name,
    ACTIONS(250), 13,
      sym__newline,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
      anon_sym_DQUOTE,
  [3684] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(208), 1,
      sym_name,
    ACTIONS(216), 1,
      anon_sym_BANG,
    ACTIONS(218), 1,
      anon_sym_LPAREN,
    ACTIONS(222), 1,
      sym_number,
    ACTIONS(224), 1,
      anon_sym_SQUOTE,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    STATE(177), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(134), 2,
      sym_string_name,
      sym__any_name,
    STATE(191), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3726] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(207), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3768] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(272), 1,
      sym_name,
    ACTIONS(274), 1,
      anon_sym_BANG,
    ACTIONS(276), 1,
      anon_sym_LPAREN,
    ACTIONS(282), 1,
      sym_number,
    ACTIONS(284), 1,
      anon_sym_SQUOTE,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    STATE(187), 1,
      sym__expr,
    ACTIONS(280), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(138), 2,
      sym_string_name,
      sym__any_name,
    STATE(165), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3810] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(7), 1,
      sym_name,
    ACTIONS(17), 1,
      anon_sym_BANG,
    ACTIONS(19), 1,
      anon_sym_LPAREN,
    ACTIONS(23), 1,
      sym_number,
    ACTIONS(29), 1,
      anon_sym_SQUOTE,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    STATE(153), 1,
      sym__expr,
    ACTIONS(21), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(124), 2,
      sym_string_name,
      sym__any_name,
    STATE(149), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3852] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(326), 1,
      sym_name,
    ACTIONS(158), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(155), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(160), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [3883] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(328), 1,
      sym_name,
    ACTIONS(306), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(148), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(308), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [3914] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(328), 1,
      sym_name,
    ACTIONS(158), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(148), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(160), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [3945] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    ACTIONS(330), 1,
      sym_name,
    ACTIONS(158), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(146), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(160), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [3976] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    ACTIONS(330), 1,
      sym_name,
    ACTIONS(306), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(146), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(308), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4007] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(326), 1,
      sym_name,
    ACTIONS(306), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(155), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(308), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4038] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(336), 1,
      anon_sym_DOT,
    STATE(120), 1,
      aux_sym_path_repeat1,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 13,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_as,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4067] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(343), 1,
      anon_sym_DOT,
    STATE(120), 1,
      aux_sym_path_repeat1,
    ACTIONS(341), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(339), 13,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_as,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4096] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(290), 1,
      sym_name,
    STATE(230), 2,
      sym_major_lvl,
      sym_minor_lvl,
    STATE(236), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(27), 3,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
    ACTIONS(13), 7,
      anon_sym_STAR,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
      anon_sym_string_DASHconstraints,
      anon_sym_numeric_DASHconstraints,
  [4128] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 14,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_as,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
  [4152] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(345), 1,
      anon_sym_DOT,
    STATE(121), 1,
      aux_sym_path_repeat1,
    ACTIONS(264), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(266), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4180] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 14,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_as,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
  [4204] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(347), 1,
      anon_sym_LPAREN,
    ACTIONS(296), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(298), 12,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
      anon_sym_DOT,
  [4229] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(349), 1,
      anon_sym_LPAREN,
    ACTIONS(296), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(298), 12,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
  [4254] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(353), 1,
      anon_sym_as,
    ACTIONS(357), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(351), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
    ACTIONS(355), 9,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4281] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(359), 1,
      anon_sym_DOT,
    STATE(129), 1,
      aux_sym_path_repeat1,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4308] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(362), 1,
      anon_sym_DOT,
    STATE(129), 1,
      aux_sym_path_repeat1,
    ACTIONS(341), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(339), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4335] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(364), 1,
      anon_sym_DOT,
    STATE(137), 1,
      aux_sym_path_repeat1,
    ACTIONS(341), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(339), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [4362] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(366), 1,
      anon_sym_DOT,
    STATE(132), 1,
      aux_sym_path_repeat1,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4389] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(369), 1,
      anon_sym_DOT,
    STATE(132), 1,
      aux_sym_path_repeat1,
    ACTIONS(341), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(339), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4416] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(371), 1,
      anon_sym_DOT,
    STATE(130), 1,
      aux_sym_path_repeat1,
    ACTIONS(264), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(266), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4443] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(373), 1,
      anon_sym_DOT,
    STATE(133), 1,
      aux_sym_path_repeat1,
    ACTIONS(264), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(266), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4470] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(375), 1,
      anon_sym_LPAREN,
    ACTIONS(296), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(298), 12,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
  [4495] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(377), 1,
      anon_sym_DOT,
    STATE(137), 1,
      aux_sym_path_repeat1,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [4522] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(380), 1,
      anon_sym_DOT,
    STATE(131), 1,
      aux_sym_path_repeat1,
    ACTIONS(264), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(266), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [4549] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(384), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(382), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4571] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(394), 1,
      anon_sym_LT,
    ACTIONS(396), 1,
      anon_sym_SLASH,
    ACTIONS(390), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(392), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(388), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 5,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4601] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(400), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(398), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4623] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(396), 1,
      anon_sym_SLASH,
    ACTIONS(402), 1,
      anon_sym_LT,
    ACTIONS(388), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 9,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
  [4649] = 10,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(404), 1,
      anon_sym_COMMA,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(418), 1,
      anon_sym_RPAREN,
    STATE(239), 1,
      aux_sym_function_repeat1,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4685] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(422), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(420), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4707] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(426), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(424), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4729] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 12,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
  [4751] = 10,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(428), 1,
      anon_sym_COMMA,
    ACTIONS(430), 1,
      anon_sym_RPAREN,
    STATE(254), 1,
      aux_sym_function_repeat1,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4787] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 12,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
      anon_sym_DOT,
  [4809] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(357), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(355), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4831] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(394), 1,
      anon_sym_LT,
    ACTIONS(396), 1,
      anon_sym_SLASH,
    ACTIONS(392), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(388), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 7,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4859] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(434), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(432), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4881] = 10,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(436), 1,
      anon_sym_COMMA,
    ACTIONS(440), 1,
      anon_sym_RBRACK,
    ACTIONS(448), 1,
      anon_sym_LT,
    ACTIONS(450), 1,
      anon_sym_SLASH,
    STATE(257), 1,
      aux_sym_attribute_constraints_repeat1,
    ACTIONS(442), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(444), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(446), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(438), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4917] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(454), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(452), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4939] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(402), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(386), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [4961] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(334), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(332), 12,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
  [4983] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(458), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(456), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5005] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(248), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(250), 12,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
      anon_sym_DOT,
  [5027] = 10,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(460), 1,
      anon_sym_COMMA,
    ACTIONS(462), 1,
      anon_sym_RPAREN,
    STATE(264), 1,
      aux_sym_function_repeat1,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5063] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(248), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(250), 12,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_DOT,
  [5085] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(394), 1,
      anon_sym_LT,
    ACTIONS(396), 1,
      anon_sym_SLASH,
    ACTIONS(390), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(392), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(466), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(388), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(464), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [5117] = 10,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(468), 1,
      anon_sym_COMMA,
    ACTIONS(470), 1,
      anon_sym_RPAREN,
    STATE(248), 1,
      aux_sym_function_repeat1,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5153] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(474), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(472), 12,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5175] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(402), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(386), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5196] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(458), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(456), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5217] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(357), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(355), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5238] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(454), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(452), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5259] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(426), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(424), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5280] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(422), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(420), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5301] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(448), 1,
      anon_sym_LT,
    ACTIONS(450), 1,
      anon_sym_SLASH,
    ACTIONS(442), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(446), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(438), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 4,
      anon_sym_COMMA,
      anon_sym_RBRACK,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5330] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(448), 1,
      anon_sym_LT,
    ACTIONS(450), 1,
      anon_sym_SLASH,
    ACTIONS(446), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(438), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 6,
      anon_sym_COMMA,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5357] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(402), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(386), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5378] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(434), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(432), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5399] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 6,
      anon_sym_COMMA,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_RPAREN,
  [5426] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 4,
      anon_sym_COMMA,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_RPAREN,
  [5455] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(402), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 8,
      anon_sym_COMMA,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_RPAREN,
  [5480] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(474), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(472), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5501] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(486), 1,
      anon_sym_LT,
    ACTIONS(488), 1,
      anon_sym_SLASH,
    ACTIONS(476), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
    ACTIONS(480), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(482), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(484), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(478), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5532] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(448), 1,
      anon_sym_LT,
    ACTIONS(450), 1,
      anon_sym_SLASH,
    ACTIONS(442), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(444), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(446), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(490), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
    ACTIONS(438), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5563] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(422), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(420), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5584] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(384), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(382), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5605] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(400), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(398), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5626] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(426), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(424), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5647] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(474), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(472), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5668] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(458), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(456), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
      anon_sym_RPAREN,
  [5689] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(486), 1,
      anon_sym_LT,
    ACTIONS(488), 1,
      anon_sym_SLASH,
    ACTIONS(480), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(482), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(484), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(490), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
    ACTIONS(478), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5720] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(454), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(452), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5741] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(492), 2,
      anon_sym_COMMA,
      anon_sym_RPAREN,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5772] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(384), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(382), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5793] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(357), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(355), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5814] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(434), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(432), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5835] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(357), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(355), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5856] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(434), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(432), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5877] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(400), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(398), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5898] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(454), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(452), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5919] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(402), 1,
      anon_sym_LT,
    ACTIONS(450), 1,
      anon_sym_SLASH,
    ACTIONS(438), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 8,
      anon_sym_COMMA,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
  [5944] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(458), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(456), 11,
      anon_sym_COMMA,
      anon_sym_STAR,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5965] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(400), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(398), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [5986] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(384), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(382), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6007] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(448), 1,
      anon_sym_LT,
    ACTIONS(450), 1,
      anon_sym_SLASH,
    ACTIONS(442), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(444), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(446), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(494), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
    ACTIONS(438), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6038] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(474), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(472), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6059] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(426), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(424), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6080] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(422), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(420), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6101] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(402), 1,
      anon_sym_LT,
    ACTIONS(488), 1,
      anon_sym_SLASH,
    ACTIONS(478), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 8,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
  [6126] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(486), 1,
      anon_sym_LT,
    ACTIONS(488), 1,
      anon_sym_SLASH,
    ACTIONS(480), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(484), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(478), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 4,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [6155] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(402), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(386), 11,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_STAR,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6176] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(486), 1,
      anon_sym_LT,
    ACTIONS(488), 1,
      anon_sym_SLASH,
    ACTIONS(484), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(478), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(386), 6,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [6203] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(496), 1,
      anon_sym_RPAREN,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6233] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(498), 1,
      anon_sym_RPAREN,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6263] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(500), 1,
      anon_sym_RPAREN,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6293] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 1,
      anon_sym_LT,
    ACTIONS(416), 1,
      anon_sym_SLASH,
    ACTIONS(502), 1,
      anon_sym_RPAREN,
    ACTIONS(408), 2,
      anon_sym_PIPE,
      anon_sym_AMP,
    ACTIONS(410), 2,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
    ACTIONS(412), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(406), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
  [6323] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(506), 1,
      anon_sym_RBRACE,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6352] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(512), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6381] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(514), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6410] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(516), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6439] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(518), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(261), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6468] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(520), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(249), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6497] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(522), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6526] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(524), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6555] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(526), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6584] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(528), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(262), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6613] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(530), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6642] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    ACTIONS(532), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(255), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6671] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(504), 1,
      sym_name,
    ACTIONS(508), 1,
      anon_sym_constraint,
    ACTIONS(510), 1,
      anon_sym_constraints,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(297), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6697] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(534), 1,
      sym_name,
    ACTIONS(536), 1,
      anon_sym_cardinality,
    STATE(250), 1,
      sym_path,
    ACTIONS(538), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(124), 2,
      sym_string_name,
      sym__any_name,
  [6721] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(540), 1,
      sym_name,
    ACTIONS(542), 1,
      anon_sym_cardinality,
    ACTIONS(544), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(259), 2,
      sym_string_name,
      sym__any_name,
  [6742] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(548), 1,
      anon_sym_DOT,
    STATE(227), 1,
      aux_sym_lang_lvl_repeat1,
    ACTIONS(546), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6757] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(552), 1,
      anon_sym_DOT,
    STATE(227), 1,
      aux_sym_lang_lvl_repeat1,
    ACTIONS(550), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6772] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(557), 1,
      anon_sym_DOT,
    STATE(226), 1,
      aux_sym_lang_lvl_repeat1,
    ACTIONS(555), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6787] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(559), 1,
      anon_sym_cardinality,
    ACTIONS(561), 1,
      anon_sym_LBRACE,
    ACTIONS(563), 1,
      sym__newline,
    STATE(35), 1,
      sym_attributes,
  [6803] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(550), 4,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_DOT,
  [6813] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(246), 1,
      anon_sym_DQUOTE,
    ACTIONS(330), 1,
      sym_name,
    STATE(146), 2,
      sym_string_name,
      sym__any_name,
  [6827] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(565), 1,
      sym_name,
    STATE(123), 2,
      sym_string_name,
      sym__any_name,
  [6841] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(286), 1,
      anon_sym_DQUOTE,
    ACTIONS(328), 1,
      sym_name,
    STATE(148), 2,
      sym_string_name,
      sym__any_name,
  [6855] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(567), 1,
      anon_sym_cardinality,
    ACTIONS(569), 1,
      anon_sym_LBRACE,
    ACTIONS(571), 1,
      sym__newline,
    STATE(22), 1,
      sym_attributes,
  [6871] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(326), 1,
      sym_name,
    STATE(155), 2,
      sym_string_name,
      sym__any_name,
  [6885] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(550), 4,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_DOT,
  [6895] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(573), 4,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_DOT,
  [6905] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(575), 4,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_DOT,
  [6915] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(577), 1,
      anon_sym_COMMA,
    ACTIONS(579), 1,
      anon_sym_RPAREN,
    STATE(247), 1,
      aux_sym_function_repeat1,
  [6928] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(581), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6937] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(583), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6946] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(585), 1,
      anon_sym_COMMA,
    ACTIONS(588), 1,
      anon_sym_RBRACK,
    STATE(242), 1,
      aux_sym_vector_repeat1,
  [6959] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(590), 1,
      anon_sym_COMMA,
    ACTIONS(592), 1,
      anon_sym_RBRACE,
    STATE(252), 1,
      aux_sym_attributes_repeat1,
  [6972] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(594), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6981] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(596), 1,
      anon_sym_COMMA,
    ACTIONS(598), 1,
      anon_sym_RBRACE,
    STATE(252), 1,
      aux_sym_attributes_repeat1,
  [6994] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(600), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [7003] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(602), 1,
      anon_sym_COMMA,
    ACTIONS(605), 1,
      anon_sym_RPAREN,
    STATE(247), 1,
      aux_sym_function_repeat1,
  [7016] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(607), 1,
      anon_sym_COMMA,
    ACTIONS(609), 1,
      anon_sym_RPAREN,
    STATE(247), 1,
      aux_sym_function_repeat1,
  [7029] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(611), 1,
      anon_sym_COMMA,
    ACTIONS(613), 1,
      anon_sym_RBRACE,
    STATE(245), 1,
      aux_sym_attributes_repeat1,
  [7042] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(615), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [7051] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(617), 1,
      anon_sym_COMMA,
    ACTIONS(619), 1,
      anon_sym_RBRACE,
    STATE(252), 1,
      aux_sym_attributes_repeat1,
  [7064] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(621), 1,
      anon_sym_COMMA,
    ACTIONS(624), 1,
      anon_sym_RBRACE,
    STATE(252), 1,
      aux_sym_attributes_repeat1,
  [7077] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(626), 1,
      anon_sym_COMMA,
    ACTIONS(628), 1,
      anon_sym_RBRACK,
    STATE(266), 1,
      aux_sym_vector_repeat1,
  [7090] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(630), 1,
      anon_sym_COMMA,
    ACTIONS(632), 1,
      anon_sym_RPAREN,
    STATE(247), 1,
      aux_sym_function_repeat1,
  [7103] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(634), 1,
      anon_sym_COMMA,
    ACTIONS(636), 1,
      anon_sym_RBRACE,
    STATE(251), 1,
      aux_sym_attributes_repeat1,
  [7116] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(638), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [7125] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(640), 1,
      anon_sym_COMMA,
    ACTIONS(642), 1,
      anon_sym_RBRACK,
    STATE(263), 1,
      aux_sym_attribute_constraints_repeat1,
  [7138] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(644), 1,
      anon_sym_COMMA,
    ACTIONS(646), 1,
      anon_sym_RBRACK,
    STATE(242), 1,
      aux_sym_vector_repeat1,
  [7151] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(648), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [7160] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(561), 1,
      anon_sym_LBRACE,
    ACTIONS(650), 1,
      sym__newline,
    STATE(38), 1,
      sym_attributes,
  [7173] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(652), 1,
      anon_sym_COMMA,
    ACTIONS(654), 1,
      anon_sym_RBRACE,
    STATE(267), 1,
      aux_sym_attributes_repeat1,
  [7186] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(656), 1,
      anon_sym_COMMA,
    ACTIONS(658), 1,
      anon_sym_RBRACE,
    STATE(243), 1,
      aux_sym_attributes_repeat1,
  [7199] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(660), 1,
      anon_sym_COMMA,
    ACTIONS(663), 1,
      anon_sym_RBRACK,
    STATE(263), 1,
      aux_sym_attribute_constraints_repeat1,
  [7212] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(665), 1,
      anon_sym_COMMA,
    ACTIONS(667), 1,
      anon_sym_RPAREN,
    STATE(247), 1,
      aux_sym_function_repeat1,
  [7225] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(569), 1,
      anon_sym_LBRACE,
    ACTIONS(669), 1,
      sym__newline,
    STATE(24), 1,
      sym_attributes,
  [7238] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(671), 1,
      anon_sym_COMMA,
    ACTIONS(673), 1,
      anon_sym_RBRACK,
    STATE(242), 1,
      aux_sym_vector_repeat1,
  [7251] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(675), 1,
      anon_sym_COMMA,
    ACTIONS(677), 1,
      anon_sym_RBRACE,
    STATE(252), 1,
      aux_sym_attributes_repeat1,
  [7264] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(679), 1,
      anon_sym_COMMA,
    ACTIONS(681), 1,
      anon_sym_RBRACK,
    STATE(258), 1,
      aux_sym_vector_repeat1,
  [7277] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(142), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7285] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(683), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7293] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(685), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7301] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(687), 1,
      anon_sym_STAR,
    ACTIONS(689), 1,
      sym_int,
  [7311] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(691), 2,
      anon_sym_STAR,
      sym_int,
  [7319] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(693), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7327] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(695), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7335] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(588), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7343] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(11), 1,
      anon_sym_LBRACK,
    STATE(265), 1,
      sym_cardinality,
  [7353] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(697), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7361] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(130), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7369] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(699), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7377] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(701), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7385] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(683), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7393] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(703), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7401] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(150), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7409] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(11), 1,
      anon_sym_LBRACK,
    STATE(260), 1,
      sym_cardinality,
  [7419] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(705), 1,
      anon_sym_DOT_DOT,
    ACTIONS(707), 1,
      anon_sym_RBRACK,
  [7429] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(152), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7437] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(699), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7445] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(709), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7453] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(144), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7461] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(695), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7469] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(142), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7477] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(685), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7485] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(130), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7493] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(152), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7501] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(150), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7509] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(624), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7517] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(144), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7525] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(711), 1,
      anon_sym_SQUOTE,
  [7532] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(713), 1,
      anon_sym_DQUOTE,
  [7539] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(715), 1,
      anon_sym_LBRACK,
  [7546] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(717), 1,
      anon_sym_DQUOTE,
  [7553] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(719), 1,
      ts_builtin_sym_end,
  [7560] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(707), 1,
      anon_sym_RBRACK,
  [7567] = 2,
    ACTIONS(721), 1,
      sym_comment,
    ACTIONS(723), 1,
      aux_sym_string_name_token1,
  [7574] = 2,
    ACTIONS(721), 1,
      sym_comment,
    ACTIONS(725), 1,
      sym_string_content,
  [7581] = 2,
    ACTIONS(721), 1,
      sym_comment,
    ACTIONS(727), 1,
      aux_sym_string_name_token1,
  [7588] = 2,
    ACTIONS(721), 1,
      sym_comment,
    ACTIONS(729), 1,
      sym_string_content,
  [7595] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(731), 1,
      anon_sym_SQUOTE,
  [7602] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(733), 1,
      anon_sym_RBRACK,
  [7609] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(735), 1,
      anon_sym_DQUOTE,
  [7616] = 2,
    ACTIONS(721), 1,
      sym_comment,
    ACTIONS(737), 1,
      sym_string_content,
  [7623] = 2,
    ACTIONS(721), 1,
      sym_comment,
    ACTIONS(739), 1,
      aux_sym_string_name_token1,
  [7630] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(741), 1,
      anon_sym_SQUOTE,
  [7637] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(743), 1,
      anon_sym_SQUOTE,
  [7644] = 2,
    ACTIONS(721), 1,
      sym_comment,
    ACTIONS(745), 1,
      sym_string_content,
  [7651] = 2,
    ACTIONS(721), 1,
      sym_comment,
    ACTIONS(747), 1,
      aux_sym_string_name_token1,
  [7658] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(749), 1,
      anon_sym_DQUOTE,
};

static const uint32_t ts_small_parse_table_map[] = {
  [SMALL_STATE(21)] = 0,
  [SMALL_STATE(22)] = 40,
  [SMALL_STATE(23)] = 80,
  [SMALL_STATE(24)] = 118,
  [SMALL_STATE(25)] = 158,
  [SMALL_STATE(26)] = 196,
  [SMALL_STATE(27)] = 234,
  [SMALL_STATE(28)] = 272,
  [SMALL_STATE(29)] = 310,
  [SMALL_STATE(30)] = 348,
  [SMALL_STATE(31)] = 386,
  [SMALL_STATE(32)] = 424,
  [SMALL_STATE(33)] = 462,
  [SMALL_STATE(34)] = 500,
  [SMALL_STATE(35)] = 550,
  [SMALL_STATE(36)] = 590,
  [SMALL_STATE(37)] = 630,
  [SMALL_STATE(38)] = 670,
  [SMALL_STATE(39)] = 710,
  [SMALL_STATE(40)] = 750,
  [SMALL_STATE(41)] = 787,
  [SMALL_STATE(42)] = 824,
  [SMALL_STATE(43)] = 861,
  [SMALL_STATE(44)] = 898,
  [SMALL_STATE(45)] = 935,
  [SMALL_STATE(46)] = 972,
  [SMALL_STATE(47)] = 1009,
  [SMALL_STATE(48)] = 1046,
  [SMALL_STATE(49)] = 1083,
  [SMALL_STATE(50)] = 1120,
  [SMALL_STATE(51)] = 1157,
  [SMALL_STATE(52)] = 1194,
  [SMALL_STATE(53)] = 1231,
  [SMALL_STATE(54)] = 1268,
  [SMALL_STATE(55)] = 1305,
  [SMALL_STATE(56)] = 1342,
  [SMALL_STATE(57)] = 1399,
  [SMALL_STATE(58)] = 1455,
  [SMALL_STATE(59)] = 1487,
  [SMALL_STATE(60)] = 1543,
  [SMALL_STATE(61)] = 1599,
  [SMALL_STATE(62)] = 1655,
  [SMALL_STATE(63)] = 1708,
  [SMALL_STATE(64)] = 1761,
  [SMALL_STATE(65)] = 1814,
  [SMALL_STATE(66)] = 1860,
  [SMALL_STATE(67)] = 1905,
  [SMALL_STATE(68)] = 1950,
  [SMALL_STATE(69)] = 1995,
  [SMALL_STATE(70)] = 2034,
  [SMALL_STATE(71)] = 2063,
  [SMALL_STATE(72)] = 2108,
  [SMALL_STATE(73)] = 2141,
  [SMALL_STATE(74)] = 2186,
  [SMALL_STATE(75)] = 2231,
  [SMALL_STATE(76)] = 2276,
  [SMALL_STATE(77)] = 2321,
  [SMALL_STATE(78)] = 2366,
  [SMALL_STATE(79)] = 2405,
  [SMALL_STATE(80)] = 2450,
  [SMALL_STATE(81)] = 2492,
  [SMALL_STATE(82)] = 2534,
  [SMALL_STATE(83)] = 2576,
  [SMALL_STATE(84)] = 2618,
  [SMALL_STATE(85)] = 2660,
  [SMALL_STATE(86)] = 2702,
  [SMALL_STATE(87)] = 2744,
  [SMALL_STATE(88)] = 2786,
  [SMALL_STATE(89)] = 2828,
  [SMALL_STATE(90)] = 2870,
  [SMALL_STATE(91)] = 2912,
  [SMALL_STATE(92)] = 2954,
  [SMALL_STATE(93)] = 2996,
  [SMALL_STATE(94)] = 3038,
  [SMALL_STATE(95)] = 3080,
  [SMALL_STATE(96)] = 3122,
  [SMALL_STATE(97)] = 3164,
  [SMALL_STATE(98)] = 3206,
  [SMALL_STATE(99)] = 3248,
  [SMALL_STATE(100)] = 3290,
  [SMALL_STATE(101)] = 3332,
  [SMALL_STATE(102)] = 3374,
  [SMALL_STATE(103)] = 3416,
  [SMALL_STATE(104)] = 3458,
  [SMALL_STATE(105)] = 3500,
  [SMALL_STATE(106)] = 3542,
  [SMALL_STATE(107)] = 3584,
  [SMALL_STATE(108)] = 3626,
  [SMALL_STATE(109)] = 3658,
  [SMALL_STATE(110)] = 3684,
  [SMALL_STATE(111)] = 3726,
  [SMALL_STATE(112)] = 3768,
  [SMALL_STATE(113)] = 3810,
  [SMALL_STATE(114)] = 3852,
  [SMALL_STATE(115)] = 3883,
  [SMALL_STATE(116)] = 3914,
  [SMALL_STATE(117)] = 3945,
  [SMALL_STATE(118)] = 3976,
  [SMALL_STATE(119)] = 4007,
  [SMALL_STATE(120)] = 4038,
  [SMALL_STATE(121)] = 4067,
  [SMALL_STATE(122)] = 4096,
  [SMALL_STATE(123)] = 4128,
  [SMALL_STATE(124)] = 4152,
  [SMALL_STATE(125)] = 4180,
  [SMALL_STATE(126)] = 4204,
  [SMALL_STATE(127)] = 4229,
  [SMALL_STATE(128)] = 4254,
  [SMALL_STATE(129)] = 4281,
  [SMALL_STATE(130)] = 4308,
  [SMALL_STATE(131)] = 4335,
  [SMALL_STATE(132)] = 4362,
  [SMALL_STATE(133)] = 4389,
  [SMALL_STATE(134)] = 4416,
  [SMALL_STATE(135)] = 4443,
  [SMALL_STATE(136)] = 4470,
  [SMALL_STATE(137)] = 4495,
  [SMALL_STATE(138)] = 4522,
  [SMALL_STATE(139)] = 4549,
  [SMALL_STATE(140)] = 4571,
  [SMALL_STATE(141)] = 4601,
  [SMALL_STATE(142)] = 4623,
  [SMALL_STATE(143)] = 4649,
  [SMALL_STATE(144)] = 4685,
  [SMALL_STATE(145)] = 4707,
  [SMALL_STATE(146)] = 4729,
  [SMALL_STATE(147)] = 4751,
  [SMALL_STATE(148)] = 4787,
  [SMALL_STATE(149)] = 4809,
  [SMALL_STATE(150)] = 4831,
  [SMALL_STATE(151)] = 4859,
  [SMALL_STATE(152)] = 4881,
  [SMALL_STATE(153)] = 4917,
  [SMALL_STATE(154)] = 4939,
  [SMALL_STATE(155)] = 4961,
  [SMALL_STATE(156)] = 4983,
  [SMALL_STATE(157)] = 5005,
  [SMALL_STATE(158)] = 5027,
  [SMALL_STATE(159)] = 5063,
  [SMALL_STATE(160)] = 5085,
  [SMALL_STATE(161)] = 5117,
  [SMALL_STATE(162)] = 5153,
  [SMALL_STATE(163)] = 5175,
  [SMALL_STATE(164)] = 5196,
  [SMALL_STATE(165)] = 5217,
  [SMALL_STATE(166)] = 5238,
  [SMALL_STATE(167)] = 5259,
  [SMALL_STATE(168)] = 5280,
  [SMALL_STATE(169)] = 5301,
  [SMALL_STATE(170)] = 5330,
  [SMALL_STATE(171)] = 5357,
  [SMALL_STATE(172)] = 5378,
  [SMALL_STATE(173)] = 5399,
  [SMALL_STATE(174)] = 5426,
  [SMALL_STATE(175)] = 5455,
  [SMALL_STATE(176)] = 5480,
  [SMALL_STATE(177)] = 5501,
  [SMALL_STATE(178)] = 5532,
  [SMALL_STATE(179)] = 5563,
  [SMALL_STATE(180)] = 5584,
  [SMALL_STATE(181)] = 5605,
  [SMALL_STATE(182)] = 5626,
  [SMALL_STATE(183)] = 5647,
  [SMALL_STATE(184)] = 5668,
  [SMALL_STATE(185)] = 5689,
  [SMALL_STATE(186)] = 5720,
  [SMALL_STATE(187)] = 5741,
  [SMALL_STATE(188)] = 5772,
  [SMALL_STATE(189)] = 5793,
  [SMALL_STATE(190)] = 5814,
  [SMALL_STATE(191)] = 5835,
  [SMALL_STATE(192)] = 5856,
  [SMALL_STATE(193)] = 5877,
  [SMALL_STATE(194)] = 5898,
  [SMALL_STATE(195)] = 5919,
  [SMALL_STATE(196)] = 5944,
  [SMALL_STATE(197)] = 5965,
  [SMALL_STATE(198)] = 5986,
  [SMALL_STATE(199)] = 6007,
  [SMALL_STATE(200)] = 6038,
  [SMALL_STATE(201)] = 6059,
  [SMALL_STATE(202)] = 6080,
  [SMALL_STATE(203)] = 6101,
  [SMALL_STATE(204)] = 6126,
  [SMALL_STATE(205)] = 6155,
  [SMALL_STATE(206)] = 6176,
  [SMALL_STATE(207)] = 6203,
  [SMALL_STATE(208)] = 6233,
  [SMALL_STATE(209)] = 6263,
  [SMALL_STATE(210)] = 6293,
  [SMALL_STATE(211)] = 6323,
  [SMALL_STATE(212)] = 6352,
  [SMALL_STATE(213)] = 6381,
  [SMALL_STATE(214)] = 6410,
  [SMALL_STATE(215)] = 6439,
  [SMALL_STATE(216)] = 6468,
  [SMALL_STATE(217)] = 6497,
  [SMALL_STATE(218)] = 6526,
  [SMALL_STATE(219)] = 6555,
  [SMALL_STATE(220)] = 6584,
  [SMALL_STATE(221)] = 6613,
  [SMALL_STATE(222)] = 6642,
  [SMALL_STATE(223)] = 6671,
  [SMALL_STATE(224)] = 6697,
  [SMALL_STATE(225)] = 6721,
  [SMALL_STATE(226)] = 6742,
  [SMALL_STATE(227)] = 6757,
  [SMALL_STATE(228)] = 6772,
  [SMALL_STATE(229)] = 6787,
  [SMALL_STATE(230)] = 6803,
  [SMALL_STATE(231)] = 6813,
  [SMALL_STATE(232)] = 6827,
  [SMALL_STATE(233)] = 6841,
  [SMALL_STATE(234)] = 6855,
  [SMALL_STATE(235)] = 6871,
  [SMALL_STATE(236)] = 6885,
  [SMALL_STATE(237)] = 6895,
  [SMALL_STATE(238)] = 6905,
  [SMALL_STATE(239)] = 6915,
  [SMALL_STATE(240)] = 6928,
  [SMALL_STATE(241)] = 6937,
  [SMALL_STATE(242)] = 6946,
  [SMALL_STATE(243)] = 6959,
  [SMALL_STATE(244)] = 6972,
  [SMALL_STATE(245)] = 6981,
  [SMALL_STATE(246)] = 6994,
  [SMALL_STATE(247)] = 7003,
  [SMALL_STATE(248)] = 7016,
  [SMALL_STATE(249)] = 7029,
  [SMALL_STATE(250)] = 7042,
  [SMALL_STATE(251)] = 7051,
  [SMALL_STATE(252)] = 7064,
  [SMALL_STATE(253)] = 7077,
  [SMALL_STATE(254)] = 7090,
  [SMALL_STATE(255)] = 7103,
  [SMALL_STATE(256)] = 7116,
  [SMALL_STATE(257)] = 7125,
  [SMALL_STATE(258)] = 7138,
  [SMALL_STATE(259)] = 7151,
  [SMALL_STATE(260)] = 7160,
  [SMALL_STATE(261)] = 7173,
  [SMALL_STATE(262)] = 7186,
  [SMALL_STATE(263)] = 7199,
  [SMALL_STATE(264)] = 7212,
  [SMALL_STATE(265)] = 7225,
  [SMALL_STATE(266)] = 7238,
  [SMALL_STATE(267)] = 7251,
  [SMALL_STATE(268)] = 7264,
  [SMALL_STATE(269)] = 7277,
  [SMALL_STATE(270)] = 7285,
  [SMALL_STATE(271)] = 7293,
  [SMALL_STATE(272)] = 7301,
  [SMALL_STATE(273)] = 7311,
  [SMALL_STATE(274)] = 7319,
  [SMALL_STATE(275)] = 7327,
  [SMALL_STATE(276)] = 7335,
  [SMALL_STATE(277)] = 7343,
  [SMALL_STATE(278)] = 7353,
  [SMALL_STATE(279)] = 7361,
  [SMALL_STATE(280)] = 7369,
  [SMALL_STATE(281)] = 7377,
  [SMALL_STATE(282)] = 7385,
  [SMALL_STATE(283)] = 7393,
  [SMALL_STATE(284)] = 7401,
  [SMALL_STATE(285)] = 7409,
  [SMALL_STATE(286)] = 7419,
  [SMALL_STATE(287)] = 7429,
  [SMALL_STATE(288)] = 7437,
  [SMALL_STATE(289)] = 7445,
  [SMALL_STATE(290)] = 7453,
  [SMALL_STATE(291)] = 7461,
  [SMALL_STATE(292)] = 7469,
  [SMALL_STATE(293)] = 7477,
  [SMALL_STATE(294)] = 7485,
  [SMALL_STATE(295)] = 7493,
  [SMALL_STATE(296)] = 7501,
  [SMALL_STATE(297)] = 7509,
  [SMALL_STATE(298)] = 7517,
  [SMALL_STATE(299)] = 7525,
  [SMALL_STATE(300)] = 7532,
  [SMALL_STATE(301)] = 7539,
  [SMALL_STATE(302)] = 7546,
  [SMALL_STATE(303)] = 7553,
  [SMALL_STATE(304)] = 7560,
  [SMALL_STATE(305)] = 7567,
  [SMALL_STATE(306)] = 7574,
  [SMALL_STATE(307)] = 7581,
  [SMALL_STATE(308)] = 7588,
  [SMALL_STATE(309)] = 7595,
  [SMALL_STATE(310)] = 7602,
  [SMALL_STATE(311)] = 7609,
  [SMALL_STATE(312)] = 7616,
  [SMALL_STATE(313)] = 7623,
  [SMALL_STATE(314)] = 7630,
  [SMALL_STATE(315)] = 7637,
  [SMALL_STATE(316)] = 7644,
  [SMALL_STATE(317)] = 7651,
  [SMALL_STATE(318)] = 7658,
};

static const TSParseActionEntry ts_parse_actions[] = {
  [0] = {.entry = {.count = 0, .reusable = false}},
  [1] = {.entry = {.count = 1, .reusable = false}}, RECOVER(),
  [3] = {.entry = {.count = 1, .reusable = true}}, SHIFT_EXTRA(),
  [5] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_source_file, 0),
  [7] = {.entry = {.count = 1, .reusable = false}}, SHIFT(70),
  [9] = {.entry = {.count = 1, .reusable = false}}, SHIFT(224),
  [11] = {.entry = {.count = 1, .reusable = true}}, SHIFT(272),
  [13] = {.entry = {.count = 1, .reusable = true}}, SHIFT(238),
  [15] = {.entry = {.count = 1, .reusable = false}}, SHIFT(241),
  [17] = {.entry = {.count = 1, .reusable = true}}, SHIFT(113),
  [19] = {.entry = {.count = 1, .reusable = true}}, SHIFT(102),
  [21] = {.entry = {.count = 1, .reusable = false}}, SHIFT(151),
  [23] = {.entry = {.count = 1, .reusable = true}}, SHIFT(149),
  [25] = {.entry = {.count = 1, .reusable = false}}, SHIFT(244),
  [27] = {.entry = {.count = 1, .reusable = true}}, SHIFT(237),
  [29] = {.entry = {.count = 1, .reusable = true}}, SHIFT(308),
  [31] = {.entry = {.count = 1, .reusable = true}}, SHIFT(305),
  [33] = {.entry = {.count = 1, .reusable = false}}, SHIFT(234),
  [35] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2),
  [37] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(70),
  [40] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(224),
  [43] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(272),
  [46] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(238),
  [49] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(241),
  [52] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(113),
  [55] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(102),
  [58] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(151),
  [61] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(149),
  [64] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(244),
  [67] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(237),
  [70] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(308),
  [73] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(305),
  [76] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(234),
  [79] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(229),
  [82] = {.entry = {.count = 1, .reusable = false}}, SHIFT(229),
  [84] = {.entry = {.count = 1, .reusable = true}}, SHIFT(52),
  [86] = {.entry = {.count = 1, .reusable = true}}, SHIFT(53),
  [88] = {.entry = {.count = 1, .reusable = true}}, SHIFT(51),
  [90] = {.entry = {.count = 1, .reusable = true}}, SHIFT(40),
  [92] = {.entry = {.count = 1, .reusable = true}}, SHIFT(42),
  [94] = {.entry = {.count = 1, .reusable = true}}, SHIFT(54),
  [96] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_source_file, 1),
  [98] = {.entry = {.count = 1, .reusable = true}}, SHIFT(45),
  [100] = {.entry = {.count = 1, .reusable = true}}, SHIFT(55),
  [102] = {.entry = {.count = 1, .reusable = true}}, SHIFT(46),
  [104] = {.entry = {.count = 1, .reusable = true}}, SHIFT(43),
  [106] = {.entry = {.count = 1, .reusable = true}}, SHIFT(44),
  [108] = {.entry = {.count = 1, .reusable = true}}, SHIFT(49),
  [110] = {.entry = {.count = 1, .reusable = true}}, SHIFT(41),
  [112] = {.entry = {.count = 1, .reusable = true}}, SHIFT(48),
  [114] = {.entry = {.count = 1, .reusable = true}}, SHIFT(50),
  [116] = {.entry = {.count = 1, .reusable = true}}, SHIFT(47),
  [118] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 4, .production_id = 16),
  [120] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 4, .production_id = 16),
  [122] = {.entry = {.count = 1, .reusable = true}}, SHIFT(7),
  [124] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 2, .production_id = 6),
  [126] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 2, .production_id = 6),
  [128] = {.entry = {.count = 1, .reusable = true}}, SHIFT(18),
  [130] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 3),
  [132] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 3),
  [134] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 4, .production_id = 17),
  [136] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 4, .production_id = 17),
  [138] = {.entry = {.count = 1, .reusable = true}}, SHIFT(6),
  [140] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 5, .production_id = 33),
  [142] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 5, .production_id = 33),
  [144] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 4, .production_id = 13),
  [146] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 4, .production_id = 13),
  [148] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 4),
  [150] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 4),
  [152] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 2),
  [154] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 2),
  [156] = {.entry = {.count = 1, .reusable = false}}, SHIFT(125),
  [158] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_path, 2, .production_id = 7),
  [160] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_path, 2, .production_id = 7),
  [162] = {.entry = {.count = 1, .reusable = true}}, SHIFT(9),
  [164] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 2, .production_id = 5),
  [166] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 2, .production_id = 5),
  [168] = {.entry = {.count = 1, .reusable = true}}, SHIFT(11),
  [170] = {.entry = {.count = 1, .reusable = true}}, SHIFT(15),
  [172] = {.entry = {.count = 1, .reusable = true}}, SHIFT(14),
  [174] = {.entry = {.count = 1, .reusable = true}}, SHIFT(16),
  [176] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 6, .production_id = 30),
  [178] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 6, .production_id = 30),
  [180] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 5, .production_id = 27),
  [182] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 5, .production_id = 27),
  [184] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 5, .production_id = 28),
  [186] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 5, .production_id = 28),
  [188] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 6, .production_id = 31),
  [190] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 6, .production_id = 31),
  [192] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 4, .production_id = 15),
  [194] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 4, .production_id = 15),
  [196] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 7, .production_id = 34),
  [198] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 7, .production_id = 34),
  [200] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 4, .production_id = 21),
  [202] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 4, .production_id = 21),
  [204] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 7, .production_id = 35),
  [206] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 7, .production_id = 35),
  [208] = {.entry = {.count = 1, .reusable = false}}, SHIFT(136),
  [210] = {.entry = {.count = 1, .reusable = true}}, SHIFT(215),
  [212] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_value, 1, .production_id = 10),
  [214] = {.entry = {.count = 1, .reusable = true}}, SHIFT(63),
  [216] = {.entry = {.count = 1, .reusable = true}}, SHIFT(95),
  [218] = {.entry = {.count = 1, .reusable = true}}, SHIFT(111),
  [220] = {.entry = {.count = 1, .reusable = false}}, SHIFT(190),
  [222] = {.entry = {.count = 1, .reusable = true}}, SHIFT(191),
  [224] = {.entry = {.count = 1, .reusable = true}}, SHIFT(312),
  [226] = {.entry = {.count = 1, .reusable = true}}, SHIFT(313),
  [228] = {.entry = {.count = 1, .reusable = false}}, SHIFT(127),
  [230] = {.entry = {.count = 1, .reusable = true}}, SHIFT(216),
  [232] = {.entry = {.count = 1, .reusable = true}}, SHIFT(62),
  [234] = {.entry = {.count = 1, .reusable = true}}, SHIFT(275),
  [236] = {.entry = {.count = 1, .reusable = true}}, SHIFT(84),
  [238] = {.entry = {.count = 1, .reusable = true}}, SHIFT(83),
  [240] = {.entry = {.count = 1, .reusable = false}}, SHIFT(192),
  [242] = {.entry = {.count = 1, .reusable = true}}, SHIFT(189),
  [244] = {.entry = {.count = 1, .reusable = true}}, SHIFT(316),
  [246] = {.entry = {.count = 1, .reusable = true}}, SHIFT(317),
  [248] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_string_name, 3),
  [250] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_string_name, 3),
  [252] = {.entry = {.count = 1, .reusable = true}}, SHIFT(282),
  [254] = {.entry = {.count = 1, .reusable = true}}, SHIFT(291),
  [256] = {.entry = {.count = 1, .reusable = true}}, SHIFT(270),
  [258] = {.entry = {.count = 1, .reusable = false}}, SHIFT(256),
  [260] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym__header, 1),
  [262] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__header, 1),
  [264] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_path, 1),
  [266] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_path, 1),
  [268] = {.entry = {.count = 1, .reusable = true}}, SHIFT(34),
  [270] = {.entry = {.count = 1, .reusable = true}}, SHIFT(274),
  [272] = {.entry = {.count = 1, .reusable = false}}, SHIFT(126),
  [274] = {.entry = {.count = 1, .reusable = true}}, SHIFT(107),
  [276] = {.entry = {.count = 1, .reusable = true}}, SHIFT(82),
  [278] = {.entry = {.count = 1, .reusable = true}}, SHIFT(180),
  [280] = {.entry = {.count = 1, .reusable = false}}, SHIFT(172),
  [282] = {.entry = {.count = 1, .reusable = true}}, SHIFT(165),
  [284] = {.entry = {.count = 1, .reusable = true}}, SHIFT(306),
  [286] = {.entry = {.count = 1, .reusable = true}}, SHIFT(307),
  [288] = {.entry = {.count = 1, .reusable = true}}, SHIFT(188),
  [290] = {.entry = {.count = 1, .reusable = false}}, SHIFT(236),
  [292] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_lang_lvl, 3, .production_id = 13),
  [294] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_lang_lvl, 3, .production_id = 13),
  [296] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym__any_name, 1),
  [298] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__any_name, 1),
  [300] = {.entry = {.count = 1, .reusable = true}}, SHIFT(96),
  [302] = {.entry = {.count = 1, .reusable = true}}, SHIFT(164),
  [304] = {.entry = {.count = 1, .reusable = false}}, SHIFT(123),
  [306] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_path, 3, .production_id = 13),
  [308] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_path, 3, .production_id = 13),
  [310] = {.entry = {.count = 1, .reusable = true}}, SHIFT(196),
  [312] = {.entry = {.count = 1, .reusable = true}}, SHIFT(156),
  [314] = {.entry = {.count = 1, .reusable = true}}, SHIFT(184),
  [316] = {.entry = {.count = 1, .reusable = true}}, SHIFT(139),
  [318] = {.entry = {.count = 1, .reusable = true}}, SHIFT(198),
  [320] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_lang_lvl, 2, .production_id = 7),
  [322] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_lang_lvl, 2, .production_id = 7),
  [324] = {.entry = {.count = 1, .reusable = true}}, SHIFT(278),
  [326] = {.entry = {.count = 1, .reusable = true}}, SHIFT(155),
  [328] = {.entry = {.count = 1, .reusable = true}}, SHIFT(148),
  [330] = {.entry = {.count = 1, .reusable = true}}, SHIFT(146),
  [332] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2),
  [334] = {.entry = {.count = 1, .reusable = false}}, REDUCE(aux_sym_path_repeat1, 2),
  [336] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2), SHIFT_REPEAT(232),
  [339] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_path, 2),
  [341] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_path, 2),
  [343] = {.entry = {.count = 1, .reusable = true}}, SHIFT(72),
  [345] = {.entry = {.count = 1, .reusable = true}}, SHIFT(108),
  [347] = {.entry = {.count = 1, .reusable = true}}, SHIFT(97),
  [349] = {.entry = {.count = 1, .reusable = true}}, SHIFT(91),
  [351] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_ref, 1, .production_id = 2),
  [353] = {.entry = {.count = 1, .reusable = true}}, SHIFT(225),
  [355] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__expr, 1),
  [357] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym__expr, 1),
  [359] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2), SHIFT_REPEAT(235),
  [362] = {.entry = {.count = 1, .reusable = true}}, SHIFT(119),
  [364] = {.entry = {.count = 1, .reusable = true}}, SHIFT(115),
  [366] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2), SHIFT_REPEAT(231),
  [369] = {.entry = {.count = 1, .reusable = true}}, SHIFT(118),
  [371] = {.entry = {.count = 1, .reusable = true}}, SHIFT(114),
  [373] = {.entry = {.count = 1, .reusable = true}}, SHIFT(117),
  [375] = {.entry = {.count = 1, .reusable = true}}, SHIFT(85),
  [377] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2), SHIFT_REPEAT(233),
  [380] = {.entry = {.count = 1, .reusable = true}}, SHIFT(116),
  [382] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_function, 5, .production_id = 23),
  [384] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_function, 5, .production_id = 23),
  [386] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_binary_expr, 3, .production_id = 11),
  [388] = {.entry = {.count = 1, .reusable = true}}, SHIFT(81),
  [390] = {.entry = {.count = 1, .reusable = true}}, SHIFT(98),
  [392] = {.entry = {.count = 1, .reusable = true}}, SHIFT(101),
  [394] = {.entry = {.count = 1, .reusable = false}}, SHIFT(101),
  [396] = {.entry = {.count = 1, .reusable = false}}, SHIFT(81),
  [398] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_function, 5, .production_id = 25),
  [400] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_function, 5, .production_id = 25),
  [402] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_binary_expr, 3, .production_id = 11),
  [404] = {.entry = {.count = 1, .reusable = true}}, SHIFT(76),
  [406] = {.entry = {.count = 1, .reusable = true}}, SHIFT(94),
  [408] = {.entry = {.count = 1, .reusable = true}}, SHIFT(93),
  [410] = {.entry = {.count = 1, .reusable = true}}, SHIFT(92),
  [412] = {.entry = {.count = 1, .reusable = true}}, SHIFT(87),
  [414] = {.entry = {.count = 1, .reusable = false}}, SHIFT(87),
  [416] = {.entry = {.count = 1, .reusable = false}}, SHIFT(94),
  [418] = {.entry = {.count = 1, .reusable = true}}, SHIFT(162),
  [420] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_string, 3),
  [422] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_string, 3),
  [424] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_nested_expr, 3),
  [426] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_nested_expr, 3),
  [428] = {.entry = {.count = 1, .reusable = true}}, SHIFT(77),
  [430] = {.entry = {.count = 1, .reusable = true}}, SHIFT(200),
  [432] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_bool, 1),
  [434] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_bool, 1),
  [436] = {.entry = {.count = 1, .reusable = true}}, SHIFT(66),
  [438] = {.entry = {.count = 1, .reusable = true}}, SHIFT(80),
  [440] = {.entry = {.count = 1, .reusable = true}}, SHIFT(289),
  [442] = {.entry = {.count = 1, .reusable = true}}, SHIFT(90),
  [444] = {.entry = {.count = 1, .reusable = true}}, SHIFT(89),
  [446] = {.entry = {.count = 1, .reusable = true}}, SHIFT(88),
  [448] = {.entry = {.count = 1, .reusable = false}}, SHIFT(88),
  [450] = {.entry = {.count = 1, .reusable = false}}, SHIFT(80),
  [452] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_unary_expr, 2, .production_id = 4),
  [454] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_unary_expr, 2, .production_id = 4),
  [456] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_function, 6, .production_id = 29),
  [458] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_function, 6, .production_id = 29),
  [460] = {.entry = {.count = 1, .reusable = true}}, SHIFT(67),
  [462] = {.entry = {.count = 1, .reusable = true}}, SHIFT(176),
  [464] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__header, 1, .production_id = 1),
  [466] = {.entry = {.count = 1, .reusable = true}}, SHIFT(99),
  [468] = {.entry = {.count = 1, .reusable = true}}, SHIFT(68),
  [470] = {.entry = {.count = 1, .reusable = true}}, SHIFT(183),
  [472] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_function, 4, .production_id = 14),
  [474] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_function, 4, .production_id = 14),
  [476] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraint, 2, .production_id = 18),
  [478] = {.entry = {.count = 1, .reusable = true}}, SHIFT(103),
  [480] = {.entry = {.count = 1, .reusable = true}}, SHIFT(104),
  [482] = {.entry = {.count = 1, .reusable = true}}, SHIFT(105),
  [484] = {.entry = {.count = 1, .reusable = true}}, SHIFT(106),
  [486] = {.entry = {.count = 1, .reusable = false}}, SHIFT(106),
  [488] = {.entry = {.count = 1, .reusable = false}}, SHIFT(103),
  [490] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__value, 1, .production_id = 20),
  [492] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_function_repeat1, 2, .production_id = 24),
  [494] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_attribute_constraints_repeat1, 2, .production_id = 18),
  [496] = {.entry = {.count = 1, .reusable = true}}, SHIFT(201),
  [498] = {.entry = {.count = 1, .reusable = true}}, SHIFT(182),
  [500] = {.entry = {.count = 1, .reusable = true}}, SHIFT(145),
  [502] = {.entry = {.count = 1, .reusable = true}}, SHIFT(167),
  [504] = {.entry = {.count = 1, .reusable = false}}, SHIFT(56),
  [506] = {.entry = {.count = 1, .reusable = true}}, SHIFT(26),
  [508] = {.entry = {.count = 1, .reusable = false}}, SHIFT(110),
  [510] = {.entry = {.count = 1, .reusable = false}}, SHIFT(301),
  [512] = {.entry = {.count = 1, .reusable = true}}, SHIFT(28),
  [514] = {.entry = {.count = 1, .reusable = true}}, SHIFT(292),
  [516] = {.entry = {.count = 1, .reusable = true}}, SHIFT(290),
  [518] = {.entry = {.count = 1, .reusable = true}}, SHIFT(287),
  [520] = {.entry = {.count = 1, .reusable = true}}, SHIFT(295),
  [522] = {.entry = {.count = 1, .reusable = true}}, SHIFT(269),
  [524] = {.entry = {.count = 1, .reusable = true}}, SHIFT(32),
  [526] = {.entry = {.count = 1, .reusable = true}}, SHIFT(25),
  [528] = {.entry = {.count = 1, .reusable = true}}, SHIFT(31),
  [530] = {.entry = {.count = 1, .reusable = true}}, SHIFT(298),
  [532] = {.entry = {.count = 1, .reusable = true}}, SHIFT(33),
  [534] = {.entry = {.count = 1, .reusable = false}}, SHIFT(124),
  [536] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_incomplete_namespace, 1),
  [538] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_incomplete_namespace, 1),
  [540] = {.entry = {.count = 1, .reusable = false}}, SHIFT(259),
  [542] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_incomplete_ref, 2),
  [544] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_incomplete_ref, 2),
  [546] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_lang_lvl, 2),
  [548] = {.entry = {.count = 1, .reusable = true}}, SHIFT(69),
  [550] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_lang_lvl_repeat1, 2),
  [552] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_lang_lvl_repeat1, 2), SHIFT_REPEAT(122),
  [555] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_lang_lvl, 1),
  [557] = {.entry = {.count = 1, .reusable = true}}, SHIFT(78),
  [559] = {.entry = {.count = 1, .reusable = true}}, SHIFT(285),
  [561] = {.entry = {.count = 1, .reusable = true}}, SHIFT(222),
  [563] = {.entry = {.count = 1, .reusable = true}}, SHIFT(37),
  [565] = {.entry = {.count = 1, .reusable = true}}, SHIFT(123),
  [567] = {.entry = {.count = 1, .reusable = true}}, SHIFT(277),
  [569] = {.entry = {.count = 1, .reusable = true}}, SHIFT(220),
  [571] = {.entry = {.count = 1, .reusable = true}}, SHIFT(36),
  [573] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_major_lvl, 1),
  [575] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_minor_lvl, 1),
  [577] = {.entry = {.count = 1, .reusable = true}}, SHIFT(74),
  [579] = {.entry = {.count = 1, .reusable = true}}, SHIFT(141),
  [581] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_cardinality, 3, .production_id = 9),
  [583] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_constraints, 1),
  [585] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_vector_repeat1, 2), SHIFT_REPEAT(64),
  [588] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_vector_repeat1, 2),
  [590] = {.entry = {.count = 1, .reusable = true}}, SHIFT(218),
  [592] = {.entry = {.count = 1, .reusable = true}}, SHIFT(29),
  [594] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_group_mode, 1),
  [596] = {.entry = {.count = 1, .reusable = true}}, SHIFT(213),
  [598] = {.entry = {.count = 1, .reusable = true}}, SHIFT(284),
  [600] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_cardinality, 5, .production_id = 22),
  [602] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_function_repeat1, 2, .production_id = 26), SHIFT_REPEAT(112),
  [605] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_function_repeat1, 2, .production_id = 26),
  [607] = {.entry = {.count = 1, .reusable = true}}, SHIFT(73),
  [609] = {.entry = {.count = 1, .reusable = true}}, SHIFT(193),
  [611] = {.entry = {.count = 1, .reusable = true}}, SHIFT(214),
  [613] = {.entry = {.count = 1, .reusable = true}}, SHIFT(279),
  [615] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_namespace, 2, .production_id = 3),
  [617] = {.entry = {.count = 1, .reusable = true}}, SHIFT(219),
  [619] = {.entry = {.count = 1, .reusable = true}}, SHIFT(27),
  [621] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_attributes_repeat1, 2), SHIFT_REPEAT(223),
  [624] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_attributes_repeat1, 2),
  [626] = {.entry = {.count = 1, .reusable = true}}, SHIFT(57),
  [628] = {.entry = {.count = 1, .reusable = true}}, SHIFT(271),
  [630] = {.entry = {.count = 1, .reusable = true}}, SHIFT(71),
  [632] = {.entry = {.count = 1, .reusable = true}}, SHIFT(197),
  [634] = {.entry = {.count = 1, .reusable = true}}, SHIFT(212),
  [636] = {.entry = {.count = 1, .reusable = true}}, SHIFT(30),
  [638] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_typed_feature, 2, .production_id = 8),
  [640] = {.entry = {.count = 1, .reusable = true}}, SHIFT(79),
  [642] = {.entry = {.count = 1, .reusable = true}}, SHIFT(283),
  [644] = {.entry = {.count = 1, .reusable = true}}, SHIFT(61),
  [646] = {.entry = {.count = 1, .reusable = true}}, SHIFT(288),
  [648] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_ref, 3, .production_id = 12),
  [650] = {.entry = {.count = 1, .reusable = true}}, SHIFT(39),
  [652] = {.entry = {.count = 1, .reusable = true}}, SHIFT(221),
  [654] = {.entry = {.count = 1, .reusable = true}}, SHIFT(294),
  [656] = {.entry = {.count = 1, .reusable = true}}, SHIFT(211),
  [658] = {.entry = {.count = 1, .reusable = true}}, SHIFT(23),
  [660] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_attribute_constraints_repeat1, 2), SHIFT_REPEAT(100),
  [663] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_attribute_constraints_repeat1, 2),
  [665] = {.entry = {.count = 1, .reusable = true}}, SHIFT(75),
  [667] = {.entry = {.count = 1, .reusable = true}}, SHIFT(181),
  [669] = {.entry = {.count = 1, .reusable = true}}, SHIFT(21),
  [671] = {.entry = {.count = 1, .reusable = true}}, SHIFT(59),
  [673] = {.entry = {.count = 1, .reusable = true}}, SHIFT(280),
  [675] = {.entry = {.count = 1, .reusable = true}}, SHIFT(217),
  [677] = {.entry = {.count = 1, .reusable = true}}, SHIFT(296),
  [679] = {.entry = {.count = 1, .reusable = true}}, SHIFT(60),
  [681] = {.entry = {.count = 1, .reusable = true}}, SHIFT(293),
  [683] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_vector, 5, .production_id = 33),
  [685] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_vector, 3),
  [687] = {.entry = {.count = 1, .reusable = true}}, SHIFT(304),
  [689] = {.entry = {.count = 1, .reusable = true}}, SHIFT(286),
  [691] = {.entry = {.count = 1, .reusable = true}}, SHIFT(310),
  [693] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraints, 5, .production_id = 36),
  [695] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_vector, 4, .production_id = 13),
  [697] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraints, 6, .production_id = 37),
  [699] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_vector, 4),
  [701] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_value, 2, .production_id = 19),
  [703] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraints, 5, .production_id = 32),
  [705] = {.entry = {.count = 1, .reusable = true}}, SHIFT(273),
  [707] = {.entry = {.count = 1, .reusable = true}}, SHIFT(240),
  [709] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraints, 4, .production_id = 32),
  [711] = {.entry = {.count = 1, .reusable = true}}, SHIFT(179),
  [713] = {.entry = {.count = 1, .reusable = true}}, SHIFT(159),
  [715] = {.entry = {.count = 1, .reusable = true}}, SHIFT(86),
  [717] = {.entry = {.count = 1, .reusable = true}}, SHIFT(157),
  [719] = {.entry = {.count = 1, .reusable = true}},  ACCEPT_INPUT(),
  [721] = {.entry = {.count = 1, .reusable = false}}, SHIFT_EXTRA(),
  [723] = {.entry = {.count = 1, .reusable = false}}, SHIFT(318),
  [725] = {.entry = {.count = 1, .reusable = true}}, SHIFT(309),
  [727] = {.entry = {.count = 1, .reusable = false}}, SHIFT(302),
  [729] = {.entry = {.count = 1, .reusable = true}}, SHIFT(315),
  [731] = {.entry = {.count = 1, .reusable = true}}, SHIFT(168),
  [733] = {.entry = {.count = 1, .reusable = true}}, SHIFT(246),
  [735] = {.entry = {.count = 1, .reusable = true}}, SHIFT(58),
  [737] = {.entry = {.count = 1, .reusable = true}}, SHIFT(314),
  [739] = {.entry = {.count = 1, .reusable = false}}, SHIFT(311),
  [741] = {.entry = {.count = 1, .reusable = true}}, SHIFT(202),
  [743] = {.entry = {.count = 1, .reusable = true}}, SHIFT(144),
  [745] = {.entry = {.count = 1, .reusable = true}}, SHIFT(299),
  [747] = {.entry = {.count = 1, .reusable = false}}, SHIFT(300),
  [749] = {.entry = {.count = 1, .reusable = true}}, SHIFT(109),
};

#ifdef __cplusplus
extern "C" {
#endif
void *tree_sitter_uvl_external_scanner_create(void);
void tree_sitter_uvl_external_scanner_destroy(void *);
bool tree_sitter_uvl_external_scanner_scan(void *, TSLexer *, const bool *);
unsigned tree_sitter_uvl_external_scanner_serialize(void *, char *);
void tree_sitter_uvl_external_scanner_deserialize(void *, const char *, unsigned);

#ifdef _WIN32
#define extern __declspec(dllexport)
#endif

extern const TSLanguage *tree_sitter_uvl(void) {
  static const TSLanguage language = {
    .version = LANGUAGE_VERSION,
    .symbol_count = SYMBOL_COUNT,
    .alias_count = ALIAS_COUNT,
    .token_count = TOKEN_COUNT,
    .external_token_count = EXTERNAL_TOKEN_COUNT,
    .state_count = STATE_COUNT,
    .large_state_count = LARGE_STATE_COUNT,
    .production_id_count = PRODUCTION_ID_COUNT,
    .field_count = FIELD_COUNT,
    .max_alias_sequence_length = MAX_ALIAS_SEQUENCE_LENGTH,
    .parse_table = &ts_parse_table[0][0],
    .small_parse_table = ts_small_parse_table,
    .small_parse_table_map = ts_small_parse_table_map,
    .parse_actions = ts_parse_actions,
    .symbol_names = ts_symbol_names,
    .field_names = ts_field_names,
    .field_map_slices = ts_field_map_slices,
    .field_map_entries = ts_field_map_entries,
    .symbol_metadata = ts_symbol_metadata,
    .public_symbol_map = ts_symbol_map,
    .alias_map = ts_non_terminal_alias_map,
    .alias_sequences = &ts_alias_sequences[0][0],
    .lex_modes = ts_lex_modes,
    .lex_fn = ts_lex,
    .keyword_lex_fn = ts_lex_keywords,
    .keyword_capture_token = sym_name,
    .external_scanner = {
      &ts_external_scanner_states[0][0],
      ts_external_scanner_symbol_map,
      tree_sitter_uvl_external_scanner_create,
      tree_sitter_uvl_external_scanner_destroy,
      tree_sitter_uvl_external_scanner_scan,
      tree_sitter_uvl_external_scanner_serialize,
      tree_sitter_uvl_external_scanner_deserialize,
    },
    .primary_state_ids = ts_primary_state_ids,
  };
  return &language;
}
#ifdef __cplusplus
}
#endif
