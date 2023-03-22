#include <tree_sitter/parser.h>

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"
#endif

#define LANGUAGE_VERSION 14
#define STATE_COUNT 311
#define LARGE_STATE_COUNT 21
#define SYMBOL_COUNT 96
#define ALIAS_COUNT 2
#define TOKEN_COUNT 58
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
  anon_sym_Boolean = 43,
  anon_sym_Real = 44,
  anon_sym_Integer = 45,
  anon_sym_String = 46,
  anon_sym_SQUOTE = 47,
  anon_sym_DQUOTE = 48,
  aux_sym_string_name_token1 = 49,
  sym_string_content = 50,
  sym_imports = 51,
  sym_features = 52,
  sym_include = 53,
  sym_int = 54,
  sym__indent = 55,
  sym__dedent = 56,
  sym__newline = 57,
  sym_source_file = 58,
  sym_blk = 59,
  sym_attributes = 60,
  sym__header = 61,
  sym_typed_feature = 62,
  sym_ref = 63,
  sym_namespace = 64,
  sym_incomplete_namespace = 65,
  sym_incomplete_ref = 66,
  sym_cardinality = 67,
  sym_attribute_constraint = 68,
  sym_attribute_constraints = 69,
  sym_attribute_value = 70,
  sym__attribute = 71,
  sym__value = 72,
  sym__expr = 73,
  sym_unary_expr = 74,
  sym_binary_expr = 75,
  sym_nested_expr = 76,
  sym_function = 77,
  sym_vector = 78,
  sym_bool = 79,
  sym_path = 80,
  sym_lang_lvl = 81,
  sym_group_mode = 82,
  sym_major_lvl = 83,
  sym_minor_lvl = 84,
  sym_string = 85,
  sym_string_name = 86,
  sym_constraints = 87,
  sym__any_name = 88,
  aux_sym_source_file_repeat1 = 89,
  aux_sym_attributes_repeat1 = 90,
  aux_sym_attribute_constraints_repeat1 = 91,
  aux_sym_function_repeat1 = 92,
  aux_sym_vector_repeat1 = 93,
  aux_sym_path_repeat1 = 94,
  aux_sym_lang_lvl_repeat1 = 95,
  alias_sym_attrib_expr = 96,
  alias_sym_constraint = 97,
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
  [3] = 3,
  [4] = 4,
  [5] = 5,
  [6] = 6,
  [7] = 7,
  [8] = 8,
  [9] = 3,
  [10] = 10,
  [11] = 8,
  [12] = 12,
  [13] = 6,
  [14] = 2,
  [15] = 7,
  [16] = 12,
  [17] = 17,
  [18] = 17,
  [19] = 4,
  [20] = 5,
  [21] = 21,
  [22] = 22,
  [23] = 23,
  [24] = 24,
  [25] = 25,
  [26] = 26,
  [27] = 27,
  [28] = 27,
  [29] = 23,
  [30] = 26,
  [31] = 22,
  [32] = 32,
  [33] = 33,
  [34] = 33,
  [35] = 25,
  [36] = 36,
  [37] = 24,
  [38] = 21,
  [39] = 32,
  [40] = 40,
  [41] = 40,
  [42] = 42,
  [43] = 43,
  [44] = 44,
  [45] = 45,
  [46] = 46,
  [47] = 44,
  [48] = 48,
  [49] = 49,
  [50] = 45,
  [51] = 43,
  [52] = 46,
  [53] = 48,
  [54] = 42,
  [55] = 49,
  [56] = 56,
  [57] = 57,
  [58] = 58,
  [59] = 59,
  [60] = 58,
  [61] = 59,
  [62] = 62,
  [63] = 63,
  [64] = 62,
  [65] = 65,
  [66] = 66,
  [67] = 67,
  [68] = 68,
  [69] = 66,
  [70] = 70,
  [71] = 66,
  [72] = 72,
  [73] = 66,
  [74] = 67,
  [75] = 67,
  [76] = 76,
  [77] = 67,
  [78] = 57,
  [79] = 79,
  [80] = 80,
  [81] = 81,
  [82] = 81,
  [83] = 83,
  [84] = 84,
  [85] = 85,
  [86] = 83,
  [87] = 85,
  [88] = 79,
  [89] = 89,
  [90] = 89,
  [91] = 83,
  [92] = 85,
  [93] = 93,
  [94] = 89,
  [95] = 95,
  [96] = 96,
  [97] = 81,
  [98] = 96,
  [99] = 79,
  [100] = 81,
  [101] = 96,
  [102] = 89,
  [103] = 96,
  [104] = 79,
  [105] = 105,
  [106] = 85,
  [107] = 83,
  [108] = 70,
  [109] = 109,
  [110] = 110,
  [111] = 70,
  [112] = 112,
  [113] = 70,
  [114] = 114,
  [115] = 80,
  [116] = 80,
  [117] = 80,
  [118] = 118,
  [119] = 119,
  [120] = 120,
  [121] = 114,
  [122] = 114,
  [123] = 109,
  [124] = 124,
  [125] = 118,
  [126] = 109,
  [127] = 68,
  [128] = 118,
  [129] = 118,
  [130] = 68,
  [131] = 109,
  [132] = 68,
  [133] = 114,
  [134] = 134,
  [135] = 135,
  [136] = 136,
  [137] = 119,
  [138] = 138,
  [139] = 119,
  [140] = 140,
  [141] = 141,
  [142] = 142,
  [143] = 138,
  [144] = 144,
  [145] = 119,
  [146] = 146,
  [147] = 147,
  [148] = 148,
  [149] = 138,
  [150] = 150,
  [151] = 151,
  [152] = 152,
  [153] = 153,
  [154] = 57,
  [155] = 155,
  [156] = 138,
  [157] = 57,
  [158] = 153,
  [159] = 150,
  [160] = 160,
  [161] = 150,
  [162] = 135,
  [163] = 163,
  [164] = 135,
  [165] = 150,
  [166] = 140,
  [167] = 141,
  [168] = 142,
  [169] = 148,
  [170] = 134,
  [171] = 136,
  [172] = 152,
  [173] = 153,
  [174] = 174,
  [175] = 146,
  [176] = 147,
  [177] = 146,
  [178] = 147,
  [179] = 174,
  [180] = 142,
  [181] = 141,
  [182] = 152,
  [183] = 140,
  [184] = 148,
  [185] = 134,
  [186] = 135,
  [187] = 136,
  [188] = 134,
  [189] = 148,
  [190] = 140,
  [191] = 142,
  [192] = 146,
  [193] = 193,
  [194] = 147,
  [195] = 152,
  [196] = 141,
  [197] = 153,
  [198] = 136,
  [199] = 199,
  [200] = 199,
  [201] = 199,
  [202] = 199,
  [203] = 203,
  [204] = 204,
  [205] = 203,
  [206] = 206,
  [207] = 204,
  [208] = 204,
  [209] = 206,
  [210] = 203,
  [211] = 206,
  [212] = 204,
  [213] = 203,
  [214] = 206,
  [215] = 215,
  [216] = 216,
  [217] = 217,
  [218] = 218,
  [219] = 219,
  [220] = 220,
  [221] = 221,
  [222] = 222,
  [223] = 222,
  [224] = 224,
  [225] = 222,
  [226] = 226,
  [227] = 227,
  [228] = 222,
  [229] = 226,
  [230] = 230,
  [231] = 231,
  [232] = 232,
  [233] = 233,
  [234] = 234,
  [235] = 235,
  [236] = 234,
  [237] = 235,
  [238] = 238,
  [239] = 239,
  [240] = 240,
  [241] = 241,
  [242] = 242,
  [243] = 234,
  [244] = 244,
  [245] = 235,
  [246] = 246,
  [247] = 238,
  [248] = 239,
  [249] = 249,
  [250] = 250,
  [251] = 251,
  [252] = 252,
  [253] = 238,
  [254] = 238,
  [255] = 255,
  [256] = 234,
  [257] = 252,
  [258] = 258,
  [259] = 235,
  [260] = 249,
  [261] = 261,
  [262] = 27,
  [263] = 263,
  [264] = 264,
  [265] = 265,
  [266] = 266,
  [267] = 267,
  [268] = 268,
  [269] = 266,
  [270] = 270,
  [271] = 271,
  [272] = 25,
  [273] = 33,
  [274] = 261,
  [275] = 26,
  [276] = 23,
  [277] = 277,
  [278] = 278,
  [279] = 268,
  [280] = 25,
  [281] = 281,
  [282] = 282,
  [283] = 23,
  [284] = 26,
  [285] = 33,
  [286] = 286,
  [287] = 267,
  [288] = 263,
  [289] = 27,
  [290] = 290,
  [291] = 291,
  [292] = 292,
  [293] = 292,
  [294] = 294,
  [295] = 295,
  [296] = 296,
  [297] = 297,
  [298] = 298,
  [299] = 297,
  [300] = 298,
  [301] = 301,
  [302] = 291,
  [303] = 292,
  [304] = 298,
  [305] = 297,
  [306] = 292,
  [307] = 291,
  [308] = 298,
  [309] = 297,
  [310] = 291,
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
      if (eof) ADVANCE(78);
      if (lookahead == '!') ADVANCE(86);
      if (lookahead == '"') ADVANCE(126);
      if (lookahead == '&') ADVANCE(88);
      if (lookahead == '\'') ADVANCE(125);
      if (lookahead == '(') ADVANCE(97);
      if (lookahead == ')') ADVANCE(98);
      if (lookahead == '*') ADVANCE(84);
      if (lookahead == '+') ADVANCE(94);
      if (lookahead == ',') ADVANCE(80);
      if (lookahead == '-') ADVANCE(95);
      if (lookahead == '.') ADVANCE(117);
      if (lookahead == '/') ADVANCE(96);
      if (lookahead == '0') ADVANCE(99);
      if (lookahead == '<') ADVANCE(92);
      if (lookahead == '=') ADVANCE(11);
      if (lookahead == '>') ADVANCE(91);
      if (lookahead == 'S') ADVANCE(144);
      if (lookahead == 'T') ADVANCE(149);
      if (lookahead == '[') ADVANCE(82);
      if (lookahead == '\\') SKIP(74)
      if (lookahead == ']') ADVANCE(85);
      if (lookahead == '_') ADVANCE(171);
      if (lookahead == 'a') ADVANCE(157);
      if (lookahead == 'f') ADVANCE(152);
      if (lookahead == 'g') ADVANCE(163);
      if (lookahead == 't') ADVANCE(170);
      if (lookahead == '{') ADVANCE(79);
      if (lookahead == '|') ADVANCE(87);
      if (lookahead == '}') ADVANCE(81);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(0)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(100);
      if (sym_name_character_set_1(lookahead)) ADVANCE(172);
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
      if (lookahead == '!') ADVANCE(86);
      if (lookahead == '"') ADVANCE(126);
      if (lookahead == '&') ADVANCE(88);
      if (lookahead == '\'') ADVANCE(125);
      if (lookahead == '(') ADVANCE(97);
      if (lookahead == ')') ADVANCE(98);
      if (lookahead == '*') ADVANCE(84);
      if (lookahead == '+') ADVANCE(94);
      if (lookahead == ',') ADVANCE(80);
      if (lookahead == '-') ADVANCE(95);
      if (lookahead == '.') ADVANCE(116);
      if (lookahead == '/') ADVANCE(96);
      if (lookahead == '0') ADVANCE(99);
      if (lookahead == '<') ADVANCE(92);
      if (lookahead == '=') ADVANCE(11);
      if (lookahead == '>') ADVANCE(91);
      if (lookahead == '[') ADVANCE(82);
      if (lookahead == '\\') SKIP(2)
      if (lookahead == ']') ADVANCE(85);
      if (lookahead == '{') ADVANCE(79);
      if (lookahead == '|') ADVANCE(87);
      if (lookahead == '}') ADVANCE(81);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(5)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(100);
      if (sym_name_character_set_2(lookahead)) ADVANCE(172);
      END_STATE();
    case 6:
      if (lookahead == '*') ADVANCE(84);
      if (lookahead == '.') ADVANCE(10);
      if (lookahead == '/') ADVANCE(7);
      if (lookahead == '0') ADVANCE(173);
      if (lookahead == '\\') SKIP(4)
      if (lookahead == ']') ADVANCE(85);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(6)
      if (('1' <= lookahead && lookahead <= '9') ||
          lookahead == '_') ADVANCE(174);
      END_STATE();
    case 7:
      if (lookahead == '*') ADVANCE(9);
      if (lookahead == '/') ADVANCE(113);
      END_STATE();
    case 8:
      if (lookahead == '*') ADVANCE(8);
      if (lookahead == '/') ADVANCE(111);
      if (lookahead != 0) ADVANCE(9);
      END_STATE();
    case 9:
      if (lookahead == '*') ADVANCE(8);
      if (lookahead != 0) ADVANCE(9);
      END_STATE();
    case 10:
      if (lookahead == '.') ADVANCE(83);
      END_STATE();
    case 11:
      if (lookahead == '=') ADVANCE(93);
      if (lookahead == '>') ADVANCE(89);
      END_STATE();
    case 12:
      if (lookahead == '>') ADVANCE(90);
      END_STATE();
    case 13:
      if (lookahead == 'a') ADVANCE(53);
      END_STATE();
    case 14:
      if (lookahead == 'a') ADVANCE(41);
      END_STATE();
    case 15:
      if (lookahead == 'a') ADVANCE(32);
      END_STATE();
    case 16:
      if (lookahead == 'a') ADVANCE(42);
      END_STATE();
    case 17:
      if (lookahead == 'a') ADVANCE(55);
      END_STATE();
    case 18:
      if (lookahead == 'c') ADVANCE(51);
      END_STATE();
    case 19:
      if (lookahead == 'c') ADVANCE(13);
      END_STATE();
    case 20:
      if (lookahead == 'c') ADVANCE(62);
      END_STATE();
    case 21:
      if (lookahead == 'c') ADVANCE(17);
      END_STATE();
    case 22:
      if (lookahead == 'd') ADVANCE(31);
      END_STATE();
    case 23:
      if (lookahead == 'd') ADVANCE(36);
      END_STATE();
    case 24:
      if (lookahead == 'e') ADVANCE(64);
      END_STATE();
    case 25:
      if (lookahead == 'e') ADVANCE(38);
      END_STATE();
    case 26:
      if (lookahead == 'e') ADVANCE(39);
      END_STATE();
    case 27:
      if (lookahead == 'e') ADVANCE(40);
      END_STATE();
    case 28:
      if (lookahead == 'e') ADVANCE(65);
      END_STATE();
    case 29:
      if (lookahead == 'e') ADVANCE(66);
      END_STATE();
    case 30:
      if (lookahead == 'f') ADVANCE(63);
      END_STATE();
    case 31:
      if (lookahead == 'i') ADVANCE(48);
      END_STATE();
    case 32:
      if (lookahead == 'i') ADVANCE(49);
      END_STATE();
    case 33:
      if (lookahead == 'i') ADVANCE(58);
      END_STATE();
    case 34:
      if (lookahead == 'i') ADVANCE(61);
      END_STATE();
    case 35:
      if (lookahead == 'i') ADVANCE(52);
      END_STATE();
    case 36:
      if (lookahead == 'i') ADVANCE(50);
      END_STATE();
    case 37:
      if (lookahead == 'l') ADVANCE(24);
      END_STATE();
    case 38:
      if (lookahead == 'l') ADVANCE(119);
      END_STATE();
    case 39:
      if (lookahead == 'l') ADVANCE(118);
      END_STATE();
    case 40:
      if (lookahead == 'l') ADVANCE(120);
      END_STATE();
    case 41:
      if (lookahead == 'l') ADVANCE(33);
      END_STATE();
    case 42:
      if (lookahead == 'l') ADVANCE(34);
      END_STATE();
    case 43:
      if (lookahead == 'l') ADVANCE(28);
      END_STATE();
    case 44:
      if (lookahead == 'l') ADVANCE(29);
      END_STATE();
    case 45:
      if (lookahead == 'n') ADVANCE(56);
      END_STATE();
    case 46:
      if (lookahead == 'n') ADVANCE(123);
      END_STATE();
    case 47:
      if (lookahead == 'n') ADVANCE(20);
      END_STATE();
    case 48:
      if (lookahead == 'n') ADVANCE(14);
      END_STATE();
    case 49:
      if (lookahead == 'n') ADVANCE(60);
      END_STATE();
    case 50:
      if (lookahead == 'n') ADVANCE(16);
      END_STATE();
    case 51:
      if (lookahead == 'o') ADVANCE(45);
      END_STATE();
    case 52:
      if (lookahead == 'o') ADVANCE(46);
      END_STATE();
    case 53:
      if (lookahead == 'r') ADVANCE(22);
      END_STATE();
    case 54:
      if (lookahead == 'r') ADVANCE(15);
      END_STATE();
    case 55:
      if (lookahead == 'r') ADVANCE(23);
      END_STATE();
    case 56:
      if (lookahead == 's') ADVANCE(59);
      END_STATE();
    case 57:
      if (lookahead == 's') ADVANCE(124);
      END_STATE();
    case 58:
      if (lookahead == 't') ADVANCE(67);
      END_STATE();
    case 59:
      if (lookahead == 't') ADVANCE(54);
      END_STATE();
    case 60:
      if (lookahead == 't') ADVANCE(57);
      END_STATE();
    case 61:
      if (lookahead == 't') ADVANCE(68);
      END_STATE();
    case 62:
      if (lookahead == 't') ADVANCE(35);
      END_STATE();
    case 63:
      if (lookahead == 'u') ADVANCE(47);
      END_STATE();
    case 64:
      if (lookahead == 'v') ADVANCE(25);
      END_STATE();
    case 65:
      if (lookahead == 'v') ADVANCE(26);
      END_STATE();
    case 66:
      if (lookahead == 'v') ADVANCE(27);
      END_STATE();
    case 67:
      if (lookahead == 'y') ADVANCE(121);
      END_STATE();
    case 68:
      if (lookahead == 'y') ADVANCE(122);
      END_STATE();
    case 69:
      if (lookahead == '+' ||
          lookahead == '-') ADVANCE(70);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(110);
      END_STATE();
    case 70:
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(110);
      END_STATE();
    case 71:
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(103);
      END_STATE();
    case 72:
      if (lookahead != 0 &&
          lookahead != '\r') ADVANCE(113);
      if (lookahead == '\r') ADVANCE(115);
      END_STATE();
    case 73:
      if (eof) ADVANCE(78);
      if (lookahead == '\n') SKIP(0)
      END_STATE();
    case 74:
      if (eof) ADVANCE(78);
      if (lookahead == '\n') SKIP(0)
      if (lookahead == '\r') SKIP(73)
      END_STATE();
    case 75:
      if (eof) ADVANCE(78);
      if (lookahead == '\n') SKIP(77)
      END_STATE();
    case 76:
      if (eof) ADVANCE(78);
      if (lookahead == '\n') SKIP(77)
      if (lookahead == '\r') SKIP(75)
      END_STATE();
    case 77:
      if (eof) ADVANCE(78);
      if (lookahead == '!') ADVANCE(86);
      if (lookahead == '"') ADVANCE(126);
      if (lookahead == '&') ADVANCE(88);
      if (lookahead == '\'') ADVANCE(125);
      if (lookahead == '(') ADVANCE(97);
      if (lookahead == ')') ADVANCE(98);
      if (lookahead == '*') ADVANCE(84);
      if (lookahead == '+') ADVANCE(94);
      if (lookahead == ',') ADVANCE(80);
      if (lookahead == '-') ADVANCE(95);
      if (lookahead == '.') ADVANCE(116);
      if (lookahead == '/') ADVANCE(96);
      if (lookahead == '0') ADVANCE(99);
      if (lookahead == '<') ADVANCE(92);
      if (lookahead == '=') ADVANCE(11);
      if (lookahead == '>') ADVANCE(91);
      if (lookahead == 'S') ADVANCE(144);
      if (lookahead == 'T') ADVANCE(149);
      if (lookahead == '[') ADVANCE(82);
      if (lookahead == '\\') SKIP(76)
      if (lookahead == ']') ADVANCE(85);
      if (lookahead == 'a') ADVANCE(157);
      if (lookahead == 'f') ADVANCE(152);
      if (lookahead == 'g') ADVANCE(163);
      if (lookahead == 't') ADVANCE(170);
      if (lookahead == '{') ADVANCE(79);
      if (lookahead == '|') ADVANCE(87);
      if (lookahead == '}') ADVANCE(81);
      if (lookahead == '\t' ||
          lookahead == '\n' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) SKIP(77)
      if (('1' <= lookahead && lookahead <= '9')) ADVANCE(100);
      if (sym_name_character_set_3(lookahead)) ADVANCE(172);
      END_STATE();
    case 78:
      ACCEPT_TOKEN(ts_builtin_sym_end);
      END_STATE();
    case 79:
      ACCEPT_TOKEN(anon_sym_LBRACE);
      END_STATE();
    case 80:
      ACCEPT_TOKEN(anon_sym_COMMA);
      END_STATE();
    case 81:
      ACCEPT_TOKEN(anon_sym_RBRACE);
      END_STATE();
    case 82:
      ACCEPT_TOKEN(anon_sym_LBRACK);
      END_STATE();
    case 83:
      ACCEPT_TOKEN(anon_sym_DOT_DOT);
      END_STATE();
    case 84:
      ACCEPT_TOKEN(anon_sym_STAR);
      END_STATE();
    case 85:
      ACCEPT_TOKEN(anon_sym_RBRACK);
      END_STATE();
    case 86:
      ACCEPT_TOKEN(anon_sym_BANG);
      END_STATE();
    case 87:
      ACCEPT_TOKEN(anon_sym_PIPE);
      END_STATE();
    case 88:
      ACCEPT_TOKEN(anon_sym_AMP);
      END_STATE();
    case 89:
      ACCEPT_TOKEN(anon_sym_EQ_GT);
      END_STATE();
    case 90:
      ACCEPT_TOKEN(anon_sym_LT_EQ_GT);
      END_STATE();
    case 91:
      ACCEPT_TOKEN(anon_sym_GT);
      END_STATE();
    case 92:
      ACCEPT_TOKEN(anon_sym_LT);
      if (lookahead == '=') ADVANCE(12);
      END_STATE();
    case 93:
      ACCEPT_TOKEN(anon_sym_EQ_EQ);
      END_STATE();
    case 94:
      ACCEPT_TOKEN(anon_sym_PLUS);
      END_STATE();
    case 95:
      ACCEPT_TOKEN(anon_sym_DASH);
      END_STATE();
    case 96:
      ACCEPT_TOKEN(anon_sym_SLASH);
      if (lookahead == '*') ADVANCE(9);
      if (lookahead == '/') ADVANCE(113);
      END_STATE();
    case 97:
      ACCEPT_TOKEN(anon_sym_LPAREN);
      END_STATE();
    case 98:
      ACCEPT_TOKEN(anon_sym_RPAREN);
      END_STATE();
    case 99:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(108);
      if (lookahead == '_') ADVANCE(100);
      if (lookahead == 'X' ||
          lookahead == 'x') ADVANCE(71);
      if (lookahead == 'E' ||
          lookahead == 'P' ||
          lookahead == 'e' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(100);
      END_STATE();
    case 100:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(108);
      if (lookahead == '_') ADVANCE(100);
      if (lookahead == 'E' ||
          lookahead == 'P' ||
          lookahead == 'e' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(100);
      END_STATE();
    case 101:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(106);
      if (lookahead == '_') ADVANCE(103);
      if (lookahead == '+' ||
          lookahead == '-') ADVANCE(70);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(101);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(69);
      if (('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(103);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(102);
      END_STATE();
    case 102:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(106);
      if (lookahead == '_') ADVANCE(103);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(101);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(69);
      if (('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(103);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(102);
      END_STATE();
    case 103:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '.') ADVANCE(106);
      if (lookahead == '_') ADVANCE(103);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(101);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(103);
      END_STATE();
    case 104:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == '+' ||
          lookahead == '-') ADVANCE(70);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(104);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(105);
      if (('A' <= lookahead && lookahead <= 'F') ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(107);
      END_STATE();
    case 105:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(104);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(105);
      if (('A' <= lookahead && lookahead <= 'F') ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(107);
      END_STATE();
    case 106:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(104);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(107);
      END_STATE();
    case 107:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'e') ADVANCE(104);
      if (lookahead == 'P' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9') ||
          ('A' <= lookahead && lookahead <= 'F') ||
          lookahead == '_' ||
          ('a' <= lookahead && lookahead <= 'f')) ADVANCE(107);
      END_STATE();
    case 108:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'P' ||
          lookahead == 'e' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(109);
      END_STATE();
    case 109:
      ACCEPT_TOKEN(sym_number);
      if (lookahead == 'E' ||
          lookahead == 'P' ||
          lookahead == 'e' ||
          lookahead == 'p') ADVANCE(69);
      if (('0' <= lookahead && lookahead <= '9') ||
          lookahead == '_') ADVANCE(109);
      END_STATE();
    case 110:
      ACCEPT_TOKEN(sym_number);
      if (('0' <= lookahead && lookahead <= '9')) ADVANCE(110);
      END_STATE();
    case 111:
      ACCEPT_TOKEN(sym_comment);
      END_STATE();
    case 112:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead == '"') ADVANCE(113);
      if (lookahead == '\\') ADVANCE(72);
      if (lookahead != 0 &&
          lookahead != '\n') ADVANCE(112);
      END_STATE();
    case 113:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead == '\\') ADVANCE(72);
      if (lookahead != 0 &&
          lookahead != '\n') ADVANCE(113);
      END_STATE();
    case 114:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '"' &&
          lookahead != '\\') ADVANCE(131);
      END_STATE();
    case 115:
      ACCEPT_TOKEN(sym_comment);
      if (lookahead != 0 &&
          lookahead != '\\') ADVANCE(113);
      if (lookahead == '\\') ADVANCE(72);
      END_STATE();
    case 116:
      ACCEPT_TOKEN(anon_sym_DOT);
      END_STATE();
    case 117:
      ACCEPT_TOKEN(anon_sym_DOT);
      if (lookahead == '.') ADVANCE(83);
      END_STATE();
    case 118:
      ACCEPT_TOKEN(anon_sym_SMT_DASHlevel);
      END_STATE();
    case 119:
      ACCEPT_TOKEN(anon_sym_SAT_DASHlevel);
      END_STATE();
    case 120:
      ACCEPT_TOKEN(anon_sym_TYPE_DASHlevel);
      END_STATE();
    case 121:
      ACCEPT_TOKEN(anon_sym_group_DASHcardinality);
      END_STATE();
    case 122:
      ACCEPT_TOKEN(anon_sym_feature_DASHcardinality);
      END_STATE();
    case 123:
      ACCEPT_TOKEN(anon_sym_aggregate_DASHfunction);
      END_STATE();
    case 124:
      ACCEPT_TOKEN(anon_sym_type_DASHconstraints);
      END_STATE();
    case 125:
      ACCEPT_TOKEN(anon_sym_SQUOTE);
      END_STATE();
    case 126:
      ACCEPT_TOKEN(anon_sym_DQUOTE);
      END_STATE();
    case 127:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead == '*') ADVANCE(129);
      if (lookahead == '/') ADVANCE(112);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '"' &&
          lookahead != '\\') ADVANCE(131);
      END_STATE();
    case 128:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead == '*') ADVANCE(128);
      if (lookahead == '/') ADVANCE(114);
      if (lookahead == '\n' ||
          lookahead == '"' ||
          lookahead == '\\') ADVANCE(9);
      if (lookahead != 0) ADVANCE(129);
      END_STATE();
    case 129:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead == '*') ADVANCE(128);
      if (lookahead == '\n' ||
          lookahead == '"' ||
          lookahead == '\\') ADVANCE(9);
      if (lookahead != 0) ADVANCE(129);
      END_STATE();
    case 130:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead == '/') ADVANCE(127);
      if (lookahead == '\t' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) ADVANCE(130);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '"' &&
          lookahead != '\\') ADVANCE(131);
      END_STATE();
    case 131:
      ACCEPT_TOKEN(aux_sym_string_name_token1);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '"' &&
          lookahead != '\\') ADVANCE(131);
      END_STATE();
    case 132:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead == '*') ADVANCE(134);
      if (lookahead == '/') ADVANCE(136);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(136);
      END_STATE();
    case 133:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead == '*') ADVANCE(133);
      if (lookahead == '/') ADVANCE(136);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(134);
      END_STATE();
    case 134:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead == '*') ADVANCE(133);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(134);
      END_STATE();
    case 135:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead == '/') ADVANCE(132);
      if (lookahead == '\t' ||
          lookahead == '\f' ||
          lookahead == '\r' ||
          lookahead == ' ' ||
          lookahead == 8203 ||
          lookahead == 8288 ||
          lookahead == 65279) ADVANCE(135);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(136);
      END_STATE();
    case 136:
      ACCEPT_TOKEN(sym_string_content);
      if (lookahead != 0 &&
          lookahead != '\n' &&
          lookahead != '\'' &&
          lookahead != '\\') ADVANCE(136);
      END_STATE();
    case 137:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(37);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 138:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(18);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 139:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(30);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 140:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(19);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 141:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(43);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 142:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(44);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 143:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == '-') ADVANCE(21);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 144:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'A') ADVANCE(147);
      if (lookahead == 'M') ADVANCE(148);
      if (sym_name_character_set_5(lookahead)) ADVANCE(172);
      END_STATE();
    case 145:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'E') ADVANCE(142);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 146:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'P') ADVANCE(145);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 147:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'T') ADVANCE(137);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 148:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'T') ADVANCE(141);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 149:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'Y') ADVANCE(146);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 150:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'a') ADVANCE(166);
      if (sym_name_character_set_6(lookahead)) ADVANCE(172);
      END_STATE();
    case 151:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'a') ADVANCE(167);
      if (sym_name_character_set_6(lookahead)) ADVANCE(172);
      END_STATE();
    case 152:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(150);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 153:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(138);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 154:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(159);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 155:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(139);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 156:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'e') ADVANCE(143);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 157:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'g') ADVANCE(158);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 158:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'g') ADVANCE(164);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 159:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'g') ADVANCE(151);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 160:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'o') ADVANCE(168);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 161:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'p') ADVANCE(153);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 162:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'p') ADVANCE(140);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 163:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'r') ADVANCE(160);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 164:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'r') ADVANCE(154);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 165:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'r') ADVANCE(156);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 166:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 't') ADVANCE(169);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 167:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 't') ADVANCE(155);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 168:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'u') ADVANCE(162);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 169:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'u') ADVANCE(165);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 170:
      ACCEPT_TOKEN(sym_name);
      if (lookahead == 'y') ADVANCE(161);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 171:
      ACCEPT_TOKEN(sym_name);
      if (('0' <= lookahead && lookahead <= '9') ||
          lookahead == '_') ADVANCE(171);
      if (sym_name_character_set_7(lookahead)) ADVANCE(172);
      END_STATE();
    case 172:
      ACCEPT_TOKEN(sym_name);
      if (sym_name_character_set_4(lookahead)) ADVANCE(172);
      END_STATE();
    case 173:
      ACCEPT_TOKEN(sym_int);
      END_STATE();
    case 174:
      ACCEPT_TOKEN(sym_int);
      if (('0' <= lookahead && lookahead <= '9') ||
          lookahead == '_') ADVANCE(174);
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
  [1] = {.lex_state = 77, .external_lex_state = 2},
  [2] = {.lex_state = 77, .external_lex_state = 3},
  [3] = {.lex_state = 77, .external_lex_state = 3},
  [4] = {.lex_state = 77, .external_lex_state = 3},
  [5] = {.lex_state = 77, .external_lex_state = 3},
  [6] = {.lex_state = 77, .external_lex_state = 3},
  [7] = {.lex_state = 77, .external_lex_state = 3},
  [8] = {.lex_state = 77, .external_lex_state = 3},
  [9] = {.lex_state = 77, .external_lex_state = 2},
  [10] = {.lex_state = 77, .external_lex_state = 2},
  [11] = {.lex_state = 77, .external_lex_state = 3},
  [12] = {.lex_state = 77, .external_lex_state = 3},
  [13] = {.lex_state = 77, .external_lex_state = 3},
  [14] = {.lex_state = 77, .external_lex_state = 3},
  [15] = {.lex_state = 77, .external_lex_state = 3},
  [16] = {.lex_state = 77, .external_lex_state = 3},
  [17] = {.lex_state = 77, .external_lex_state = 3},
  [18] = {.lex_state = 77, .external_lex_state = 3},
  [19] = {.lex_state = 77, .external_lex_state = 3},
  [20] = {.lex_state = 77, .external_lex_state = 3},
  [21] = {.lex_state = 77, .external_lex_state = 4},
  [22] = {.lex_state = 77, .external_lex_state = 4},
  [23] = {.lex_state = 77, .external_lex_state = 4},
  [24] = {.lex_state = 77, .external_lex_state = 4},
  [25] = {.lex_state = 77, .external_lex_state = 5},
  [26] = {.lex_state = 77, .external_lex_state = 5},
  [27] = {.lex_state = 77, .external_lex_state = 4},
  [28] = {.lex_state = 77, .external_lex_state = 5},
  [29] = {.lex_state = 77, .external_lex_state = 5},
  [30] = {.lex_state = 77, .external_lex_state = 4},
  [31] = {.lex_state = 77, .external_lex_state = 5},
  [32] = {.lex_state = 77, .external_lex_state = 5},
  [33] = {.lex_state = 77, .external_lex_state = 4},
  [34] = {.lex_state = 77, .external_lex_state = 5},
  [35] = {.lex_state = 77, .external_lex_state = 4},
  [36] = {.lex_state = 77, .external_lex_state = 6},
  [37] = {.lex_state = 77, .external_lex_state = 5},
  [38] = {.lex_state = 77, .external_lex_state = 5},
  [39] = {.lex_state = 77, .external_lex_state = 4},
  [40] = {.lex_state = 77, .external_lex_state = 3},
  [41] = {.lex_state = 77, .external_lex_state = 2},
  [42] = {.lex_state = 77, .external_lex_state = 3},
  [43] = {.lex_state = 77, .external_lex_state = 3},
  [44] = {.lex_state = 77, .external_lex_state = 3},
  [45] = {.lex_state = 77, .external_lex_state = 3},
  [46] = {.lex_state = 77, .external_lex_state = 2},
  [47] = {.lex_state = 77, .external_lex_state = 2},
  [48] = {.lex_state = 77, .external_lex_state = 2},
  [49] = {.lex_state = 77, .external_lex_state = 2},
  [50] = {.lex_state = 77, .external_lex_state = 2},
  [51] = {.lex_state = 77, .external_lex_state = 2},
  [52] = {.lex_state = 77, .external_lex_state = 3},
  [53] = {.lex_state = 77, .external_lex_state = 3},
  [54] = {.lex_state = 77, .external_lex_state = 2},
  [55] = {.lex_state = 77, .external_lex_state = 3},
  [56] = {.lex_state = 5, .external_lex_state = 7},
  [57] = {.lex_state = 5, .external_lex_state = 7},
  [58] = {.lex_state = 5, .external_lex_state = 8},
  [59] = {.lex_state = 5, .external_lex_state = 8},
  [60] = {.lex_state = 5, .external_lex_state = 8},
  [61] = {.lex_state = 5, .external_lex_state = 8},
  [62] = {.lex_state = 5, .external_lex_state = 2},
  [63] = {.lex_state = 5, .external_lex_state = 2},
  [64] = {.lex_state = 5, .external_lex_state = 2},
  [65] = {.lex_state = 5, .external_lex_state = 6},
  [66] = {.lex_state = 5, .external_lex_state = 9},
  [67] = {.lex_state = 5, .external_lex_state = 9},
  [68] = {.lex_state = 5, .external_lex_state = 6},
  [69] = {.lex_state = 5, .external_lex_state = 9},
  [70] = {.lex_state = 5, .external_lex_state = 6},
  [71] = {.lex_state = 5, .external_lex_state = 9},
  [72] = {.lex_state = 5, .external_lex_state = 8},
  [73] = {.lex_state = 5, .external_lex_state = 9},
  [74] = {.lex_state = 5, .external_lex_state = 9},
  [75] = {.lex_state = 5, .external_lex_state = 9},
  [76] = {.lex_state = 5, .external_lex_state = 8},
  [77] = {.lex_state = 5, .external_lex_state = 9},
  [78] = {.lex_state = 5, .external_lex_state = 6},
  [79] = {.lex_state = 5, .external_lex_state = 2},
  [80] = {.lex_state = 5, .external_lex_state = 6},
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
  [108] = {.lex_state = 5, .external_lex_state = 9},
  [109] = {.lex_state = 5, .external_lex_state = 6},
  [110] = {.lex_state = 77, .external_lex_state = 6},
  [111] = {.lex_state = 5, .external_lex_state = 8},
  [112] = {.lex_state = 77, .external_lex_state = 6},
  [113] = {.lex_state = 5, .external_lex_state = 7},
  [114] = {.lex_state = 5, .external_lex_state = 6},
  [115] = {.lex_state = 5, .external_lex_state = 9},
  [116] = {.lex_state = 5, .external_lex_state = 7},
  [117] = {.lex_state = 5, .external_lex_state = 8},
  [118] = {.lex_state = 5, .external_lex_state = 6},
  [119] = {.lex_state = 5, .external_lex_state = 6},
  [120] = {.lex_state = 5, .external_lex_state = 6},
  [121] = {.lex_state = 77, .external_lex_state = 8},
  [122] = {.lex_state = 77, .external_lex_state = 7},
  [123] = {.lex_state = 77, .external_lex_state = 8},
  [124] = {.lex_state = 5, .external_lex_state = 6},
  [125] = {.lex_state = 77, .external_lex_state = 8},
  [126] = {.lex_state = 77, .external_lex_state = 9},
  [127] = {.lex_state = 77, .external_lex_state = 8},
  [128] = {.lex_state = 77, .external_lex_state = 9},
  [129] = {.lex_state = 77, .external_lex_state = 7},
  [130] = {.lex_state = 77, .external_lex_state = 7},
  [131] = {.lex_state = 77, .external_lex_state = 7},
  [132] = {.lex_state = 77, .external_lex_state = 9},
  [133] = {.lex_state = 77, .external_lex_state = 9},
  [134] = {.lex_state = 5, .external_lex_state = 6},
  [135] = {.lex_state = 5, .external_lex_state = 6},
  [136] = {.lex_state = 5, .external_lex_state = 6},
  [137] = {.lex_state = 77, .external_lex_state = 7},
  [138] = {.lex_state = 0, .external_lex_state = 9},
  [139] = {.lex_state = 77, .external_lex_state = 8},
  [140] = {.lex_state = 5, .external_lex_state = 6},
  [141] = {.lex_state = 5, .external_lex_state = 6},
  [142] = {.lex_state = 5, .external_lex_state = 6},
  [143] = {.lex_state = 0, .external_lex_state = 9},
  [144] = {.lex_state = 0, .external_lex_state = 8},
  [145] = {.lex_state = 77, .external_lex_state = 9},
  [146] = {.lex_state = 5, .external_lex_state = 6},
  [147] = {.lex_state = 5, .external_lex_state = 6},
  [148] = {.lex_state = 5, .external_lex_state = 6},
  [149] = {.lex_state = 0, .external_lex_state = 9},
  [150] = {.lex_state = 5, .external_lex_state = 6},
  [151] = {.lex_state = 77, .external_lex_state = 2},
  [152] = {.lex_state = 5, .external_lex_state = 6},
  [153] = {.lex_state = 5, .external_lex_state = 6},
  [154] = {.lex_state = 77, .external_lex_state = 9},
  [155] = {.lex_state = 5, .external_lex_state = 6},
  [156] = {.lex_state = 0, .external_lex_state = 9},
  [157] = {.lex_state = 77, .external_lex_state = 8},
  [158] = {.lex_state = 0, .external_lex_state = 9},
  [159] = {.lex_state = 0, .external_lex_state = 7},
  [160] = {.lex_state = 0, .external_lex_state = 9},
  [161] = {.lex_state = 0, .external_lex_state = 8},
  [162] = {.lex_state = 0, .external_lex_state = 8},
  [163] = {.lex_state = 0, .external_lex_state = 7},
  [164] = {.lex_state = 0, .external_lex_state = 9},
  [165] = {.lex_state = 0, .external_lex_state = 9},
  [166] = {.lex_state = 0, .external_lex_state = 9},
  [167] = {.lex_state = 0, .external_lex_state = 9},
  [168] = {.lex_state = 0, .external_lex_state = 7},
  [169] = {.lex_state = 0, .external_lex_state = 9},
  [170] = {.lex_state = 0, .external_lex_state = 9},
  [171] = {.lex_state = 0, .external_lex_state = 9},
  [172] = {.lex_state = 0, .external_lex_state = 9},
  [173] = {.lex_state = 0, .external_lex_state = 8},
  [174] = {.lex_state = 0, .external_lex_state = 8},
  [175] = {.lex_state = 0, .external_lex_state = 7},
  [176] = {.lex_state = 0, .external_lex_state = 9},
  [177] = {.lex_state = 0, .external_lex_state = 9},
  [178] = {.lex_state = 0, .external_lex_state = 7},
  [179] = {.lex_state = 0, .external_lex_state = 7},
  [180] = {.lex_state = 0, .external_lex_state = 9},
  [181] = {.lex_state = 0, .external_lex_state = 8},
  [182] = {.lex_state = 0, .external_lex_state = 7},
  [183] = {.lex_state = 0, .external_lex_state = 8},
  [184] = {.lex_state = 0, .external_lex_state = 8},
  [185] = {.lex_state = 0, .external_lex_state = 8},
  [186] = {.lex_state = 0, .external_lex_state = 7},
  [187] = {.lex_state = 0, .external_lex_state = 7},
  [188] = {.lex_state = 0, .external_lex_state = 7},
  [189] = {.lex_state = 0, .external_lex_state = 7},
  [190] = {.lex_state = 0, .external_lex_state = 7},
  [191] = {.lex_state = 0, .external_lex_state = 8},
  [192] = {.lex_state = 0, .external_lex_state = 8},
  [193] = {.lex_state = 0, .external_lex_state = 8},
  [194] = {.lex_state = 0, .external_lex_state = 8},
  [195] = {.lex_state = 0, .external_lex_state = 8},
  [196] = {.lex_state = 0, .external_lex_state = 7},
  [197] = {.lex_state = 0, .external_lex_state = 7},
  [198] = {.lex_state = 0, .external_lex_state = 8},
  [199] = {.lex_state = 0, .external_lex_state = 9},
  [200] = {.lex_state = 0, .external_lex_state = 9},
  [201] = {.lex_state = 0, .external_lex_state = 9},
  [202] = {.lex_state = 0, .external_lex_state = 9},
  [203] = {.lex_state = 5, .external_lex_state = 7},
  [204] = {.lex_state = 5, .external_lex_state = 7},
  [205] = {.lex_state = 5, .external_lex_state = 7},
  [206] = {.lex_state = 5, .external_lex_state = 7},
  [207] = {.lex_state = 5, .external_lex_state = 7},
  [208] = {.lex_state = 5, .external_lex_state = 7},
  [209] = {.lex_state = 5, .external_lex_state = 7},
  [210] = {.lex_state = 5, .external_lex_state = 7},
  [211] = {.lex_state = 5, .external_lex_state = 7},
  [212] = {.lex_state = 5, .external_lex_state = 7},
  [213] = {.lex_state = 5, .external_lex_state = 7},
  [214] = {.lex_state = 5, .external_lex_state = 7},
  [215] = {.lex_state = 5, .external_lex_state = 2},
  [216] = {.lex_state = 5, .external_lex_state = 6},
  [217] = {.lex_state = 5, .external_lex_state = 6},
  [218] = {.lex_state = 5, .external_lex_state = 6},
  [219] = {.lex_state = 5, .external_lex_state = 6},
  [220] = {.lex_state = 5, .external_lex_state = 6},
  [221] = {.lex_state = 5, .external_lex_state = 6},
  [222] = {.lex_state = 5, .external_lex_state = 2},
  [223] = {.lex_state = 5, .external_lex_state = 2},
  [224] = {.lex_state = 5, .external_lex_state = 6},
  [225] = {.lex_state = 5, .external_lex_state = 2},
  [226] = {.lex_state = 5, .external_lex_state = 6},
  [227] = {.lex_state = 5, .external_lex_state = 6},
  [228] = {.lex_state = 5, .external_lex_state = 2},
  [229] = {.lex_state = 5, .external_lex_state = 6},
  [230] = {.lex_state = 5, .external_lex_state = 6},
  [231] = {.lex_state = 5, .external_lex_state = 6},
  [232] = {.lex_state = 0, .external_lex_state = 8},
  [233] = {.lex_state = 0, .external_lex_state = 8},
  [234] = {.lex_state = 0, .external_lex_state = 9},
  [235] = {.lex_state = 0, .external_lex_state = 7},
  [236] = {.lex_state = 0, .external_lex_state = 9},
  [237] = {.lex_state = 0, .external_lex_state = 7},
  [238] = {.lex_state = 0, .external_lex_state = 7},
  [239] = {.lex_state = 0, .external_lex_state = 8},
  [240] = {.lex_state = 5, .external_lex_state = 6},
  [241] = {.lex_state = 0, .external_lex_state = 9},
  [242] = {.lex_state = 5, .external_lex_state = 6},
  [243] = {.lex_state = 0, .external_lex_state = 9},
  [244] = {.lex_state = 5, .external_lex_state = 6},
  [245] = {.lex_state = 0, .external_lex_state = 7},
  [246] = {.lex_state = 0, .external_lex_state = 8},
  [247] = {.lex_state = 0, .external_lex_state = 7},
  [248] = {.lex_state = 0, .external_lex_state = 8},
  [249] = {.lex_state = 0, .external_lex_state = 8},
  [250] = {.lex_state = 5, .external_lex_state = 6},
  [251] = {.lex_state = 5, .external_lex_state = 6},
  [252] = {.lex_state = 0, .external_lex_state = 6},
  [253] = {.lex_state = 0, .external_lex_state = 7},
  [254] = {.lex_state = 0, .external_lex_state = 7},
  [255] = {.lex_state = 0, .external_lex_state = 7},
  [256] = {.lex_state = 0, .external_lex_state = 9},
  [257] = {.lex_state = 0, .external_lex_state = 6},
  [258] = {.lex_state = 5, .external_lex_state = 6},
  [259] = {.lex_state = 0, .external_lex_state = 7},
  [260] = {.lex_state = 0, .external_lex_state = 8},
  [261] = {.lex_state = 0, .external_lex_state = 8},
  [262] = {.lex_state = 0, .external_lex_state = 7},
  [263] = {.lex_state = 0, .external_lex_state = 8},
  [264] = {.lex_state = 6, .external_lex_state = 2},
  [265] = {.lex_state = 0, .external_lex_state = 7},
  [266] = {.lex_state = 0, .external_lex_state = 8},
  [267] = {.lex_state = 0, .external_lex_state = 8},
  [268] = {.lex_state = 0, .external_lex_state = 2},
  [269] = {.lex_state = 0, .external_lex_state = 7},
  [270] = {.lex_state = 6, .external_lex_state = 2},
  [271] = {.lex_state = 0, .external_lex_state = 7},
  [272] = {.lex_state = 0, .external_lex_state = 7},
  [273] = {.lex_state = 0, .external_lex_state = 8},
  [274] = {.lex_state = 0, .external_lex_state = 7},
  [275] = {.lex_state = 0, .external_lex_state = 7},
  [276] = {.lex_state = 0, .external_lex_state = 8},
  [277] = {.lex_state = 0, .external_lex_state = 7},
  [278] = {.lex_state = 6, .external_lex_state = 8},
  [279] = {.lex_state = 0, .external_lex_state = 2},
  [280] = {.lex_state = 0, .external_lex_state = 8},
  [281] = {.lex_state = 0, .external_lex_state = 7},
  [282] = {.lex_state = 0, .external_lex_state = 8},
  [283] = {.lex_state = 0, .external_lex_state = 7},
  [284] = {.lex_state = 0, .external_lex_state = 8},
  [285] = {.lex_state = 0, .external_lex_state = 7},
  [286] = {.lex_state = 0, .external_lex_state = 7},
  [287] = {.lex_state = 0, .external_lex_state = 7},
  [288] = {.lex_state = 0, .external_lex_state = 7},
  [289] = {.lex_state = 0, .external_lex_state = 8},
  [290] = {.lex_state = 0, .external_lex_state = 7},
  [291] = {.lex_state = 0, .external_lex_state = 2},
  [292] = {.lex_state = 0, .external_lex_state = 2},
  [293] = {.lex_state = 0, .external_lex_state = 2},
  [294] = {.lex_state = 0, .external_lex_state = 2},
  [295] = {.lex_state = 0, .external_lex_state = 2},
  [296] = {.lex_state = 0, .external_lex_state = 8},
  [297] = {.lex_state = 130, .external_lex_state = 2},
  [298] = {.lex_state = 135, .external_lex_state = 2},
  [299] = {.lex_state = 130, .external_lex_state = 2},
  [300] = {.lex_state = 135, .external_lex_state = 2},
  [301] = {.lex_state = 0, .external_lex_state = 8},
  [302] = {.lex_state = 0, .external_lex_state = 2},
  [303] = {.lex_state = 0, .external_lex_state = 2},
  [304] = {.lex_state = 135, .external_lex_state = 2},
  [305] = {.lex_state = 130, .external_lex_state = 2},
  [306] = {.lex_state = 0, .external_lex_state = 2},
  [307] = {.lex_state = 0, .external_lex_state = 2},
  [308] = {.lex_state = 135, .external_lex_state = 2},
  [309] = {.lex_state = 130, .external_lex_state = 2},
  [310] = {.lex_state = 0, .external_lex_state = 2},
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
    [sym_source_file] = STATE(295),
    [sym_blk] = STATE(10),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(33),
    [sym_features] = ACTIONS(33),
    [sym_include] = ACTIONS(33),
  },
  [2] = {
    [sym_blk] = STATE(16),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(16),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(37),
  },
  [3] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(3),
    [sym_name] = ACTIONS(39),
    [anon_sym_namespace] = ACTIONS(42),
    [anon_sym_LBRACK] = ACTIONS(45),
    [anon_sym_STAR] = ACTIONS(48),
    [anon_sym_constraints] = ACTIONS(51),
    [anon_sym_BANG] = ACTIONS(54),
    [anon_sym_LPAREN] = ACTIONS(57),
    [anon_sym_true] = ACTIONS(60),
    [anon_sym_false] = ACTIONS(60),
    [sym_number] = ACTIONS(63),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(66),
    [anon_sym_alternative] = ACTIONS(66),
    [anon_sym_mandatory] = ACTIONS(66),
    [anon_sym_optional] = ACTIONS(66),
    [anon_sym_SMT_DASHlevel] = ACTIONS(69),
    [anon_sym_SAT_DASHlevel] = ACTIONS(69),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(69),
    [anon_sym_group_DASHcardinality] = ACTIONS(48),
    [anon_sym_feature_DASHcardinality] = ACTIONS(48),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(48),
    [anon_sym_type_DASHconstraints] = ACTIONS(48),
    [anon_sym_SQUOTE] = ACTIONS(72),
    [anon_sym_DQUOTE] = ACTIONS(75),
    [sym_imports] = ACTIONS(78),
    [sym_features] = ACTIONS(78),
    [sym_include] = ACTIONS(78),
    [sym__dedent] = ACTIONS(81),
  },
  [4] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(83),
  },
  [5] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(85),
  },
  [6] = {
    [sym_blk] = STATE(4),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(87),
  },
  [7] = {
    [sym_blk] = STATE(5),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(89),
  },
  [8] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(91),
  },
  [9] = {
    [sym_blk] = STATE(9),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(9),
    [ts_builtin_sym_end] = ACTIONS(81),
    [sym_name] = ACTIONS(39),
    [anon_sym_namespace] = ACTIONS(42),
    [anon_sym_LBRACK] = ACTIONS(45),
    [anon_sym_STAR] = ACTIONS(48),
    [anon_sym_constraints] = ACTIONS(51),
    [anon_sym_BANG] = ACTIONS(54),
    [anon_sym_LPAREN] = ACTIONS(57),
    [anon_sym_true] = ACTIONS(60),
    [anon_sym_false] = ACTIONS(60),
    [sym_number] = ACTIONS(63),
    [sym_comment] = ACTIONS(3),
    [anon_sym_or] = ACTIONS(66),
    [anon_sym_alternative] = ACTIONS(66),
    [anon_sym_mandatory] = ACTIONS(66),
    [anon_sym_optional] = ACTIONS(66),
    [anon_sym_SMT_DASHlevel] = ACTIONS(69),
    [anon_sym_SAT_DASHlevel] = ACTIONS(69),
    [anon_sym_TYPE_DASHlevel] = ACTIONS(69),
    [anon_sym_group_DASHcardinality] = ACTIONS(48),
    [anon_sym_feature_DASHcardinality] = ACTIONS(48),
    [anon_sym_aggregate_DASHfunction] = ACTIONS(48),
    [anon_sym_type_DASHconstraints] = ACTIONS(48),
    [anon_sym_SQUOTE] = ACTIONS(72),
    [anon_sym_DQUOTE] = ACTIONS(75),
    [sym_imports] = ACTIONS(93),
    [sym_features] = ACTIONS(93),
    [sym_include] = ACTIONS(93),
  },
  [10] = {
    [sym_blk] = STATE(9),
    [sym__header] = STATE(229),
    [sym_typed_feature] = STATE(229),
    [sym_ref] = STATE(229),
    [sym_namespace] = STATE(229),
    [sym_incomplete_namespace] = STATE(229),
    [sym_incomplete_ref] = STATE(229),
    [sym_cardinality] = STATE(229),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(229),
    [sym_group_mode] = STATE(229),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(229),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(9),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(33),
    [sym_features] = ACTIONS(33),
    [sym_include] = ACTIONS(33),
  },
  [11] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(98),
  },
  [12] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(100),
  },
  [13] = {
    [sym_blk] = STATE(19),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(102),
  },
  [14] = {
    [sym_blk] = STATE(12),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(104),
  },
  [15] = {
    [sym_blk] = STATE(20),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(106),
  },
  [16] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(108),
  },
  [17] = {
    [sym_blk] = STATE(8),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(110),
  },
  [18] = {
    [sym_blk] = STATE(11),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
    [sym__any_name] = STATE(65),
    [aux_sym_source_file_repeat1] = STATE(11),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(112),
  },
  [19] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
    [sym__dedent] = ACTIONS(114),
  },
  [20] = {
    [sym_blk] = STATE(3),
    [sym__header] = STATE(226),
    [sym_typed_feature] = STATE(226),
    [sym_ref] = STATE(226),
    [sym_namespace] = STATE(226),
    [sym_incomplete_namespace] = STATE(226),
    [sym_incomplete_ref] = STATE(226),
    [sym_cardinality] = STATE(226),
    [sym__expr] = STATE(155),
    [sym_unary_expr] = STATE(150),
    [sym_binary_expr] = STATE(150),
    [sym_nested_expr] = STATE(150),
    [sym_function] = STATE(150),
    [sym_bool] = STATE(150),
    [sym_path] = STATE(124),
    [sym_lang_lvl] = STATE(226),
    [sym_group_mode] = STATE(226),
    [sym_major_lvl] = STATE(219),
    [sym_minor_lvl] = STATE(219),
    [sym_string] = STATE(150),
    [sym_string_name] = STATE(65),
    [sym_constraints] = STATE(226),
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
    [anon_sym_SQUOTE] = ACTIONS(29),
    [anon_sym_DQUOTE] = ACTIONS(31),
    [sym_imports] = ACTIONS(35),
    [sym_features] = ACTIONS(35),
    [sym_include] = ACTIONS(35),
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
    ACTIONS(118), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [38] = 4,
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
    ACTIONS(124), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [76] = 3,
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
    ACTIONS(130), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [112] = 4,
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
    ACTIONS(134), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [150] = 3,
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
    ACTIONS(142), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [186] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(144), 12,
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
    ACTIONS(146), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [222] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(150), 12,
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
    ACTIONS(148), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [258] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(150), 12,
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
    ACTIONS(148), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [294] = 3,
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
    ACTIONS(130), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [330] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(144), 12,
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
    ACTIONS(146), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [366] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(152), 1,
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
    ACTIONS(124), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [404] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(158), 1,
      sym__indent,
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
    ACTIONS(156), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [442] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(162), 12,
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
    ACTIONS(160), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [478] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(162), 12,
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
    ACTIONS(160), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [514] = 3,
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
    ACTIONS(142), 16,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [550] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(164), 1,
      sym_name,
    STATE(120), 2,
      sym_string_name,
      sym__any_name,
    STATE(224), 2,
      sym_major_lvl,
      sym_minor_lvl,
    ACTIONS(27), 3,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
    ACTIONS(166), 4,
      anon_sym_cardinality,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(13), 5,
      anon_sym_STAR,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
    ACTIONS(168), 10,
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
  [598] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(170), 1,
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
    ACTIONS(134), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [636] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(172), 1,
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
    ACTIONS(118), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [674] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(174), 1,
      sym__indent,
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
    ACTIONS(156), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [712] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(176), 12,
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
    ACTIONS(178), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [747] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(176), 12,
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
    ACTIONS(178), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [782] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(180), 12,
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
    ACTIONS(182), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [817] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(184), 12,
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
    ACTIONS(186), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [852] = 3,
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
    ACTIONS(190), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [887] = 3,
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
    ACTIONS(194), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [922] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(198), 12,
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
    ACTIONS(196), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [957] = 3,
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
    ACTIONS(190), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [992] = 3,
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
    ACTIONS(200), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1027] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(206), 12,
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
    ACTIONS(204), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1062] = 3,
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
    ACTIONS(194), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1097] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(184), 12,
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
    ACTIONS(186), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1132] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(198), 12,
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
    ACTIONS(196), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1167] = 3,
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
    ACTIONS(200), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1202] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(180), 12,
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
    ACTIONS(182), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1237] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(206), 12,
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
    ACTIONS(204), 15,
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
      anon_sym_SQUOTE,
      anon_sym_DQUOTE,
  [1272] = 15,
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
    STATE(179), 1,
      sym__expr,
    ACTIONS(212), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(129), 2,
      sym_string_name,
      sym__any_name,
    STATE(271), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(159), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1329] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 5,
      anon_sym_LT,
      anon_sym_SLASH,
      anon_sym_true,
      anon_sym_false,
      sym_name,
    ACTIONS(230), 19,
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
  [1361] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(234), 1,
      anon_sym_LBRACE,
    ACTIONS(236), 1,
      anon_sym_LBRACK,
    ACTIONS(238), 1,
      anon_sym_RBRACK,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(174), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(282), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1417] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(234), 1,
      anon_sym_LBRACE,
    ACTIONS(236), 1,
      anon_sym_LBRACK,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    ACTIONS(252), 1,
      anon_sym_RBRACK,
    STATE(174), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(282), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1473] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(234), 1,
      anon_sym_LBRACE,
    ACTIONS(236), 1,
      anon_sym_LBRACK,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    ACTIONS(254), 1,
      anon_sym_RBRACK,
    STATE(174), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(282), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1529] = 15,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(234), 1,
      anon_sym_LBRACE,
    ACTIONS(236), 1,
      anon_sym_LBRACK,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    ACTIONS(256), 1,
      anon_sym_RBRACK,
    STATE(174), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(282), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1585] = 14,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(234), 1,
      anon_sym_LBRACE,
    ACTIONS(236), 1,
      anon_sym_LBRACK,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(174), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(260), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1638] = 14,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(234), 1,
      anon_sym_LBRACE,
    ACTIONS(236), 1,
      anon_sym_LBRACK,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(174), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(282), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1691] = 14,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(234), 1,
      anon_sym_LBRACE,
    ACTIONS(236), 1,
      anon_sym_LBRACK,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(174), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(249), 3,
      sym_attributes,
      sym__value,
      sym_vector,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [1744] = 11,
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
    STATE(109), 1,
      aux_sym_path_repeat1,
    STATE(220), 1,
      aux_sym_lang_lvl_repeat1,
    ACTIONS(262), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(240), 2,
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
  [1790] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(276), 1,
      anon_sym_RPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [1835] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(286), 1,
      anon_sym_RPAREN,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [1880] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(292), 1,
      anon_sym_LPAREN,
    ACTIONS(288), 5,
      anon_sym_cardinality,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
      sym_name,
    ACTIONS(290), 13,
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
  [1909] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(294), 1,
      anon_sym_RPAREN,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [1954] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(296), 1,
      sym_name,
    STATE(119), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(298), 4,
      anon_sym_cardinality,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(300), 11,
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
  [1987] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(302), 1,
      anon_sym_RPAREN,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2032] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    ACTIONS(304), 1,
      anon_sym_RBRACK,
    STATE(193), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2077] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(306), 1,
      anon_sym_RPAREN,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2122] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(308), 1,
      anon_sym_RPAREN,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2167] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(310), 1,
      anon_sym_RPAREN,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2212] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    ACTIONS(312), 1,
      anon_sym_RBRACK,
    STATE(193), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2257] = 12,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(314), 1,
      anon_sym_RPAREN,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2302] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 5,
      anon_sym_cardinality,
      anon_sym_as,
      anon_sym_LT,
      anon_sym_SLASH,
      sym_name,
    ACTIONS(230), 13,
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
  [2328] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(169), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2370] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(296), 1,
      sym_name,
    STATE(119), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(166), 3,
      anon_sym_cardinality,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(168), 11,
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
  [2402] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(199), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2444] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(202), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2486] = 11,
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
    STATE(187), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(129), 2,
      sym_string_name,
      sym__any_name,
    STATE(159), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2528] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(144), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2570] = 11,
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
    STATE(188), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(129), 2,
      sym_string_name,
      sym__any_name,
    STATE(159), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2612] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(198), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2654] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(185), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2696] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(184), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [2738] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(156), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2780] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(143), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2822] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(171), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2864] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(170), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2906] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(160), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2948] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(138), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [2990] = 11,
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
    STATE(163), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(129), 2,
      sym_string_name,
      sym__any_name,
    STATE(159), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3032] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(183), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3074] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(200), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [3116] = 11,
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
    STATE(118), 2,
      sym_string_name,
      sym__any_name,
    STATE(150), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3158] = 11,
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
    STATE(189), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(129), 2,
      sym_string_name,
      sym__any_name,
    STATE(159), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3200] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(201), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [3242] = 11,
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
    STATE(190), 1,
      sym__expr,
    ACTIONS(220), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(129), 2,
      sym_string_name,
      sym__any_name,
    STATE(159), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3284] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(149), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [3326] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(270), 1,
      sym_name,
    ACTIONS(272), 1,
      anon_sym_BANG,
    ACTIONS(274), 1,
      anon_sym_LPAREN,
    ACTIONS(280), 1,
      sym_number,
    ACTIONS(282), 1,
      anon_sym_SQUOTE,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    STATE(166), 1,
      sym__expr,
    ACTIONS(278), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(128), 2,
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
  [3368] = 11,
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
    STATE(148), 1,
      sym__expr,
    ACTIONS(21), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(118), 2,
      sym_string_name,
      sym__any_name,
    STATE(150), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3410] = 11,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(232), 1,
      sym_name,
    ACTIONS(240), 1,
      anon_sym_BANG,
    ACTIONS(242), 1,
      anon_sym_LPAREN,
    ACTIONS(246), 1,
      sym_number,
    ACTIONS(248), 1,
      anon_sym_SQUOTE,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    STATE(193), 1,
      sym__expr,
    ACTIONS(244), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(125), 2,
      sym_string_name,
      sym__any_name,
    STATE(161), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3452] = 11,
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
    STATE(134), 1,
      sym__expr,
    ACTIONS(21), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(118), 2,
      sym_string_name,
      sym__any_name,
    STATE(150), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3494] = 11,
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
    STATE(136), 1,
      sym__expr,
    ACTIONS(21), 2,
      anon_sym_true,
      anon_sym_false,
    STATE(118), 2,
      sym_string_name,
      sym__any_name,
    STATE(150), 7,
      sym_unary_expr,
      sym_binary_expr,
      sym_nested_expr,
      sym_function,
      sym_bool,
      sym_path,
      sym_string,
  [3536] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(316), 1,
      sym_name,
    ACTIONS(298), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(145), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(300), 11,
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
  [3567] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(322), 1,
      anon_sym_DOT,
    STATE(114), 1,
      aux_sym_path_repeat1,
    ACTIONS(320), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(318), 13,
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
  [3596] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(324), 1,
      sym_name,
    ACTIONS(326), 1,
      anon_sym_cardinality,
    ACTIONS(328), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(224), 2,
      sym_major_lvl,
      sym_minor_lvl,
    STATE(227), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(27), 3,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
    ACTIONS(13), 5,
      anon_sym_STAR,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
  [3633] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    ACTIONS(330), 1,
      sym_name,
    ACTIONS(298), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(139), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(300), 11,
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
  [3664] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(324), 1,
      sym_name,
    ACTIONS(332), 1,
      anon_sym_cardinality,
    ACTIONS(334), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(224), 2,
      sym_major_lvl,
      sym_minor_lvl,
    STATE(227), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(27), 3,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
    ACTIONS(13), 5,
      anon_sym_STAR,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
  [3701] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(336), 1,
      sym_name,
    ACTIONS(298), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(137), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(300), 11,
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
  [3732] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(342), 1,
      anon_sym_DOT,
    STATE(114), 1,
      aux_sym_path_repeat1,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 13,
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
  [3761] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(316), 1,
      sym_name,
    ACTIONS(166), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(145), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(168), 11,
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
  [3792] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(336), 1,
      sym_name,
    ACTIONS(166), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(137), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(168), 11,
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
  [3823] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    ACTIONS(330), 1,
      sym_name,
    ACTIONS(166), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    STATE(139), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(168), 11,
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
  [3854] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(345), 1,
      anon_sym_DOT,
    STATE(109), 1,
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
  [3882] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 14,
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
  [3906] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 14,
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
  [3930] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(347), 1,
      anon_sym_DOT,
    STATE(121), 1,
      aux_sym_path_repeat1,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 11,
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
  [3957] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(350), 1,
      anon_sym_DOT,
    STATE(122), 1,
      aux_sym_path_repeat1,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 11,
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
  [3984] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(353), 1,
      anon_sym_DOT,
    STATE(121), 1,
      aux_sym_path_repeat1,
    ACTIONS(320), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(318), 11,
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
  [4011] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(357), 1,
      anon_sym_as,
    ACTIONS(361), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(355), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
    ACTIONS(359), 9,
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
    ACTIONS(363), 1,
      anon_sym_DOT,
    STATE(123), 1,
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
  [4065] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(365), 1,
      anon_sym_DOT,
    STATE(133), 1,
      aux_sym_path_repeat1,
    ACTIONS(320), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(318), 11,
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
  [4092] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(367), 1,
      anon_sym_LPAREN,
    ACTIONS(288), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(290), 12,
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
  [4117] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(369), 1,
      anon_sym_DOT,
    STATE(126), 1,
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
  [4144] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(371), 1,
      anon_sym_DOT,
    STATE(131), 1,
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
  [4171] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(373), 1,
      anon_sym_LPAREN,
    ACTIONS(288), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(290), 12,
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
  [4196] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(375), 1,
      anon_sym_DOT,
    STATE(122), 1,
      aux_sym_path_repeat1,
    ACTIONS(320), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(318), 11,
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
  [4223] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(377), 1,
      anon_sym_LPAREN,
    ACTIONS(288), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(290), 12,
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
  [4248] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(379), 1,
      anon_sym_DOT,
    STATE(133), 1,
      aux_sym_path_repeat1,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 11,
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
  [4275] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(388), 1,
      anon_sym_LT,
    ACTIONS(390), 1,
      anon_sym_SLASH,
    ACTIONS(386), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(384), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(382), 7,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4303] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(394), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(392), 12,
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
  [4325] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(390), 1,
      anon_sym_SLASH,
    ACTIONS(396), 1,
      anon_sym_LT,
    ACTIONS(384), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(382), 9,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
  [4351] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 12,
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
  [4373] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(398), 1,
      anon_sym_COMMA,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(410), 1,
      anon_sym_RPAREN,
    STATE(256), 1,
      aux_sym_function_repeat1,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4407] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 12,
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
  [4429] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(412), 12,
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
  [4451] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(418), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(416), 12,
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
  [4473] = 3,
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
  [4495] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(424), 1,
      anon_sym_COMMA,
    ACTIONS(426), 1,
      anon_sym_RPAREN,
    STATE(243), 1,
      aux_sym_function_repeat1,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4529] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(428), 1,
      anon_sym_COMMA,
    ACTIONS(432), 1,
      anon_sym_RBRACK,
    ACTIONS(438), 1,
      anon_sym_LT,
    ACTIONS(440), 1,
      anon_sym_SLASH,
    STATE(233), 1,
      aux_sym_attribute_constraints_repeat1,
    ACTIONS(436), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(430), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(434), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4563] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(340), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(338), 12,
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
  [4585] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(444), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(442), 12,
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
  [4607] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(448), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(446), 12,
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
  [4629] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(396), 2,
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
  [4651] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(450), 1,
      anon_sym_COMMA,
    ACTIONS(452), 1,
      anon_sym_RPAREN,
    STATE(234), 1,
      aux_sym_function_repeat1,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4685] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(361), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(359), 12,
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
  [4707] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(324), 1,
      sym_name,
    STATE(224), 2,
      sym_major_lvl,
      sym_minor_lvl,
    STATE(227), 2,
      sym_string_name,
      sym__any_name,
    ACTIONS(27), 3,
      anon_sym_SMT_DASHlevel,
      anon_sym_SAT_DASHlevel,
      anon_sym_TYPE_DASHlevel,
    ACTIONS(13), 5,
      anon_sym_STAR,
      anon_sym_group_DASHcardinality,
      anon_sym_feature_DASHcardinality,
      anon_sym_aggregate_DASHfunction,
      anon_sym_type_DASHconstraints,
  [4737] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(456), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(454), 12,
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
  [4759] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(460), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(458), 12,
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
  [4781] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(230), 12,
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
  [4803] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(388), 1,
      anon_sym_LT,
    ACTIONS(390), 1,
      anon_sym_SLASH,
    ACTIONS(386), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(384), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(462), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
    ACTIONS(464), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4833] = 9,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(466), 1,
      anon_sym_COMMA,
    ACTIONS(468), 1,
      anon_sym_RPAREN,
    STATE(236), 1,
      aux_sym_function_repeat1,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4867] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(228), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(230), 12,
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
  [4889] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(460), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(458), 11,
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
  [4910] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(361), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(359), 11,
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
  [4931] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(470), 2,
      anon_sym_COMMA,
      anon_sym_RPAREN,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [4960] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(361), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(359), 11,
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
  [4981] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(394), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(392), 11,
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
  [5002] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(480), 1,
      anon_sym_LT,
    ACTIONS(482), 1,
      anon_sym_SLASH,
    ACTIONS(472), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
    ACTIONS(478), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(474), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(476), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5031] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(394), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(392), 11,
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
  [5052] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(361), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(359), 11,
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
  [5073] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(412), 11,
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
  [5094] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(418), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(416), 11,
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
  [5115] = 3,
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
  [5136] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(396), 2,
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
  [5157] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(382), 6,
      anon_sym_COMMA,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_RPAREN,
  [5184] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(396), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(382), 8,
      anon_sym_COMMA,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
      anon_sym_RPAREN,
  [5209] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(456), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(454), 11,
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
  [5230] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(460), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(458), 11,
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
  [5251] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(438), 1,
      anon_sym_LT,
    ACTIONS(440), 1,
      anon_sym_SLASH,
    ACTIONS(436), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(484), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
    ACTIONS(430), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(434), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5280] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(444), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(442), 11,
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
  [5301] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(448), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(446), 11,
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
  [5322] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(444), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(442), 11,
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
  [5343] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(448), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(446), 11,
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
  [5364] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(480), 1,
      anon_sym_LT,
    ACTIONS(482), 1,
      anon_sym_SLASH,
    ACTIONS(478), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(484), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
    ACTIONS(474), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(476), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5393] = 3,
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
  [5414] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(418), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(416), 11,
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
  [5435] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(456), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(454), 11,
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
  [5456] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(412), 11,
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
  [5477] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(396), 2,
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
  [5498] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(438), 1,
      anon_sym_LT,
    ACTIONS(440), 1,
      anon_sym_SLASH,
    ACTIONS(436), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(430), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(382), 6,
      anon_sym_COMMA,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5525] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(394), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(392), 11,
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
  [5546] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(396), 1,
      anon_sym_LT,
    ACTIONS(482), 1,
      anon_sym_SLASH,
    ACTIONS(474), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(382), 8,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
  [5571] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(480), 1,
      anon_sym_LT,
    ACTIONS(482), 1,
      anon_sym_SLASH,
    ACTIONS(478), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(474), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(382), 6,
      anon_sym_COMMA,
      anon_sym_RBRACE,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5598] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(396), 2,
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
  [5619] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(414), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(412), 11,
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
  [5640] = 3,
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
  [5661] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(444), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(442), 11,
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
  [5682] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(438), 1,
      anon_sym_LT,
    ACTIONS(440), 1,
      anon_sym_SLASH,
    ACTIONS(436), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(486), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
    ACTIONS(430), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(434), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5711] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(448), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(446), 11,
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
  [5732] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(456), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(454), 11,
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
  [5753] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(418), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(416), 11,
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
  [5774] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(460), 2,
      anon_sym_LT,
      anon_sym_SLASH,
    ACTIONS(458), 11,
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
  [5795] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(396), 1,
      anon_sym_LT,
    ACTIONS(440), 1,
      anon_sym_SLASH,
    ACTIONS(430), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(382), 8,
      anon_sym_COMMA,
      anon_sym_RBRACK,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
      anon_sym_GT,
      anon_sym_EQ_EQ,
  [5820] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(488), 1,
      anon_sym_RPAREN,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5848] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(490), 1,
      anon_sym_RPAREN,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5876] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(492), 1,
      anon_sym_RPAREN,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5904] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(406), 1,
      anon_sym_LT,
    ACTIONS(408), 1,
      anon_sym_SLASH,
    ACTIONS(494), 1,
      anon_sym_RPAREN,
    ACTIONS(404), 2,
      anon_sym_GT,
      anon_sym_EQ_EQ,
    ACTIONS(400), 3,
      anon_sym_STAR,
      anon_sym_PLUS,
      anon_sym_DASH,
    ACTIONS(402), 4,
      anon_sym_PIPE,
      anon_sym_AMP,
      anon_sym_EQ_GT,
      anon_sym_LT_EQ_GT,
  [5932] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(498), 1,
      anon_sym_RBRACE,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [5961] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(504), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(253), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [5990] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(506), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6019] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(508), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6048] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(510), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(254), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6077] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(512), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(247), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6106] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(514), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6135] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(516), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6164] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(518), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6193] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(520), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(238), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6222] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(522), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6251] = 8,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    ACTIONS(524), 1,
      anon_sym_RBRACE,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6280] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(496), 1,
      sym_name,
    ACTIONS(500), 1,
      anon_sym_constraint,
    ACTIONS(502), 1,
      anon_sym_constraints,
    STATE(56), 2,
      sym_string_name,
      sym__any_name,
    STATE(265), 4,
      sym_attribute_constraint,
      sym_attribute_constraints,
      sym_attribute_value,
      sym__attribute,
  [6306] = 7,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(526), 1,
      sym_name,
    ACTIONS(528), 1,
      anon_sym_cardinality,
    STATE(231), 1,
      sym_path,
    ACTIONS(530), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(118), 2,
      sym_string_name,
      sym__any_name,
  [6330] = 6,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(532), 1,
      sym_name,
    ACTIONS(534), 1,
      anon_sym_cardinality,
    ACTIONS(536), 2,
      sym__newline,
      anon_sym_LBRACE,
    STATE(251), 2,
      sym_string_name,
      sym__any_name,
  [6351] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(540), 1,
      anon_sym_DOT,
    STATE(218), 1,
      aux_sym_lang_lvl_repeat1,
    ACTIONS(538), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6366] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(545), 1,
      anon_sym_DOT,
    STATE(220), 1,
      aux_sym_lang_lvl_repeat1,
    ACTIONS(543), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6381] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(549), 1,
      anon_sym_DOT,
    STATE(218), 1,
      aux_sym_lang_lvl_repeat1,
    ACTIONS(547), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6396] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(551), 4,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_DOT,
  [6406] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(250), 1,
      anon_sym_DQUOTE,
    ACTIONS(330), 1,
      sym_name,
    STATE(139), 2,
      sym_string_name,
      sym__any_name,
  [6420] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(226), 1,
      anon_sym_DQUOTE,
    ACTIONS(336), 1,
      sym_name,
    STATE(137), 2,
      sym_string_name,
      sym__any_name,
  [6434] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(538), 4,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_DOT,
  [6444] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(31), 1,
      anon_sym_DQUOTE,
    ACTIONS(553), 1,
      sym_name,
    STATE(119), 2,
      sym_string_name,
      sym__any_name,
  [6458] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(555), 1,
      anon_sym_cardinality,
    ACTIONS(557), 1,
      anon_sym_LBRACE,
    ACTIONS(559), 1,
      sym__newline,
    STATE(31), 1,
      sym_attributes,
  [6474] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(538), 4,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_DOT,
  [6484] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(284), 1,
      anon_sym_DQUOTE,
    ACTIONS(316), 1,
      sym_name,
    STATE(145), 2,
      sym_string_name,
      sym__any_name,
  [6498] = 5,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(561), 1,
      anon_sym_cardinality,
    ACTIONS(563), 1,
      anon_sym_LBRACE,
    ACTIONS(565), 1,
      sym__newline,
    STATE(22), 1,
      sym_attributes,
  [6514] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(567), 4,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
      anon_sym_DOT,
  [6524] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(569), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6533] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(571), 1,
      anon_sym_COMMA,
    ACTIONS(574), 1,
      anon_sym_RBRACK,
    STATE(232), 1,
      aux_sym_attribute_constraints_repeat1,
  [6546] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(576), 1,
      anon_sym_COMMA,
    ACTIONS(578), 1,
      anon_sym_RBRACK,
    STATE(232), 1,
      aux_sym_attribute_constraints_repeat1,
  [6559] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(580), 1,
      anon_sym_COMMA,
    ACTIONS(582), 1,
      anon_sym_RPAREN,
    STATE(241), 1,
      aux_sym_function_repeat1,
  [6572] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(584), 1,
      anon_sym_COMMA,
    ACTIONS(586), 1,
      anon_sym_RBRACE,
    STATE(255), 1,
      aux_sym_attributes_repeat1,
  [6585] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(588), 1,
      anon_sym_COMMA,
    ACTIONS(590), 1,
      anon_sym_RPAREN,
    STATE(241), 1,
      aux_sym_function_repeat1,
  [6598] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(592), 1,
      anon_sym_COMMA,
    ACTIONS(594), 1,
      anon_sym_RBRACE,
    STATE(255), 1,
      aux_sym_attributes_repeat1,
  [6611] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(596), 1,
      anon_sym_COMMA,
    ACTIONS(598), 1,
      anon_sym_RBRACE,
    STATE(235), 1,
      aux_sym_attributes_repeat1,
  [6624] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(600), 1,
      anon_sym_COMMA,
    ACTIONS(602), 1,
      anon_sym_RBRACK,
    STATE(246), 1,
      aux_sym_vector_repeat1,
  [6637] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(604), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6646] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(606), 1,
      anon_sym_COMMA,
    ACTIONS(609), 1,
      anon_sym_RPAREN,
    STATE(241), 1,
      aux_sym_function_repeat1,
  [6659] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(611), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6668] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(613), 1,
      anon_sym_COMMA,
    ACTIONS(615), 1,
      anon_sym_RPAREN,
    STATE(241), 1,
      aux_sym_function_repeat1,
  [6681] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(617), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6690] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(619), 1,
      anon_sym_COMMA,
    ACTIONS(621), 1,
      anon_sym_RBRACE,
    STATE(255), 1,
      aux_sym_attributes_repeat1,
  [6703] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(623), 1,
      anon_sym_COMMA,
    ACTIONS(626), 1,
      anon_sym_RBRACK,
    STATE(246), 1,
      aux_sym_vector_repeat1,
  [6716] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(628), 1,
      anon_sym_COMMA,
    ACTIONS(630), 1,
      anon_sym_RBRACE,
    STATE(237), 1,
      aux_sym_attributes_repeat1,
  [6729] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(632), 1,
      anon_sym_COMMA,
    ACTIONS(634), 1,
      anon_sym_RBRACK,
    STATE(246), 1,
      aux_sym_vector_repeat1,
  [6742] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(636), 1,
      anon_sym_COMMA,
    ACTIONS(638), 1,
      anon_sym_RBRACK,
    STATE(248), 1,
      aux_sym_vector_repeat1,
  [6755] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(640), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6764] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(642), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6773] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(557), 1,
      anon_sym_LBRACE,
    ACTIONS(644), 1,
      sym__newline,
    STATE(37), 1,
      sym_attributes,
  [6786] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(646), 1,
      anon_sym_COMMA,
    ACTIONS(648), 1,
      anon_sym_RBRACE,
    STATE(259), 1,
      aux_sym_attributes_repeat1,
  [6799] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(650), 1,
      anon_sym_COMMA,
    ACTIONS(652), 1,
      anon_sym_RBRACE,
    STATE(245), 1,
      aux_sym_attributes_repeat1,
  [6812] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(654), 1,
      anon_sym_COMMA,
    ACTIONS(657), 1,
      anon_sym_RBRACE,
    STATE(255), 1,
      aux_sym_attributes_repeat1,
  [6825] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(659), 1,
      anon_sym_COMMA,
    ACTIONS(661), 1,
      anon_sym_RPAREN,
    STATE(241), 1,
      aux_sym_function_repeat1,
  [6838] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(563), 1,
      anon_sym_LBRACE,
    ACTIONS(663), 1,
      sym__newline,
    STATE(24), 1,
      sym_attributes,
  [6851] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(665), 3,
      sym__newline,
      anon_sym_cardinality,
      anon_sym_LBRACE,
  [6860] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(667), 1,
      anon_sym_COMMA,
    ACTIONS(669), 1,
      anon_sym_RBRACE,
    STATE(255), 1,
      aux_sym_attributes_repeat1,
  [6873] = 4,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(671), 1,
      anon_sym_COMMA,
    ACTIONS(673), 1,
      anon_sym_RBRACK,
    STATE(239), 1,
      aux_sym_vector_repeat1,
  [6886] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(675), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [6894] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(148), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [6902] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(677), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [6910] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(679), 2,
      anon_sym_STAR,
      sym_int,
  [6918] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(657), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [6926] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(681), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [6934] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(683), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [6942] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(11), 1,
      anon_sym_LBRACK,
    STATE(257), 1,
      sym_cardinality,
  [6952] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(681), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [6960] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(685), 1,
      anon_sym_STAR,
    ACTIONS(687), 1,
      sym_int,
  [6970] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(689), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [6978] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(142), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [6986] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(160), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [6994] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(675), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7002] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(146), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7010] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(130), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7018] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(691), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7026] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(693), 1,
      anon_sym_DOT_DOT,
    ACTIONS(695), 1,
      anon_sym_RBRACK,
  [7036] = 3,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(11), 1,
      anon_sym_LBRACK,
    STATE(252), 1,
      sym_cardinality,
  [7046] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(142), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7054] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(697), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7062] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(626), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7070] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(130), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7078] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(146), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7086] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(160), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7094] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(699), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7102] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(683), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7110] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(677), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7118] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(148), 2,
      anon_sym_COMMA,
      anon_sym_RBRACK,
  [7126] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(701), 2,
      anon_sym_COMMA,
      anon_sym_RBRACE,
  [7134] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(703), 1,
      anon_sym_SQUOTE,
  [7141] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(705), 1,
      anon_sym_DQUOTE,
  [7148] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(707), 1,
      anon_sym_DQUOTE,
  [7155] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(709), 1,
      anon_sym_LBRACK,
  [7162] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(711), 1,
      ts_builtin_sym_end,
  [7169] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(713), 1,
      anon_sym_RBRACK,
  [7176] = 2,
    ACTIONS(715), 1,
      sym_comment,
    ACTIONS(717), 1,
      aux_sym_string_name_token1,
  [7183] = 2,
    ACTIONS(715), 1,
      sym_comment,
    ACTIONS(719), 1,
      sym_string_content,
  [7190] = 2,
    ACTIONS(715), 1,
      sym_comment,
    ACTIONS(721), 1,
      aux_sym_string_name_token1,
  [7197] = 2,
    ACTIONS(715), 1,
      sym_comment,
    ACTIONS(723), 1,
      sym_string_content,
  [7204] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(695), 1,
      anon_sym_RBRACK,
  [7211] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(725), 1,
      anon_sym_SQUOTE,
  [7218] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(727), 1,
      anon_sym_DQUOTE,
  [7225] = 2,
    ACTIONS(715), 1,
      sym_comment,
    ACTIONS(729), 1,
      sym_string_content,
  [7232] = 2,
    ACTIONS(715), 1,
      sym_comment,
    ACTIONS(731), 1,
      aux_sym_string_name_token1,
  [7239] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(733), 1,
      anon_sym_DQUOTE,
  [7246] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(735), 1,
      anon_sym_SQUOTE,
  [7253] = 2,
    ACTIONS(715), 1,
      sym_comment,
    ACTIONS(737), 1,
      sym_string_content,
  [7260] = 2,
    ACTIONS(715), 1,
      sym_comment,
    ACTIONS(739), 1,
      aux_sym_string_name_token1,
  [7267] = 2,
    ACTIONS(3), 1,
      sym_comment,
    ACTIONS(741), 1,
      anon_sym_SQUOTE,
};

static const uint32_t ts_small_parse_table_map[] = {
  [SMALL_STATE(21)] = 0,
  [SMALL_STATE(22)] = 38,
  [SMALL_STATE(23)] = 76,
  [SMALL_STATE(24)] = 112,
  [SMALL_STATE(25)] = 150,
  [SMALL_STATE(26)] = 186,
  [SMALL_STATE(27)] = 222,
  [SMALL_STATE(28)] = 258,
  [SMALL_STATE(29)] = 294,
  [SMALL_STATE(30)] = 330,
  [SMALL_STATE(31)] = 366,
  [SMALL_STATE(32)] = 404,
  [SMALL_STATE(33)] = 442,
  [SMALL_STATE(34)] = 478,
  [SMALL_STATE(35)] = 514,
  [SMALL_STATE(36)] = 550,
  [SMALL_STATE(37)] = 598,
  [SMALL_STATE(38)] = 636,
  [SMALL_STATE(39)] = 674,
  [SMALL_STATE(40)] = 712,
  [SMALL_STATE(41)] = 747,
  [SMALL_STATE(42)] = 782,
  [SMALL_STATE(43)] = 817,
  [SMALL_STATE(44)] = 852,
  [SMALL_STATE(45)] = 887,
  [SMALL_STATE(46)] = 922,
  [SMALL_STATE(47)] = 957,
  [SMALL_STATE(48)] = 992,
  [SMALL_STATE(49)] = 1027,
  [SMALL_STATE(50)] = 1062,
  [SMALL_STATE(51)] = 1097,
  [SMALL_STATE(52)] = 1132,
  [SMALL_STATE(53)] = 1167,
  [SMALL_STATE(54)] = 1202,
  [SMALL_STATE(55)] = 1237,
  [SMALL_STATE(56)] = 1272,
  [SMALL_STATE(57)] = 1329,
  [SMALL_STATE(58)] = 1361,
  [SMALL_STATE(59)] = 1417,
  [SMALL_STATE(60)] = 1473,
  [SMALL_STATE(61)] = 1529,
  [SMALL_STATE(62)] = 1585,
  [SMALL_STATE(63)] = 1638,
  [SMALL_STATE(64)] = 1691,
  [SMALL_STATE(65)] = 1744,
  [SMALL_STATE(66)] = 1790,
  [SMALL_STATE(67)] = 1835,
  [SMALL_STATE(68)] = 1880,
  [SMALL_STATE(69)] = 1909,
  [SMALL_STATE(70)] = 1954,
  [SMALL_STATE(71)] = 1987,
  [SMALL_STATE(72)] = 2032,
  [SMALL_STATE(73)] = 2077,
  [SMALL_STATE(74)] = 2122,
  [SMALL_STATE(75)] = 2167,
  [SMALL_STATE(76)] = 2212,
  [SMALL_STATE(77)] = 2257,
  [SMALL_STATE(78)] = 2302,
  [SMALL_STATE(79)] = 2328,
  [SMALL_STATE(80)] = 2370,
  [SMALL_STATE(81)] = 2402,
  [SMALL_STATE(82)] = 2444,
  [SMALL_STATE(83)] = 2486,
  [SMALL_STATE(84)] = 2528,
  [SMALL_STATE(85)] = 2570,
  [SMALL_STATE(86)] = 2612,
  [SMALL_STATE(87)] = 2654,
  [SMALL_STATE(88)] = 2696,
  [SMALL_STATE(89)] = 2738,
  [SMALL_STATE(90)] = 2780,
  [SMALL_STATE(91)] = 2822,
  [SMALL_STATE(92)] = 2864,
  [SMALL_STATE(93)] = 2906,
  [SMALL_STATE(94)] = 2948,
  [SMALL_STATE(95)] = 2990,
  [SMALL_STATE(96)] = 3032,
  [SMALL_STATE(97)] = 3074,
  [SMALL_STATE(98)] = 3116,
  [SMALL_STATE(99)] = 3158,
  [SMALL_STATE(100)] = 3200,
  [SMALL_STATE(101)] = 3242,
  [SMALL_STATE(102)] = 3284,
  [SMALL_STATE(103)] = 3326,
  [SMALL_STATE(104)] = 3368,
  [SMALL_STATE(105)] = 3410,
  [SMALL_STATE(106)] = 3452,
  [SMALL_STATE(107)] = 3494,
  [SMALL_STATE(108)] = 3536,
  [SMALL_STATE(109)] = 3567,
  [SMALL_STATE(110)] = 3596,
  [SMALL_STATE(111)] = 3633,
  [SMALL_STATE(112)] = 3664,
  [SMALL_STATE(113)] = 3701,
  [SMALL_STATE(114)] = 3732,
  [SMALL_STATE(115)] = 3761,
  [SMALL_STATE(116)] = 3792,
  [SMALL_STATE(117)] = 3823,
  [SMALL_STATE(118)] = 3854,
  [SMALL_STATE(119)] = 3882,
  [SMALL_STATE(120)] = 3906,
  [SMALL_STATE(121)] = 3930,
  [SMALL_STATE(122)] = 3957,
  [SMALL_STATE(123)] = 3984,
  [SMALL_STATE(124)] = 4011,
  [SMALL_STATE(125)] = 4038,
  [SMALL_STATE(126)] = 4065,
  [SMALL_STATE(127)] = 4092,
  [SMALL_STATE(128)] = 4117,
  [SMALL_STATE(129)] = 4144,
  [SMALL_STATE(130)] = 4171,
  [SMALL_STATE(131)] = 4196,
  [SMALL_STATE(132)] = 4223,
  [SMALL_STATE(133)] = 4248,
  [SMALL_STATE(134)] = 4275,
  [SMALL_STATE(135)] = 4303,
  [SMALL_STATE(136)] = 4325,
  [SMALL_STATE(137)] = 4351,
  [SMALL_STATE(138)] = 4373,
  [SMALL_STATE(139)] = 4407,
  [SMALL_STATE(140)] = 4429,
  [SMALL_STATE(141)] = 4451,
  [SMALL_STATE(142)] = 4473,
  [SMALL_STATE(143)] = 4495,
  [SMALL_STATE(144)] = 4529,
  [SMALL_STATE(145)] = 4563,
  [SMALL_STATE(146)] = 4585,
  [SMALL_STATE(147)] = 4607,
  [SMALL_STATE(148)] = 4629,
  [SMALL_STATE(149)] = 4651,
  [SMALL_STATE(150)] = 4685,
  [SMALL_STATE(151)] = 4707,
  [SMALL_STATE(152)] = 4737,
  [SMALL_STATE(153)] = 4759,
  [SMALL_STATE(154)] = 4781,
  [SMALL_STATE(155)] = 4803,
  [SMALL_STATE(156)] = 4833,
  [SMALL_STATE(157)] = 4867,
  [SMALL_STATE(158)] = 4889,
  [SMALL_STATE(159)] = 4910,
  [SMALL_STATE(160)] = 4931,
  [SMALL_STATE(161)] = 4960,
  [SMALL_STATE(162)] = 4981,
  [SMALL_STATE(163)] = 5002,
  [SMALL_STATE(164)] = 5031,
  [SMALL_STATE(165)] = 5052,
  [SMALL_STATE(166)] = 5073,
  [SMALL_STATE(167)] = 5094,
  [SMALL_STATE(168)] = 5115,
  [SMALL_STATE(169)] = 5136,
  [SMALL_STATE(170)] = 5157,
  [SMALL_STATE(171)] = 5184,
  [SMALL_STATE(172)] = 5209,
  [SMALL_STATE(173)] = 5230,
  [SMALL_STATE(174)] = 5251,
  [SMALL_STATE(175)] = 5280,
  [SMALL_STATE(176)] = 5301,
  [SMALL_STATE(177)] = 5322,
  [SMALL_STATE(178)] = 5343,
  [SMALL_STATE(179)] = 5364,
  [SMALL_STATE(180)] = 5393,
  [SMALL_STATE(181)] = 5414,
  [SMALL_STATE(182)] = 5435,
  [SMALL_STATE(183)] = 5456,
  [SMALL_STATE(184)] = 5477,
  [SMALL_STATE(185)] = 5498,
  [SMALL_STATE(186)] = 5525,
  [SMALL_STATE(187)] = 5546,
  [SMALL_STATE(188)] = 5571,
  [SMALL_STATE(189)] = 5598,
  [SMALL_STATE(190)] = 5619,
  [SMALL_STATE(191)] = 5640,
  [SMALL_STATE(192)] = 5661,
  [SMALL_STATE(193)] = 5682,
  [SMALL_STATE(194)] = 5711,
  [SMALL_STATE(195)] = 5732,
  [SMALL_STATE(196)] = 5753,
  [SMALL_STATE(197)] = 5774,
  [SMALL_STATE(198)] = 5795,
  [SMALL_STATE(199)] = 5820,
  [SMALL_STATE(200)] = 5848,
  [SMALL_STATE(201)] = 5876,
  [SMALL_STATE(202)] = 5904,
  [SMALL_STATE(203)] = 5932,
  [SMALL_STATE(204)] = 5961,
  [SMALL_STATE(205)] = 5990,
  [SMALL_STATE(206)] = 6019,
  [SMALL_STATE(207)] = 6048,
  [SMALL_STATE(208)] = 6077,
  [SMALL_STATE(209)] = 6106,
  [SMALL_STATE(210)] = 6135,
  [SMALL_STATE(211)] = 6164,
  [SMALL_STATE(212)] = 6193,
  [SMALL_STATE(213)] = 6222,
  [SMALL_STATE(214)] = 6251,
  [SMALL_STATE(215)] = 6280,
  [SMALL_STATE(216)] = 6306,
  [SMALL_STATE(217)] = 6330,
  [SMALL_STATE(218)] = 6351,
  [SMALL_STATE(219)] = 6366,
  [SMALL_STATE(220)] = 6381,
  [SMALL_STATE(221)] = 6396,
  [SMALL_STATE(222)] = 6406,
  [SMALL_STATE(223)] = 6420,
  [SMALL_STATE(224)] = 6434,
  [SMALL_STATE(225)] = 6444,
  [SMALL_STATE(226)] = 6458,
  [SMALL_STATE(227)] = 6474,
  [SMALL_STATE(228)] = 6484,
  [SMALL_STATE(229)] = 6498,
  [SMALL_STATE(230)] = 6514,
  [SMALL_STATE(231)] = 6524,
  [SMALL_STATE(232)] = 6533,
  [SMALL_STATE(233)] = 6546,
  [SMALL_STATE(234)] = 6559,
  [SMALL_STATE(235)] = 6572,
  [SMALL_STATE(236)] = 6585,
  [SMALL_STATE(237)] = 6598,
  [SMALL_STATE(238)] = 6611,
  [SMALL_STATE(239)] = 6624,
  [SMALL_STATE(240)] = 6637,
  [SMALL_STATE(241)] = 6646,
  [SMALL_STATE(242)] = 6659,
  [SMALL_STATE(243)] = 6668,
  [SMALL_STATE(244)] = 6681,
  [SMALL_STATE(245)] = 6690,
  [SMALL_STATE(246)] = 6703,
  [SMALL_STATE(247)] = 6716,
  [SMALL_STATE(248)] = 6729,
  [SMALL_STATE(249)] = 6742,
  [SMALL_STATE(250)] = 6755,
  [SMALL_STATE(251)] = 6764,
  [SMALL_STATE(252)] = 6773,
  [SMALL_STATE(253)] = 6786,
  [SMALL_STATE(254)] = 6799,
  [SMALL_STATE(255)] = 6812,
  [SMALL_STATE(256)] = 6825,
  [SMALL_STATE(257)] = 6838,
  [SMALL_STATE(258)] = 6851,
  [SMALL_STATE(259)] = 6860,
  [SMALL_STATE(260)] = 6873,
  [SMALL_STATE(261)] = 6886,
  [SMALL_STATE(262)] = 6894,
  [SMALL_STATE(263)] = 6902,
  [SMALL_STATE(264)] = 6910,
  [SMALL_STATE(265)] = 6918,
  [SMALL_STATE(266)] = 6926,
  [SMALL_STATE(267)] = 6934,
  [SMALL_STATE(268)] = 6942,
  [SMALL_STATE(269)] = 6952,
  [SMALL_STATE(270)] = 6960,
  [SMALL_STATE(271)] = 6970,
  [SMALL_STATE(272)] = 6978,
  [SMALL_STATE(273)] = 6986,
  [SMALL_STATE(274)] = 6994,
  [SMALL_STATE(275)] = 7002,
  [SMALL_STATE(276)] = 7010,
  [SMALL_STATE(277)] = 7018,
  [SMALL_STATE(278)] = 7026,
  [SMALL_STATE(279)] = 7036,
  [SMALL_STATE(280)] = 7046,
  [SMALL_STATE(281)] = 7054,
  [SMALL_STATE(282)] = 7062,
  [SMALL_STATE(283)] = 7070,
  [SMALL_STATE(284)] = 7078,
  [SMALL_STATE(285)] = 7086,
  [SMALL_STATE(286)] = 7094,
  [SMALL_STATE(287)] = 7102,
  [SMALL_STATE(288)] = 7110,
  [SMALL_STATE(289)] = 7118,
  [SMALL_STATE(290)] = 7126,
  [SMALL_STATE(291)] = 7134,
  [SMALL_STATE(292)] = 7141,
  [SMALL_STATE(293)] = 7148,
  [SMALL_STATE(294)] = 7155,
  [SMALL_STATE(295)] = 7162,
  [SMALL_STATE(296)] = 7169,
  [SMALL_STATE(297)] = 7176,
  [SMALL_STATE(298)] = 7183,
  [SMALL_STATE(299)] = 7190,
  [SMALL_STATE(300)] = 7197,
  [SMALL_STATE(301)] = 7204,
  [SMALL_STATE(302)] = 7211,
  [SMALL_STATE(303)] = 7218,
  [SMALL_STATE(304)] = 7225,
  [SMALL_STATE(305)] = 7232,
  [SMALL_STATE(306)] = 7239,
  [SMALL_STATE(307)] = 7246,
  [SMALL_STATE(308)] = 7253,
  [SMALL_STATE(309)] = 7260,
  [SMALL_STATE(310)] = 7267,
};

static const TSParseActionEntry ts_parse_actions[] = {
  [0] = {.entry = {.count = 0, .reusable = false}},
  [1] = {.entry = {.count = 1, .reusable = false}}, RECOVER(),
  [3] = {.entry = {.count = 1, .reusable = true}}, SHIFT_EXTRA(),
  [5] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_source_file, 0),
  [7] = {.entry = {.count = 1, .reusable = false}}, SHIFT(68),
  [9] = {.entry = {.count = 1, .reusable = false}}, SHIFT(216),
  [11] = {.entry = {.count = 1, .reusable = true}}, SHIFT(270),
  [13] = {.entry = {.count = 1, .reusable = true}}, SHIFT(230),
  [15] = {.entry = {.count = 1, .reusable = false}}, SHIFT(250),
  [17] = {.entry = {.count = 1, .reusable = true}}, SHIFT(98),
  [19] = {.entry = {.count = 1, .reusable = true}}, SHIFT(100),
  [21] = {.entry = {.count = 1, .reusable = false}}, SHIFT(135),
  [23] = {.entry = {.count = 1, .reusable = true}}, SHIFT(150),
  [25] = {.entry = {.count = 1, .reusable = false}}, SHIFT(244),
  [27] = {.entry = {.count = 1, .reusable = true}}, SHIFT(221),
  [29] = {.entry = {.count = 1, .reusable = true}}, SHIFT(300),
  [31] = {.entry = {.count = 1, .reusable = true}}, SHIFT(297),
  [33] = {.entry = {.count = 1, .reusable = false}}, SHIFT(229),
  [35] = {.entry = {.count = 1, .reusable = false}}, SHIFT(226),
  [37] = {.entry = {.count = 1, .reusable = true}}, SHIFT(47),
  [39] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(68),
  [42] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(216),
  [45] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(270),
  [48] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(230),
  [51] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(250),
  [54] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(98),
  [57] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(100),
  [60] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(135),
  [63] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(150),
  [66] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(244),
  [69] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(221),
  [72] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(300),
  [75] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(297),
  [78] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(226),
  [81] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_source_file_repeat1, 2),
  [83] = {.entry = {.count = 1, .reusable = true}}, SHIFT(48),
  [85] = {.entry = {.count = 1, .reusable = true}}, SHIFT(51),
  [87] = {.entry = {.count = 1, .reusable = true}}, SHIFT(41),
  [89] = {.entry = {.count = 1, .reusable = true}}, SHIFT(49),
  [91] = {.entry = {.count = 1, .reusable = true}}, SHIFT(46),
  [93] = {.entry = {.count = 2, .reusable = false}}, REDUCE(aux_sym_source_file_repeat1, 2), SHIFT_REPEAT(229),
  [96] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_source_file, 1),
  [98] = {.entry = {.count = 1, .reusable = true}}, SHIFT(52),
  [100] = {.entry = {.count = 1, .reusable = true}}, SHIFT(45),
  [102] = {.entry = {.count = 1, .reusable = true}}, SHIFT(40),
  [104] = {.entry = {.count = 1, .reusable = true}}, SHIFT(44),
  [106] = {.entry = {.count = 1, .reusable = true}}, SHIFT(55),
  [108] = {.entry = {.count = 1, .reusable = true}}, SHIFT(50),
  [110] = {.entry = {.count = 1, .reusable = true}}, SHIFT(54),
  [112] = {.entry = {.count = 1, .reusable = true}}, SHIFT(42),
  [114] = {.entry = {.count = 1, .reusable = true}}, SHIFT(53),
  [116] = {.entry = {.count = 1, .reusable = true}}, SHIFT(43),
  [118] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 4, .production_id = 16),
  [120] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 4, .production_id = 16),
  [122] = {.entry = {.count = 1, .reusable = true}}, SHIFT(7),
  [124] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 2, .production_id = 6),
  [126] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 2, .production_id = 6),
  [128] = {.entry = {.count = 1, .reusable = true}}, SHIFT(17),
  [130] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 3),
  [132] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 3),
  [134] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 4, .production_id = 17),
  [136] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 4, .production_id = 17),
  [138] = {.entry = {.count = 1, .reusable = true}}, SHIFT(6),
  [140] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 5, .production_id = 33),
  [142] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 5, .production_id = 33),
  [144] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 4),
  [146] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 4),
  [148] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 4, .production_id = 13),
  [150] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 4, .production_id = 13),
  [152] = {.entry = {.count = 1, .reusable = true}}, SHIFT(18),
  [154] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 2, .production_id = 5),
  [156] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 2, .production_id = 5),
  [158] = {.entry = {.count = 1, .reusable = true}}, SHIFT(14),
  [160] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attributes, 2),
  [162] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_attributes, 2),
  [164] = {.entry = {.count = 1, .reusable = false}}, SHIFT(120),
  [166] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_path, 2, .production_id = 7),
  [168] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_path, 2, .production_id = 7),
  [170] = {.entry = {.count = 1, .reusable = true}}, SHIFT(13),
  [172] = {.entry = {.count = 1, .reusable = true}}, SHIFT(15),
  [174] = {.entry = {.count = 1, .reusable = true}}, SHIFT(2),
  [176] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 6, .production_id = 31),
  [178] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 6, .production_id = 31),
  [180] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 4, .production_id = 21),
  [182] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 4, .production_id = 21),
  [184] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 7, .production_id = 34),
  [186] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 7, .production_id = 34),
  [188] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 4, .production_id = 15),
  [190] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 4, .production_id = 15),
  [192] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 5, .production_id = 27),
  [194] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 5, .production_id = 27),
  [196] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 5, .production_id = 28),
  [198] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 5, .production_id = 28),
  [200] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 7, .production_id = 35),
  [202] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 7, .production_id = 35),
  [204] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_blk, 6, .production_id = 30),
  [206] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_blk, 6, .production_id = 30),
  [208] = {.entry = {.count = 1, .reusable = false}}, SHIFT(130),
  [210] = {.entry = {.count = 1, .reusable = true}}, SHIFT(204),
  [212] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_value, 1, .production_id = 10),
  [214] = {.entry = {.count = 1, .reusable = true}}, SHIFT(62),
  [216] = {.entry = {.count = 1, .reusable = true}}, SHIFT(101),
  [218] = {.entry = {.count = 1, .reusable = true}}, SHIFT(97),
  [220] = {.entry = {.count = 1, .reusable = false}}, SHIFT(186),
  [222] = {.entry = {.count = 1, .reusable = true}}, SHIFT(159),
  [224] = {.entry = {.count = 1, .reusable = true}}, SHIFT(304),
  [226] = {.entry = {.count = 1, .reusable = true}}, SHIFT(305),
  [228] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_string_name, 3),
  [230] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_string_name, 3),
  [232] = {.entry = {.count = 1, .reusable = false}}, SHIFT(127),
  [234] = {.entry = {.count = 1, .reusable = true}}, SHIFT(212),
  [236] = {.entry = {.count = 1, .reusable = true}}, SHIFT(64),
  [238] = {.entry = {.count = 1, .reusable = true}}, SHIFT(269),
  [240] = {.entry = {.count = 1, .reusable = true}}, SHIFT(96),
  [242] = {.entry = {.count = 1, .reusable = true}}, SHIFT(82),
  [244] = {.entry = {.count = 1, .reusable = false}}, SHIFT(162),
  [246] = {.entry = {.count = 1, .reusable = true}}, SHIFT(161),
  [248] = {.entry = {.count = 1, .reusable = true}}, SHIFT(308),
  [250] = {.entry = {.count = 1, .reusable = true}}, SHIFT(309),
  [252] = {.entry = {.count = 1, .reusable = true}}, SHIFT(288),
  [254] = {.entry = {.count = 1, .reusable = true}}, SHIFT(266),
  [256] = {.entry = {.count = 1, .reusable = true}}, SHIFT(263),
  [258] = {.entry = {.count = 1, .reusable = false}}, SHIFT(240),
  [260] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym__header, 1),
  [262] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__header, 1),
  [264] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_path, 1),
  [266] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_path, 1),
  [268] = {.entry = {.count = 1, .reusable = true}}, SHIFT(36),
  [270] = {.entry = {.count = 1, .reusable = false}}, SHIFT(132),
  [272] = {.entry = {.count = 1, .reusable = true}}, SHIFT(103),
  [274] = {.entry = {.count = 1, .reusable = true}}, SHIFT(81),
  [276] = {.entry = {.count = 1, .reusable = true}}, SHIFT(180),
  [278] = {.entry = {.count = 1, .reusable = false}}, SHIFT(164),
  [280] = {.entry = {.count = 1, .reusable = true}}, SHIFT(165),
  [282] = {.entry = {.count = 1, .reusable = true}}, SHIFT(298),
  [284] = {.entry = {.count = 1, .reusable = true}}, SHIFT(299),
  [286] = {.entry = {.count = 1, .reusable = true}}, SHIFT(194),
  [288] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym__any_name, 1),
  [290] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__any_name, 1),
  [292] = {.entry = {.count = 1, .reusable = true}}, SHIFT(102),
  [294] = {.entry = {.count = 1, .reusable = true}}, SHIFT(142),
  [296] = {.entry = {.count = 1, .reusable = false}}, SHIFT(119),
  [298] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_path, 3, .production_id = 13),
  [300] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_path, 3, .production_id = 13),
  [302] = {.entry = {.count = 1, .reusable = true}}, SHIFT(191),
  [304] = {.entry = {.count = 1, .reusable = true}}, SHIFT(286),
  [306] = {.entry = {.count = 1, .reusable = true}}, SHIFT(168),
  [308] = {.entry = {.count = 1, .reusable = true}}, SHIFT(147),
  [310] = {.entry = {.count = 1, .reusable = true}}, SHIFT(176),
  [312] = {.entry = {.count = 1, .reusable = true}}, SHIFT(290),
  [314] = {.entry = {.count = 1, .reusable = true}}, SHIFT(178),
  [316] = {.entry = {.count = 1, .reusable = true}}, SHIFT(145),
  [318] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_path, 2),
  [320] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_path, 2),
  [322] = {.entry = {.count = 1, .reusable = true}}, SHIFT(70),
  [324] = {.entry = {.count = 1, .reusable = false}}, SHIFT(227),
  [326] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_lang_lvl, 3, .production_id = 13),
  [328] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_lang_lvl, 3, .production_id = 13),
  [330] = {.entry = {.count = 1, .reusable = true}}, SHIFT(139),
  [332] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_lang_lvl, 2, .production_id = 7),
  [334] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_lang_lvl, 2, .production_id = 7),
  [336] = {.entry = {.count = 1, .reusable = true}}, SHIFT(137),
  [338] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2),
  [340] = {.entry = {.count = 1, .reusable = false}}, REDUCE(aux_sym_path_repeat1, 2),
  [342] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2), SHIFT_REPEAT(225),
  [345] = {.entry = {.count = 1, .reusable = true}}, SHIFT(80),
  [347] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2), SHIFT_REPEAT(222),
  [350] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2), SHIFT_REPEAT(223),
  [353] = {.entry = {.count = 1, .reusable = true}}, SHIFT(111),
  [355] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_ref, 1, .production_id = 2),
  [357] = {.entry = {.count = 1, .reusable = true}}, SHIFT(217),
  [359] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__expr, 1),
  [361] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym__expr, 1),
  [363] = {.entry = {.count = 1, .reusable = true}}, SHIFT(117),
  [365] = {.entry = {.count = 1, .reusable = true}}, SHIFT(108),
  [367] = {.entry = {.count = 1, .reusable = true}}, SHIFT(89),
  [369] = {.entry = {.count = 1, .reusable = true}}, SHIFT(115),
  [371] = {.entry = {.count = 1, .reusable = true}}, SHIFT(116),
  [373] = {.entry = {.count = 1, .reusable = true}}, SHIFT(90),
  [375] = {.entry = {.count = 1, .reusable = true}}, SHIFT(113),
  [377] = {.entry = {.count = 1, .reusable = true}}, SHIFT(94),
  [379] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_path_repeat1, 2), SHIFT_REPEAT(228),
  [382] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_binary_expr, 3, .production_id = 11),
  [384] = {.entry = {.count = 1, .reusable = true}}, SHIFT(104),
  [386] = {.entry = {.count = 1, .reusable = true}}, SHIFT(107),
  [388] = {.entry = {.count = 1, .reusable = false}}, SHIFT(107),
  [390] = {.entry = {.count = 1, .reusable = false}}, SHIFT(104),
  [392] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_bool, 1),
  [394] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_bool, 1),
  [396] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_binary_expr, 3, .production_id = 11),
  [398] = {.entry = {.count = 1, .reusable = true}}, SHIFT(75),
  [400] = {.entry = {.count = 1, .reusable = true}}, SHIFT(79),
  [402] = {.entry = {.count = 1, .reusable = true}}, SHIFT(92),
  [404] = {.entry = {.count = 1, .reusable = true}}, SHIFT(91),
  [406] = {.entry = {.count = 1, .reusable = false}}, SHIFT(91),
  [408] = {.entry = {.count = 1, .reusable = false}}, SHIFT(79),
  [410] = {.entry = {.count = 1, .reusable = true}}, SHIFT(172),
  [412] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_unary_expr, 2, .production_id = 4),
  [414] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_unary_expr, 2, .production_id = 4),
  [416] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_nested_expr, 3),
  [418] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_nested_expr, 3),
  [420] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_function, 6, .production_id = 29),
  [422] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_function, 6, .production_id = 29),
  [424] = {.entry = {.count = 1, .reusable = true}}, SHIFT(77),
  [426] = {.entry = {.count = 1, .reusable = true}}, SHIFT(182),
  [428] = {.entry = {.count = 1, .reusable = true}}, SHIFT(76),
  [430] = {.entry = {.count = 1, .reusable = true}}, SHIFT(88),
  [432] = {.entry = {.count = 1, .reusable = true}}, SHIFT(277),
  [434] = {.entry = {.count = 1, .reusable = true}}, SHIFT(87),
  [436] = {.entry = {.count = 1, .reusable = true}}, SHIFT(86),
  [438] = {.entry = {.count = 1, .reusable = false}}, SHIFT(86),
  [440] = {.entry = {.count = 1, .reusable = false}}, SHIFT(88),
  [442] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_function, 5, .production_id = 25),
  [444] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_function, 5, .production_id = 25),
  [446] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_function, 5, .production_id = 23),
  [448] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_function, 5, .production_id = 23),
  [450] = {.entry = {.count = 1, .reusable = true}}, SHIFT(74),
  [452] = {.entry = {.count = 1, .reusable = true}}, SHIFT(152),
  [454] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_function, 4, .production_id = 14),
  [456] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_function, 4, .production_id = 14),
  [458] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_string, 3),
  [460] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_string, 3),
  [462] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__header, 1, .production_id = 1),
  [464] = {.entry = {.count = 1, .reusable = true}}, SHIFT(106),
  [466] = {.entry = {.count = 1, .reusable = true}}, SHIFT(67),
  [468] = {.entry = {.count = 1, .reusable = true}}, SHIFT(195),
  [470] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_function_repeat1, 2, .production_id = 24),
  [472] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraint, 2, .production_id = 18),
  [474] = {.entry = {.count = 1, .reusable = true}}, SHIFT(99),
  [476] = {.entry = {.count = 1, .reusable = true}}, SHIFT(85),
  [478] = {.entry = {.count = 1, .reusable = true}}, SHIFT(83),
  [480] = {.entry = {.count = 1, .reusable = false}}, SHIFT(83),
  [482] = {.entry = {.count = 1, .reusable = false}}, SHIFT(99),
  [484] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym__value, 1, .production_id = 20),
  [486] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_attribute_constraints_repeat1, 2, .production_id = 18),
  [488] = {.entry = {.count = 1, .reusable = true}}, SHIFT(167),
  [490] = {.entry = {.count = 1, .reusable = true}}, SHIFT(196),
  [492] = {.entry = {.count = 1, .reusable = true}}, SHIFT(141),
  [494] = {.entry = {.count = 1, .reusable = true}}, SHIFT(181),
  [496] = {.entry = {.count = 1, .reusable = false}}, SHIFT(56),
  [498] = {.entry = {.count = 1, .reusable = true}}, SHIFT(27),
  [500] = {.entry = {.count = 1, .reusable = false}}, SHIFT(95),
  [502] = {.entry = {.count = 1, .reusable = false}}, SHIFT(294),
  [504] = {.entry = {.count = 1, .reusable = true}}, SHIFT(285),
  [506] = {.entry = {.count = 1, .reusable = true}}, SHIFT(262),
  [508] = {.entry = {.count = 1, .reusable = true}}, SHIFT(272),
  [510] = {.entry = {.count = 1, .reusable = true}}, SHIFT(33),
  [512] = {.entry = {.count = 1, .reusable = true}}, SHIFT(34),
  [514] = {.entry = {.count = 1, .reusable = true}}, SHIFT(35),
  [516] = {.entry = {.count = 1, .reusable = true}}, SHIFT(28),
  [518] = {.entry = {.count = 1, .reusable = true}}, SHIFT(25),
  [520] = {.entry = {.count = 1, .reusable = true}}, SHIFT(273),
  [522] = {.entry = {.count = 1, .reusable = true}}, SHIFT(289),
  [524] = {.entry = {.count = 1, .reusable = true}}, SHIFT(280),
  [526] = {.entry = {.count = 1, .reusable = false}}, SHIFT(118),
  [528] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_incomplete_namespace, 1),
  [530] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_incomplete_namespace, 1),
  [532] = {.entry = {.count = 1, .reusable = false}}, SHIFT(251),
  [534] = {.entry = {.count = 1, .reusable = false}}, REDUCE(sym_incomplete_ref, 2),
  [536] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_incomplete_ref, 2),
  [538] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_lang_lvl_repeat1, 2),
  [540] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_lang_lvl_repeat1, 2), SHIFT_REPEAT(151),
  [543] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_lang_lvl, 1),
  [545] = {.entry = {.count = 1, .reusable = true}}, SHIFT(112),
  [547] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_lang_lvl, 2),
  [549] = {.entry = {.count = 1, .reusable = true}}, SHIFT(110),
  [551] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_major_lvl, 1),
  [553] = {.entry = {.count = 1, .reusable = true}}, SHIFT(119),
  [555] = {.entry = {.count = 1, .reusable = true}}, SHIFT(279),
  [557] = {.entry = {.count = 1, .reusable = true}}, SHIFT(208),
  [559] = {.entry = {.count = 1, .reusable = true}}, SHIFT(32),
  [561] = {.entry = {.count = 1, .reusable = true}}, SHIFT(268),
  [563] = {.entry = {.count = 1, .reusable = true}}, SHIFT(207),
  [565] = {.entry = {.count = 1, .reusable = true}}, SHIFT(39),
  [567] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_minor_lvl, 1),
  [569] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_namespace, 2, .production_id = 3),
  [571] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_attribute_constraints_repeat1, 2), SHIFT_REPEAT(105),
  [574] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_attribute_constraints_repeat1, 2),
  [576] = {.entry = {.count = 1, .reusable = true}}, SHIFT(72),
  [578] = {.entry = {.count = 1, .reusable = true}}, SHIFT(281),
  [580] = {.entry = {.count = 1, .reusable = true}}, SHIFT(69),
  [582] = {.entry = {.count = 1, .reusable = true}}, SHIFT(146),
  [584] = {.entry = {.count = 1, .reusable = true}}, SHIFT(214),
  [586] = {.entry = {.count = 1, .reusable = true}}, SHIFT(284),
  [588] = {.entry = {.count = 1, .reusable = true}}, SHIFT(71),
  [590] = {.entry = {.count = 1, .reusable = true}}, SHIFT(192),
  [592] = {.entry = {.count = 1, .reusable = true}}, SHIFT(211),
  [594] = {.entry = {.count = 1, .reusable = true}}, SHIFT(26),
  [596] = {.entry = {.count = 1, .reusable = true}}, SHIFT(213),
  [598] = {.entry = {.count = 1, .reusable = true}}, SHIFT(276),
  [600] = {.entry = {.count = 1, .reusable = true}}, SHIFT(59),
  [602] = {.entry = {.count = 1, .reusable = true}}, SHIFT(274),
  [604] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_typed_feature, 2, .production_id = 8),
  [606] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_function_repeat1, 2, .production_id = 26), SHIFT_REPEAT(93),
  [609] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_function_repeat1, 2, .production_id = 26),
  [611] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_cardinality, 3, .production_id = 9),
  [613] = {.entry = {.count = 1, .reusable = true}}, SHIFT(73),
  [615] = {.entry = {.count = 1, .reusable = true}}, SHIFT(175),
  [617] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_group_mode, 1),
  [619] = {.entry = {.count = 1, .reusable = true}}, SHIFT(209),
  [621] = {.entry = {.count = 1, .reusable = true}}, SHIFT(30),
  [623] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_vector_repeat1, 2), SHIFT_REPEAT(63),
  [626] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_vector_repeat1, 2),
  [628] = {.entry = {.count = 1, .reusable = true}}, SHIFT(210),
  [630] = {.entry = {.count = 1, .reusable = true}}, SHIFT(29),
  [632] = {.entry = {.count = 1, .reusable = true}}, SHIFT(61),
  [634] = {.entry = {.count = 1, .reusable = true}}, SHIFT(261),
  [636] = {.entry = {.count = 1, .reusable = true}}, SHIFT(60),
  [638] = {.entry = {.count = 1, .reusable = true}}, SHIFT(267),
  [640] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_constraints, 1),
  [642] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_ref, 3, .production_id = 12),
  [644] = {.entry = {.count = 1, .reusable = true}}, SHIFT(38),
  [646] = {.entry = {.count = 1, .reusable = true}}, SHIFT(205),
  [648] = {.entry = {.count = 1, .reusable = true}}, SHIFT(283),
  [650] = {.entry = {.count = 1, .reusable = true}}, SHIFT(203),
  [652] = {.entry = {.count = 1, .reusable = true}}, SHIFT(23),
  [654] = {.entry = {.count = 2, .reusable = true}}, REDUCE(aux_sym_attributes_repeat1, 2), SHIFT_REPEAT(215),
  [657] = {.entry = {.count = 1, .reusable = true}}, REDUCE(aux_sym_attributes_repeat1, 2),
  [659] = {.entry = {.count = 1, .reusable = true}}, SHIFT(66),
  [661] = {.entry = {.count = 1, .reusable = true}}, SHIFT(177),
  [663] = {.entry = {.count = 1, .reusable = true}}, SHIFT(21),
  [665] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_cardinality, 5, .production_id = 22),
  [667] = {.entry = {.count = 1, .reusable = true}}, SHIFT(206),
  [669] = {.entry = {.count = 1, .reusable = true}}, SHIFT(275),
  [671] = {.entry = {.count = 1, .reusable = true}}, SHIFT(58),
  [673] = {.entry = {.count = 1, .reusable = true}}, SHIFT(287),
  [675] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_vector, 4),
  [677] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_vector, 5, .production_id = 33),
  [679] = {.entry = {.count = 1, .reusable = true}}, SHIFT(296),
  [681] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_vector, 4, .production_id = 13),
  [683] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_vector, 3),
  [685] = {.entry = {.count = 1, .reusable = true}}, SHIFT(301),
  [687] = {.entry = {.count = 1, .reusable = true}}, SHIFT(278),
  [689] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_value, 2, .production_id = 19),
  [691] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraints, 4, .production_id = 32),
  [693] = {.entry = {.count = 1, .reusable = true}}, SHIFT(264),
  [695] = {.entry = {.count = 1, .reusable = true}}, SHIFT(242),
  [697] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraints, 5, .production_id = 32),
  [699] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraints, 6, .production_id = 37),
  [701] = {.entry = {.count = 1, .reusable = true}}, REDUCE(sym_attribute_constraints, 5, .production_id = 36),
  [703] = {.entry = {.count = 1, .reusable = true}}, SHIFT(173),
  [705] = {.entry = {.count = 1, .reusable = true}}, SHIFT(78),
  [707] = {.entry = {.count = 1, .reusable = true}}, SHIFT(157),
  [709] = {.entry = {.count = 1, .reusable = true}}, SHIFT(84),
  [711] = {.entry = {.count = 1, .reusable = true}},  ACCEPT_INPUT(),
  [713] = {.entry = {.count = 1, .reusable = true}}, SHIFT(258),
  [715] = {.entry = {.count = 1, .reusable = false}}, SHIFT_EXTRA(),
  [717] = {.entry = {.count = 1, .reusable = false}}, SHIFT(292),
  [719] = {.entry = {.count = 1, .reusable = true}}, SHIFT(302),
  [721] = {.entry = {.count = 1, .reusable = false}}, SHIFT(303),
  [723] = {.entry = {.count = 1, .reusable = true}}, SHIFT(310),
  [725] = {.entry = {.count = 1, .reusable = true}}, SHIFT(158),
  [727] = {.entry = {.count = 1, .reusable = true}}, SHIFT(154),
  [729] = {.entry = {.count = 1, .reusable = true}}, SHIFT(307),
  [731] = {.entry = {.count = 1, .reusable = false}}, SHIFT(306),
  [733] = {.entry = {.count = 1, .reusable = true}}, SHIFT(57),
  [735] = {.entry = {.count = 1, .reusable = true}}, SHIFT(197),
  [737] = {.entry = {.count = 1, .reusable = true}}, SHIFT(291),
  [739] = {.entry = {.count = 1, .reusable = false}}, SHIFT(293),
  [741] = {.entry = {.count = 1, .reusable = true}}, SHIFT(153),
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
