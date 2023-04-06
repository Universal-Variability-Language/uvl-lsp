//use ropey::Rope;
use tree_sitter::{Language, Query};
static CHECK_SANITY: &str = r#"
(blk
  header:(_)@header
)
(name)@name
(string)@string
"#;

static EXTRACT_SYNTAX_HIGHLIGHTING_SRC: &str = r#"
[
 "namespace"
 "as"
 "constraint"
 "true"
 "false"
 "cardinality"
 ]@keyword
(comment) @comment

(lang_lvl) @macro

(string) @string

(int) @number

(number) @number

[
    (group_mode)
    (constraints)
    (include)
    (features)
    (imports)
] @keyword

[
    "|"
    "&"
    "=>"
    "<=>"
    ">"
    "<"
    "=="
    "+"
    "*"
    "-"
    "/"
    "!"
    ".."
] @operator

(function op:(_) @function)

(attribute_value name:(_)@enumMember)

(ref alias:(_)@parameter)

(blk
    header: [(name)] @parameter)

(typed_feature type:(_) @class name:(_) @parameter)
(path)@parameter
"#;

pub struct Queries {
    pub highlight: Query,
    pub check_sanity: Query,
}
impl Queries {
    pub fn new(lang: &Language) -> Queries {
        Queries {
            highlight: Query::new(*lang, EXTRACT_SYNTAX_HIGHLIGHTING_SRC).unwrap(),
            check_sanity: Query::new(*lang, CHECK_SANITY).unwrap(),
        }
    }
}
/*
pub fn node_source(source: &Rope) -> impl tree_sitter::TextProvider<'_> {
    |node: tree_sitter::Node| {
        source
            .byte_slice(node.byte_range())
            .chunks()
            .map(|i: &str| i.as_bytes())
    }
}*/
