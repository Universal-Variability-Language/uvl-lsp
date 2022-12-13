use ropey::Rope;
use tree_sitter::{Language, Query};
static CHECK_SYNTAX: &str = r#"
(path
    tail:(_) 
)@missing_name
(ERROR 
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
    ".."]
 )@missing_op


(blk
  header:(_) @parent
  (blk
        header:(_)@sub)
)

(source_file
  (blk
        header:(_)@root)
)
[(incomplete_namespace) (incomplete_ref)]@incomplete
"#;
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
[
    "avg"
    "sum"
]@function

(attribute_value name:(_)@enumMember)
(ref alias:(_)@parameter)


(blk
    header: [(name)] @parameter)
(path)@some_path
"#;

static EXTRACT_DEPENDENCIES_SRC: &str = r#"
(blk 
    (blk)@inner
)@outer

(blk
    (attributes
      (attribute_value)@child
    )
)@parent

(attribute_value
    (attributes
      (attribute_value)@child
    )
)@parent
"#;

static EXTRACT_SYMBOLES_SRC: &str = r#"
(blk
  header:[(features) (name) (group_mode)]
  [(blk
    header: (name)
  )@feature
  (blk
    header: (ref path:(_) @feature_ref) 
  )]
)
(source_file
    (blk
        header:(imports)
        [(blk
            header: (ref)@import_ref
         )
         (blk
            header:(name)@import_name
          )

        ]
    )

)
(source_file
    (blk
        header:(namespace name:(_)  @namespace))
)

(source_file
    (blk
        header:(include)
        (blk
            header:(lang_lvl)@lang_lvl
        )
    )
)
(blk 
    header:[(group_mode)@group (cardinality)@cardinality ]   )
(attribute_value)@attrib
(constraint)@constraint
"#;

pub struct Queries {
    pub extract_symboles: Query,
    pub extract_dependencies: Query,
    pub highlight: Query,
    pub check_sanity: Query,
    pub check_syntax: Query,
}
impl Queries {
    pub fn new(lang: &Language) -> Queries {
        Queries {
            extract_symboles: Query::new(lang.clone(), EXTRACT_SYMBOLES_SRC).unwrap(),
            extract_dependencies: Query::new(lang.clone(), EXTRACT_DEPENDENCIES_SRC).unwrap(),
            highlight: Query::new(lang.clone(), EXTRACT_SYNTAX_HIGHLIGHTING_SRC).unwrap(),
            check_sanity: Query::new(lang.clone(), CHECK_SANITY).unwrap(),
            check_syntax: Query::new(lang.clone(), CHECK_SYNTAX).unwrap(),
        }
    }
}

pub fn node_source<'a>(source: &'a Rope) -> impl tree_sitter::TextProvider<'a> {
    |node: tree_sitter::Node| {
        source
            .byte_slice(node.byte_range())
            .chunks()
            .map(|i: &str| i.as_bytes())
    }
}
