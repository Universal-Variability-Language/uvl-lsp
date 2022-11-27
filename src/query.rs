use ropey::Rope;
use tree_sitter::{Language, Query};
static CHECK_SYNTAX: &str = r#"
(path
    tail:(_) 
)@missing_name
(ERROR 
  (op)
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


(attribute_constraint
    (expr)@constraint_expr
)

(attribute_constraints
    (expr)@constraint_expr
)
(attrib_expr)@value_expr
(blk
    header:(constraints)
    (blk
        header:[(expr) (name) (ref)]@constraint_expr
     )
)
(blk
    header:(_)@attrib_owner
    (attributes)
)
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
 ]@keyword
(comment) @comment
(lang_lvl) @macro

(string) @string

(int) @number

(bool) @keyword

(number) @number

[
    (group_mode)
    (constraints)
    (include)
    (features)
    (imports)
] @keyword

[
    (op)
] @operator
[
    (func)
]@function

(attribute_value name:(_)@enumMember)

(attribute_value name:(_)@enum value:(attributes))


[(blk
    header: [(name)] @class)
(blk
    header: (ref path:(_) @namespace))]
(source_file
    (blk
        header:(imports)
        [(blk
            header: (ref path:(_)@namespace alias:(_)?@interface))
         (blk
            header:(name)@namespace
          )

        ]
    )
)
(source_file
    (blk
        header:(namespace name:(_) @namespace)
        )
)
(constraint
  (path)@namespace
)
(equation
  (path)@enumMember
)
(numeric
  (path)@enumMember
)
"#;

static EXTRACT_DEPENDENCIES_SRC: &str = r#"
(blk 
    header:(group_mode)
    ( blk
        header:[(name)]     
    )@inner
)@group
(expr)@constraint

(blk
    header:[(name)]
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
    header: [(name) ] @feature
  )(blk
    header: (ref path:(_) @ref) 
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
        header:(namespace name:(_)  @namespace)
        )
)
(constraint
  (path)@expr_ref
)
(equation
  (path)@expr_ref
)
(numeric
  (path)@expr_ref
)
(nested_expr
  (path)@expr_ref
)
(expr
  (path)@expr_ref
)
(blk 
    header:(group_mode)@group)
(attribute_value)@attrib
"#;

pub struct Queries {
    pub extract_symboles: Query,
    pub extract_dependencies: Query,
    pub highlight: Query,
    pub check_sanity: Query,
    pub check_syntax:Query,
}
impl Queries {
    pub fn new(lang: &Language) -> Queries {
        Queries {
            extract_symboles: Query::new(lang.clone(), EXTRACT_SYMBOLES_SRC).unwrap(),
            extract_dependencies: Query::new(lang.clone(), EXTRACT_DEPENDENCIES_SRC).unwrap(),
            highlight: Query::new(lang.clone(), EXTRACT_SYNTAX_HIGHLIGHTING_SRC).unwrap(),
            check_sanity: Query::new(lang.clone(), CHECK_SANITY).unwrap(),
            check_syntax: Query::new(lang.clone(),CHECK_SYNTAX).unwrap(),
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
