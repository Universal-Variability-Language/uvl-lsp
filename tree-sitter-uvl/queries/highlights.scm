

[
 "namespace"
 "as"
 "constraint"
 "cardinality"
 ]@keyword

(lang_lvl) @definition.macro

(comment) @comment

(string) @string

(int) @number

(bool) @boolean

(number) @float
[ "(" ")" "[" "]" "{" "}"] @punctuation.bracket
[
    (group_mode)
    (constraints)
    (include)
    (features)
    (imports)
] @keyword
[".." (op)] @operator


(aggregate op:(_) @function)

(attribute_value name:(_)@definition.enum)

(ref alias:(_)@parameter)

(blk
    header: [(name)] @parameter)

(path)@parameter






