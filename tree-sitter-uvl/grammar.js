
const PREC = {

    not: 6,
    consequence: 2,
    logic: 3,
    eq: 4,
    mul: 5,
    add: 5,



}
module.exports = grammar({
    name: 'uvl',
    extras: $ => [
        /[\s\f\uFEFF\u2060\u200B]|\\\r?\n/,
        $.comment
    ],
    externals: $ => [
        $._indent,
        $._dedent,
        $._newline,
        $.comment,
        ')',
        ']',
        '}'

    ],
    conflicts: $ => [
        [$._expr, $.ref],
        [$._header, $.path],
        //[$.typed_feature,$._single_name,$.lang_lvl,$.path],

    ],
    word: $ => $.name,
    rules: {
        source_file: $ => repeat($.blk),
        blk: $ => seq(
            field("header", $._header),
            optional(seq("cardinality", field("cardinality", $.cardinality))),
            choice(field("attribs", $.attributes), $._newline),
            optional(
                field("child",
                    seq($._indent,
                        repeat($.blk),
                        $._dedent))),


        ),
        attributes: $ => seq(
            "{",
            optional(sep1($._attribute, ",", $)),
            "}"
        ),

        _header: $ => choice(
            prec(2, $._any_name),
            $.typed_feature,
            $.group_mode,
            $.imports,
            $.features,
            $.constraints,
            $.include,
            $.ref,
            alias($._expr, $.constraint),
            $.lang_lvl,
            $.namespace,
            $.cardinality,
            $.incomplete_namespace,
            $.incomplete_ref,

        ),
        typed_feature: $ => seq(field("type", $.type), field("name", $._any_name)),
        ref: $ => prec(2, seq(
            field("path", $.path),
            optional(seq("as", field("alias", $._any_name)))
        )),
        namespace: $ => seq(
            "namespace", field("name", $.path)
        ),
        incomplete_namespace: $ => seq(
            "namespace"
        ),
        incomplete_ref: $ => seq(
            $.path,
            "as"
        ),
        cardinality: $ => seq(
            "[",
            optional(seq(field("begin", $.int), "..")),
            field("end", choice($.int, "*")),
            "]",
        ),
        attribute_constraint: $ => seq(
            "constraint",
            alias($._expr, $.constraint),

        ),
        attribute_constraints: $ => seq(
            "constraints", "[", sep1(alias($._expr, $.constraint), ",", $), "]"
        ),
        attribute_value: $ => seq(
            field("name", $._any_name), optional(field("value", $._value))
        ),
        _attribute: $ => choice(
            $.attribute_value,
            $.attribute_constraint,
            $.attribute_constraints,
        ),
        _value: $ => choice(
            $.vector,
            alias($._expr, $.attrib_expr),
            $.attributes
        ),
        _expr: $ => choice(
            $.path,
            $.bool,
            $.number,
            $.nested_expr,
            $.unary_expr,
            $.binary_expr,
            $.function,
            $.string,
        ),
        unary_expr: $ => choice(
            prec(PREC.not, seq(
                field("op", '!'),
                field("lhs", $._expr),
            )),
        ),
        binary_expr: $ => choice(
            op2("|", PREC.logic, $),
            op2("&", PREC.logic, $),
            op2("=>", PREC.consequence, $),
            op2("<=>", PREC.consequence, $),
            op2(">", PREC.eq, $),
            op2("<", PREC.eq, $),
            op2("==", PREC.eq, $),
            op2("+", PREC.add, $),
            op2("-", PREC.add, $),
            op2("*", PREC.mul, $),
            op2("/", PREC.mul, $),
        ),
        nested_expr: $ =>
            seq('(', $._expr, ')'),

        function: $ =>
            seq(field("op", $.name), "(",
                sep1(field("arg", $._expr), ","), ")"),

        vector: $ => seq(
            '[',
            sep1($._value, ",", $),
            ']'
        ),
        bool: _ => choice(
            "true",
            "false",
        ),
        number: _ => {
            const decimal = /[0-9][0-9_]*/;
            const hexadecimal = /[0-9a-fA-F][0-9a-fA-F_]*/;
            return token(
                seq(
                    choice(
                        seq(/0[xX]/, hexadecimal, optional("."), optional(hexadecimal)),
                        seq(decimal, optional("."), optional(decimal))
                    ),
                    optional(/[eEpP][+-]?\d+/)
                )
            );
        },
        // http://stackoverflow.com/questions/13014947/regex-to-match-a-c-style-multiline-comment/36328890#36328890
        comment: $ => token(choice(
            seq('//', /(\\(.|\r?\n)|[^\\\n])*/),
            seq(
                '/*',
                /[^*]*\*+([^/*][^*]*\*+)*/,
                '/'
            )
        )),
        path: $ => prec.right(sep1($._any_name, ".", $)),
        lang_lvl: $ => prec.right(-1, sep1(choice($.major_lvl, $.minor_lvl, prec(-1, $._any_name)), ".", $)),


        group_mode: $ => choice(
            "or",
            "alternative",
            "mandatory",
            "optional",
        ),
        major_lvl: _ => choice(
            'Boolean',
            'Arithmetic',
            'Type',
        ),
        minor_lvl: _ => choice(
            'group-cardinality',
            'feature-cardinality',
            'aggregate-function',
            'type-constraints',
            'string-constraints',
            'numeric-constraints',
            '*'
        ),
        type: $ => choice(
            "Boolean",
            "Real",
            "Integer",
            "String",
            $._any_name,
        ),
        string: $ => seq(
            "'", $.string_content, "'"
        ),
        string_name: $ => seq(
            '"', /[^\\"\n]*/, '"'
        ),
        string_content: $ => token.immediate(prec(1, /[^\n\\']*/)),
        imports: _ => "imports",
        features: _ => "features",
        constraints: _ => "constraints",
        include: _ => "include",
        _any_name: $ => choice($.name, alias($.string_name, $.name)),
        name: _ => /[_\p{XID_Start}][_\p{XID_Continue}]*/,
        int: _ => /[1-9_][0-9_]*|0/,
    }
})
function op2(op, p, $) {
    return prec.left(p, seq(field("lhs", $._expr), field("op", op), field("rhs", $._expr)))
}
function sep1(rule, separator, $) {
    return seq(rule, repeat(seq(separator, rule)),
        optional(field("tail", separator)))
}
