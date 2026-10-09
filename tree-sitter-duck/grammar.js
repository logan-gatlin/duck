/**
 * @file Tree-sitter grammar for the Duck language.
 *
 * Mirrors `crates/duck-compiler/src/lex.rs` and `parse.rs`. Layout tokens
 * (newline, indent, dedent) come from `src/scanner.c`.
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

// Binary operator precedence, as in `binary_op` in parse.rs; higher binds
// tighter. `not`, casts, prefix and postfix operators slot in around them,
// pipes sit below them all, and assignment below pipes.
const PREC = {
  assign: -1,
  pipe: 0,
  or: 1,
  and: 2,
  not: 3,
  compare: 4,
  bit_or: 5,
  bit_xor: 6,
  bit_and: 7,
  shift: 8,
  add: 9,
  multiply: 10,
  cast: 11,
  unary: 12,
  postfix: 13,
  type: 14,
};

/** `rule, rule, ...` with an optional trailing comma. */
function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)), optional(','));
}

/** Like `commaSep1`, but possibly empty. */
function commaSep(rule) {
  return optional(commaSep1(rule));
}

/** `rule, rule, ...` with at least two elements and an optional trailing comma. */
function commaSep2(rule) {
  return seq(rule, repeat1(seq(',', rule)), optional(','));
}

/**
 * The body of a struct, a union or an enum: its `use` lines, then lines of
 * its own, each of which is `own`. At least one line of either.
 */
function usesThen($, own) {
  return choice(seq(repeat1($.type_use), repeat(own)), repeat1(own));
}

module.exports = grammar({
  name: 'duck',

  externals: $ => [
    $._newline,
    $._indent,
    $._dedent,
    // Never produced by the scanner: listed so it can tell when the parser is
    // inside brackets, where line breaks mean nothing.
    ')',
    ']',
    '}',
    // Never used in the grammar: only valid during error recovery.
    $._error_sentinel,
  ],

  extras: $ => [/[ \t\r\n]/, $.comment],

  word: $ => $.identifier,

  supertypes: $ => [$._item, $._statement, $._expression, $._type, $._pattern],

  rules: {
    source_file: $ => repeat($._item),

    // Items

    _item: $ => choice(
      $.function_declaration,
      $.extern_block,
      $.struct_declaration,
      $.enum_declaration,
      $.union_declaration,
      $.binding,
      $.use,
    ),

    function_declaration: $ => seq(
      optional('pub'),
      $._function_signature,
      field('body', $.block),
    ),

    _function_signature: $ => seq(
      'fn',
      field('type_parameters', optional($.type_parameters)),
      field('name', $.identifier),
      field('parameters', $.parameters),
      optional(seq('->', field('return_type', $._type))),
    ),

    type_parameters: $ => seq('(', commaSep1($._type_parameter), ')'),

    _type_parameter: $ => choice($.identifier, $.bounded_type_parameter),

    bounded_type_parameter: $ => seq(
      field('name', $.identifier),
      ':',
      field('bound', choice($._type, $.bound_list)),
    ),

    // `(A, B)`: the types that a type argument uses, first and in order.
    bound_list: $ => seq('(', commaSep($._type), ')'),

    parameters: $ => seq('(', commaSep($.parameter), ')'),

    parameter: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $._type),
      optional(seq('=', field('default', $._expression))),
    ),

    extern_block: $ => seq(
      'extern',
      field('module', optional($.string)),
      ':',
      $._newline,
      $._indent,
      repeat1(choice($.extern_function, $.pass_statement)),
      $._dedent,
    ),

    extern_function: $ => seq(
      optional('pub'),
      $._function_signature,
      optional(seq('=', field('import_name', $.string))),
      $._newline,
    ),

    struct_declaration: $ => seq(
      optional('pub'),
      'struct',
      field('type_parameters', optional($.type_parameters)),
      field('name', $.identifier),
      ':',
      $._newline,
      $._indent,
      usesThen($, choice($.field_declaration, $.pass_statement)),
      $._dedent,
    ),

    field_declaration: $ => seq(
      optional('pub'),
      field('name', $.identifier),
      ':',
      field('type', $._type),
      optional(seq('=', field('default', $._expression))),
      $._newline,
    ),

    enum_declaration: $ => seq(
      optional('pub'),
      'enum',
      '(',
      field('type', $._type),
      ')',
      field('name', $.identifier),
      ':',
      $._newline,
      $._indent,
      usesThen($, $.enum_member),
      $._dedent,
    ),

    enum_member: $ => seq(
      field('name', $.identifier),
      optional(seq('=', field('value', $._expression))),
      $._newline,
    ),

    union_declaration: $ => seq(
      optional('pub'),
      'union',
      field('type_parameters', optional($.type_parameters)),
      field('name', $.identifier),
      ':',
      $._newline,
      $._indent,
      usesThen($, $.union_variant),
      $._dedent,
    ),

    union_variant: $ => seq(
      field('name', $.identifier),
      optional(seq(':', field('type', $._type))),
      $._newline,
    ),

    // `use Type` in a struct, a union or an enum: the fields, variants or
    // members of another, before its own.
    type_use: $ => seq(
      'use',
      field('type', $._type),
      $._newline,
    ),

    // `use a.b` names a module or an item of one; `use a.{b, c}` several.
    use: $ => seq(
      optional('pub'),
      'use',
      $._use_tree,
      $._newline,
    ),

    _use_tree: $ => choice($._use_path, $.use_alias, $.use_group),

    _use_path: $ => choice($.identifier, $.use_path),

    use_path: $ => seq(
      field('path', $._use_path),
      '.',
      field('name', $.identifier),
    ),

    use_alias: $ => seq(
      field('path', $._use_path),
      'as',
      field('alias', $.identifier),
    ),

    use_group: $ => seq(
      field('path', $._use_path),
      '.',
      '{',
      commaSep($._use_tree),
      '}',
    ),

    // `let` and `var`, both as items and as statements; only items take `pub`.
    binding: $ => seq(
      optional('pub'),
      field('mutability', choice('let', 'var')),
      field('pattern', $._pattern),
      optional(seq(':', field('type', $._type))),
      '=',
      field('value', $._expression),
      $._newline,
    ),

    // Patterns

    // A binding takes the first four. The rest can fail to match, so only
    // the arms of a `match` take them.
    _pattern: $ => choice(
      $.identifier,
      $.discard,
      $.tuple_pattern,
      $.parenthesized_pattern,
      $.variant_pattern,
      $.array_pattern,
      $.negative_pattern,
      $.integer,
      $.float,
      $.string,
      $.boolean,
    ),

    discard: _ => '_',

    tuple_pattern: $ => seq('(', optional(commaSep2($._pattern)), ')'),

    parenthesized_pattern: $ => seq('(', $._pattern, ')'),

    // `.name` or `.name(pattern)`: a variant of a union and what it holds,
    // or a member of an enum.
    variant_pattern: $ => seq(
      '.',
      field('name', $.identifier),
      optional(seq('(', field('value', $._pattern), ')')),
    ),

    // `[a, b]`, which takes apart an array of as many elements.
    array_pattern: $ => seq('[', commaSep($._pattern), ']'),

    negative_pattern: $ => seq('-', choice($.integer, $.float)),

    // Types

    _type: $ => choice(
      $.named_type,
      $.qualified_type,
      $.pointer_type,
      $.function_type,
    ),

    // The precedence keeps the `(` after `x as Name` as the type's arguments
    // rather than a call of the cast.
    named_type: $ => prec.right(PREC.type, seq(
      field('name', $.identifier),
      field('arguments', optional($.type_arguments)),
    )),

    // `module.Name`, a type in another module.
    qualified_type: $ => prec.right(PREC.type, seq(
      field('module', $.identifier),
      '.',
      field('type', choice($.named_type, $.qualified_type)),
    )),

    type_arguments: $ => prec(PREC.type, seq('(', commaSep($._type), ')')),

    // `&T`, or `&var T`, which can be written through.
    pointer_type: $ => seq(
      '&',
      optional(field('mutability', 'var')),
      field('pointee', $._type),
    ),

    // `fn(A, B) -> R`, a pointer to a function. The result takes everything
    // it can, so `fn(A) -> fn(B) -> C` returns a function.
    function_type: $ => prec.right(PREC.type, seq(
      'fn',
      field('parameters', $.parameter_types),
      optional(seq('->', field('return_type', $._type))),
    )),

    parameter_types: $ => seq('(', commaSep($._type), ')'),

    // Statements

    block: $ => seq(
      ':',
      $._newline,
      $._indent,
      repeat1($._statement),
      $._dedent,
    ),

    _statement: $ => choice(
      $.binding,
      $.expression_statement,
      $.return_statement,
      $.if_statement,
      $.while_statement,
      $.for_statement,
      $.match_statement,
      $.break_statement,
      $.continue_statement,
      $.pass_statement,
    ),

    expression_statement: $ => seq($._expression, $._newline),

    return_statement: $ => seq(
      'return',
      field('value', optional($._expression)),
      $._newline,
    ),

    if_statement: $ => seq(
      'if',
      field('condition', $._expression),
      field('consequence', $.block),
      field('alternative', optional($.else_clause)),
    ),

    else_clause: $ => seq('else', choice($.if_statement, $.block)),

    while_statement: $ => seq(
      'while',
      field('condition', $._expression),
      field('body', $.block),
    ),

    for_statement: $ => seq(
      'for',
      field('variable', $.identifier),
      'in',
      field('iterable', $._expression),
      field('body', $.block),
    ),

    // `else` is an arm that matches every value, and comes last.
    match_statement: $ => seq(
      'match',
      field('value', $._expression),
      ':',
      $._newline,
      $._indent,
      choice(
        seq(repeat1($.match_arm), optional($.else_arm)),
        $.else_arm,
      ),
      $._dedent,
    ),

    match_arm: $ => seq(
      field('pattern', $._pattern),
      field('body', $.block),
    ),

    else_arm: $ => seq('else', field('body', $.block)),

    break_statement: $ => seq('break', $._newline),

    continue_statement: $ => seq('continue', $._newline),

    pass_statement: $ => seq('pass', $._newline),

    // Expressions

    _expression: $ => choice(
      $.identifier,
      $.integer,
      $.float,
      $.string,
      $.boolean,
      $.module_property,
      $.function_type,
      $.unit,
      $.tuple,
      $.list,
      $.repeated_list,
      $.parenthesized_expression,
      $.placeholder,
      $.dot_expression,
      $.assignment_expression,
      $.pipe_expression,
      $.unary_expression,
      $.binary_expression,
      $.cast_expression,
      $.address_of_expression,
      $.call_expression,
      $.index_expression,
      $.field_expression,
      $.dereference_expression,
    ),

    // `module.name`, a property of the module being compiled.
    module_property: $ => seq('module', '.', field('name', $.identifier)),

    unit: _ => seq('(', ')'),

    tuple: $ => seq('(', commaSep2($._expression), ')'),

    list: $ => seq('[', commaSep($._expression), ']'),

    // `[value; length]`, an array of `length` copies of `value`.
    repeated_list: $ => seq(
      '[',
      field('value', $._expression),
      ';',
      field('length', $._expression),
      ']',
    ),

    parenthesized_expression: $ => seq('(', $._expression, ')'),

    // `_`, the value piped into the nearest pipe whose body it's in.
    placeholder: _ => '_',

    // `.name`, a variant of the union or member of the enum expected of it.
    dot_expression: $ => seq('.', field('name', $.identifier)),

    // `target = value`, whose value is the one assigned. Groups to the right.
    assignment_expression: $ => prec.right(PREC.assign, seq(
      field('target', $._expression),
      field('operator', choice('=', '+=', '-=', '*=', '/=', '%=')),
      field('value', $._expression),
    )),

    // `value |> body`. The scanner lets a deeper line that starts with `|>`
    // continue the line above.
    pipe_expression: $ => prec.left(PREC.pipe, seq(
      field('value', $._expression),
      '|>',
      field('body', $._expression),
    )),

    unary_expression: $ => choice(
      prec(PREC.not, seq(
        field('operator', 'not'),
        field('operand', $._expression),
      )),
      prec(PREC.unary, seq(
        field('operator', choice('-', '~')),
        field('operand', $._expression),
      )),
    ),

    // `&place`, or `&var place`, which can be written through. In a global
    // initializer the operand may be any constant, which is placed in memory.
    address_of_expression: $ => prec(PREC.unary, seq(
      '&',
      optional(field('mutability', 'var')),
      field('operand', $._expression),
    )),

    binary_expression: $ => {
      /** @type {[RuleOrLiteral, number][]} */
      const table = [
        ['or', PREC.or],
        ['and', PREC.and],
        [choice('==', '!=', '<', '<=', '>', '>='), PREC.compare],
        ['|', PREC.bit_or],
        ['^', PREC.bit_xor],
        ['&', PREC.bit_and],
        [choice('<<', '>>'), PREC.shift],
        [choice('+', '-'), PREC.add],
        [choice('*', '/', '%'), PREC.multiply],
      ];
      return choice(...table.map(([operator, precedence]) =>
        prec.left(precedence, seq(
          field('left', $._expression),
          field('operator', operator),
          field('right', $._expression),
        )),
      ));
    },

    // `as` makes a value one of another type that it is, and `as!` an
    // address one of any type, unchecked.
    cast_expression: $ => prec.left(PREC.cast, seq(
      field('value', $._expression),
      choice('as', 'as!'),
      field('type', $._type),
    )),

    call_expression: $ => prec(PREC.postfix, seq(
      field('function', $._expression),
      field('arguments', $.arguments),
    )),

    arguments: $ => seq(
      '(',
      commaSep(choice($._expression, $.labeled_argument)),
      ')',
    ),

    // `_` is a name here, not a placeholder.
    labeled_argument: $ => seq(
      field('label', choice($.identifier, alias('_', $.identifier))),
      ':',
      field('value', $._expression),
    ),

    index_expression: $ => prec(PREC.postfix, seq(
      field('value', $._expression),
      '[',
      field('index', $._expression),
      ']',
    )),

    field_expression: $ => prec(PREC.postfix, seq(
      field('value', $._expression),
      '.',
      field('field', choice($.identifier, $.tuple_index)),
    )),

    dereference_expression: $ => prec(PREC.postfix, seq(
      field('value', $._expression),
      '.*',
    )),

    // Tokens

    identifier: _ => /[_\p{Alphabetic}][_\p{Alphabetic}\p{N}]*/,

    // Only valid after a `.`, where a float is not, so `t.0.1` is two indices.
    tuple_index: _ => /0|[1-9][0-9]*/,

    integer: _ => token(choice(
      /[0-9][0-9_]*/,
      /0[xX][0-9a-fA-F_]+/,
      /0[oO][0-7_]+/,
      /0[bB][01_]+/,
    )),

    float: _ => token(choice(
      /[0-9][0-9_]*\.[0-9][0-9_]*([eE][+-]?[0-9][0-9_]*)?/,
      /[0-9][0-9_]*[eE][+-]?[0-9][0-9_]*/,
    )),

    boolean: _ => choice('true', 'false'),

    string: $ => seq(
      '"',
      repeat(choice($.string_content, $.escape_sequence)),
      token.immediate('"'),
    ),

    string_content: _ => token.immediate(prec(1, /[^"\\\r\n]+/)),

    escape_sequence: _ => token.immediate(seq(
      '\\',
      choice(/[nrt0\\"']/, /u\{[0-9a-fA-F]{1,6}\}/),
    )),

    comment: _ => token(seq('#', /[^\r\n]*/)),
  },
});
