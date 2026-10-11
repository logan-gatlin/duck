; Identifiers

(identifier) @variable

(parameter name: (identifier) @variable.parameter)

(field_declaration name: (identifier) @property)
(field_expression field: (identifier) @property)
(field_expression field: (tuple_index) @number)
(labeled_argument label: (identifier) @property)
(module_property name: (identifier) @property)

(enum_member name: (identifier) @constant)
(union_variant name: (identifier) @constant)
(dot_expression name: (identifier) @constant)
(variant_pattern name: (identifier) @constant)

; Functions

(function_declaration name: (identifier) @function)
(extern_function name: (identifier) @function)

(call_expression function: (identifier) @function.call)
(call_expression
  function: (field_expression field: (identifier) @function.call))

; Types

(named_type name: (identifier) @type)
(type_parameters (identifier) @type)
(bounded_type_parameter name: (identifier) @type)
(default_type_parameter name: (identifier) @type)
(labeled_type_argument label: (identifier) @type)
(struct_declaration name: (identifier) @type)
(enum_declaration name: (identifier) @type)
(union_declaration name: (identifier) @type)

; Modules

(qualified_type module: (identifier) @module)
(use (identifier) @module)
(use_path path: (identifier) @module)
(use_path path: (use_path name: (identifier) @module))
(use_group path: (identifier) @module)
(use_group path: (use_path name: (identifier) @module))

((named_type name: (identifier) @type.builtin)
  (#any-of? @type.builtin
    "i8" "i16" "i32" "i64" "int" "u8" "u16" "u32" "u64" "uint" "f32" "f64" "bool"
    "array" "varray" "string" "tuple" "option" "result" "never"))

; Literals

(integer) @number
(float) @number.float
(boolean) @boolean
(string) @string
(escape_sequence) @string.escape
(discard) @variable.builtin
(placeholder) @variable.builtin
"module" @variable.builtin

(comment) @comment

; Keywords

[
  "pub"
  "let"
  "var"
  "struct"
  "enum"
  "union"
  "extern"
  "pass"
  "defer"
] @keyword

"fn" @keyword.function
"use" @keyword.import
"return" @keyword.return
[
  (todo_expression)
  (todo_type)
] @keyword.exception

[
  "if"
  "else"
  "match"
] @keyword.conditional

[
  "while"
  "for"
  "in"
  (break_expression)
  (continue_expression)
] @keyword.repeat

[
  "and"
  "or"
  "not"
  "as"
  "as!"
] @keyword.operator

; Punctuation

[
  "+"
  "-"
  "*"
  "/"
  "%"
  "&"
  "|"
  "|>"
  "^"
  "~"
  "<<"
  ">>"
  "="
  "=="
  "!="
  "<"
  "<="
  ">"
  ">="
  "+="
  "-="
  "*="
  "/="
  "%="
  ".*"
  "->"
] @operator

[
  "("
  ")"
  "["
  "]"
] @punctuation.bracket

[
  ","
  ":"
  ";"
  "."
] @punctuation.delimiter
