; Helix highlights for Duck. Later patterns take precedence.

; Identifiers

(identifier) @variable

(parameter name: (identifier) @variable.parameter)

(field_declaration name: (identifier) @variable.other.member)
(field_expression field: (identifier) @variable.other.member)
(field_expression field: (tuple_index) @constant.numeric.integer)
(labeled_argument label: (identifier) @variable.other.member)
(module_property name: (identifier) @variable.other.member)

(enum_member name: (identifier) @type.enum.variant)
(union_variant name: (identifier) @type.enum.variant)
(dot_expression name: (identifier) @type.enum.variant)
(variant_pattern name: (identifier) @type.enum.variant)

; Functions

(function_declaration name: (identifier) @function)
(extern_function name: (identifier) @function)

(call_expression function: (identifier) @function)
(call_expression
  function: (field_expression field: (identifier) @function.method))

; Types

(named_type name: (identifier) @type)
(type_parameters (identifier) @type.parameter)
(bounded_type_parameter name: (identifier) @type.parameter)
(struct_declaration name: (identifier) @type)
(enum_declaration name: (identifier) @type)
(union_declaration name: (identifier) @type)

; Modules

(qualified_type module: (identifier) @namespace)
(use (identifier) @namespace)
(use_path path: (identifier) @namespace)
(use_path path: (use_path name: (identifier) @namespace))
(use_group path: (identifier) @namespace)
(use_group path: (use_path name: (identifier) @namespace))

((named_type name: (identifier) @type.builtin)
  (#any-of? @type.builtin
    "i8" "i16" "i32" "i64" "int" "u8" "u16" "u32" "u64" "uint" "f32" "f64" "bool"
    "array" "varray" "string" "tuple" "option" "result" "externref"))

; Literals

(integer) @constant.numeric.integer
(float) @constant.numeric.float
(boolean) @constant.builtin.boolean
(string) @string
(escape_sequence) @constant.character.escape
(discard) @variable.builtin
(placeholder) @variable.builtin
"module" @variable.builtin

(comment) @comment.line

; Keywords

"pass" @keyword

[
  "let"
  "var"
  "struct"
  "enum"
  "union"
] @keyword.storage.type

[
  "pub"
  "extern"
] @keyword.storage.modifier

"fn" @keyword.function
"use" @keyword.control.import
"return" @keyword.control.return
"defer" @keyword.control

[
  "if"
  "else"
  "match"
] @keyword.control.conditional

[
  "while"
  "for"
  "in"
  "break"
  "continue"
] @keyword.control.repeat

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
