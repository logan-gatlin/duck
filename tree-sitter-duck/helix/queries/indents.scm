[
  (function_declaration)
  (extern_block)
  (struct_declaration)
  (enum_declaration)
  (if_statement)
  (while_statement)
  (for_statement)

  (parameters)
  (type_parameters)
  (type_arguments)
  (arguments)
  (list)
  (repeated_list)
  (tuple)
  (tuple_pattern)
  (parenthesized_expression)
] @indent

[
  (function_declaration)
  (extern_block)
  (struct_declaration)
  (enum_declaration)
  (if_statement)
  (while_statement)
  (for_statement)
] @extend

[
  (return_statement)
  (break_statement)
  (continue_statement)
  (pass_statement)
] @extend.prevent-once

[
  ")"
  "]"
] @outdent

(else_clause
  "else" @outdent)
