[
  (function_declaration)
  (extern_block)
  (struct_declaration)
  (enum_declaration)
  (union_declaration)
  (if_statement)
  (while_statement)
  (for_statement)
  (match_statement)
  (match_arm)
  (else_arm)

  (parameters)
  (type_parameters)
  (type_arguments)
  (arguments)
  (list)
  (repeated_list)
  (tuple)
  (tuple_pattern)
  (array_pattern)
  (parenthesized_expression)
] @indent

[
  (function_declaration)
  (extern_block)
  (struct_declaration)
  (enum_declaration)
  (union_declaration)
  (if_statement)
  (while_statement)
  (for_statement)
  (match_statement)
  (match_arm)
  (else_arm)
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
