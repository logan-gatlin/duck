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
  (defer_statement body: (block))

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
  (defer_statement body: (block))
] @extend

[
  (expression_statement (return_expression))
  (expression_statement (pipe_expression body: (return_expression)))
  (expression_statement (break_expression))
  (expression_statement (continue_expression))
  (pass_statement)
] @extend.prevent-once

[
  ")"
  "]"
] @outdent

(else_clause
  "else" @outdent)
