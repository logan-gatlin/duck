(function_declaration) @local.scope
(block) @local.scope

(parameter name: (identifier) @local.definition)
(for_statement variable: (identifier) @local.definition)
(binding pattern: (identifier) @local.definition)
(tuple_pattern (identifier) @local.definition)
(parenthesized_pattern (identifier) @local.definition)
(array_pattern (identifier) @local.definition)
(variant_pattern value: (identifier) @local.definition)
(match_arm pattern: (identifier) @local.definition)

(identifier) @local.reference
