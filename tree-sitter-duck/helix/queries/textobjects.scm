(function_declaration body: (block) @function.inside) @function.around

(struct_declaration) @class.around
(enum_declaration) @class.around
(union_declaration) @class.around

(parameter) @parameter.inside
(labeled_argument) @parameter.inside
(arguments (_expression) @parameter.inside)
(parameter_types (_type) @parameter.inside)

(comment) @comment.inside
(comment)+ @comment.around
