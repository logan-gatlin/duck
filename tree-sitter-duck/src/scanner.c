// Layout tokens for Duck: the newline that ends a logical line, and the
// indent/dedent around a block. Mirrors `Lexer::indentation` in
// `crates/duck-compiler/src/lex.rs`: blank and comment-only lines are ignored,
// as are line breaks inside brackets and before a deeper line that starts with
// `|>`.

#include "tree_sitter/array.h"
#include "tree_sitter/parser.h"

#include <stdint.h>
#include <string.h>

enum TokenType {
    NEWLINE,
    INDENT,
    DEDENT,
    CLOSE_PAREN,
    CLOSE_BRACKET,
    CLOSE_BRACE,
    ERROR_SENTINEL,
};

typedef struct {
    // Indentation width of each open block; the bottom is always 0.
    Array(uint16_t) indents;
} Scanner;

static inline void skip(TSLexer *lexer) { lexer->advance(lexer, true); }

void *tree_sitter_duck_external_scanner_create(void) {
    Scanner *scanner = ts_calloc(1, sizeof(Scanner));
    array_init(&scanner->indents);
    array_push(&scanner->indents, 0);
    return scanner;
}

void tree_sitter_duck_external_scanner_destroy(void *payload) {
    Scanner *scanner = payload;
    array_delete(&scanner->indents);
    ts_free(scanner);
}

unsigned tree_sitter_duck_external_scanner_serialize(void *payload, char *buffer) {
    Scanner *scanner = payload;
    unsigned size = 0;
    // The bottom entry is implied.
    for (uint32_t i = 1; i < scanner->indents.size; i++) {
        if (size + sizeof(uint16_t) > TREE_SITTER_SERIALIZATION_BUFFER_SIZE) {
            break;
        }
        memcpy(buffer + size, array_get(&scanner->indents, i), sizeof(uint16_t));
        size += sizeof(uint16_t);
    }
    return size;
}

void tree_sitter_duck_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {
    Scanner *scanner = payload;
    array_clear(&scanner->indents);
    array_push(&scanner->indents, 0);
    for (unsigned i = 0; i + sizeof(uint16_t) <= length; i += sizeof(uint16_t)) {
        uint16_t indent;
        memcpy(&indent, buffer + i, sizeof(uint16_t));
        array_push(&scanner->indents, indent);
    }
}

bool tree_sitter_duck_external_scanner_scan(void *payload, TSLexer *lexer, const bool *valid_symbols) {
    Scanner *scanner = payload;

    bool error_recovery = valid_symbols[ERROR_SENTINEL];
    bool within_brackets = !error_recovery &&
        (valid_symbols[CLOSE_PAREN] || valid_symbols[CLOSE_BRACKET] || valid_symbols[CLOSE_BRACE]);
    bool layout_valid = valid_symbols[NEWLINE] || valid_symbols[INDENT] || valid_symbols[DEDENT];

    // Layout tokens are zero-width, sitting before the line break they stand
    // for, so the whitespace and comments after them are lexed as usual.
    lexer->mark_end(lexer);

    bool found_end_of_line = false;
    uint32_t indent = 0;
    int32_t first_comment_indent = -1;
    for (;;) {
        if (lexer->lookahead == '\n' || lexer->lookahead == '\r') {
            found_end_of_line = true;
            indent = 0;
            skip(lexer);
        } else if (lexer->lookahead == ' ' || lexer->lookahead == '\t') {
            // Tabs and spaces weigh the same: the compiler requires a block's
            // indentation to extend that of its parent, so in a valid file
            // comparing widths is comparing prefixes.
            indent++;
            skip(lexer);
        } else if (lexer->lookahead == '#' && layout_valid) {
            // A comment trailing a line's tokens: leave it, and the line
            // break after it, for the next scan.
            if (!found_end_of_line) {
                return false;
            }
            if (first_comment_indent == -1) {
                first_comment_indent = (int32_t)indent;
            }
            while (!lexer->eof(lexer) && lexer->lookahead != '\n' && lexer->lookahead != '\r') {
                skip(lexer);
            }
            indent = 0;
        } else if (lexer->eof(lexer)) {
            found_end_of_line = true;
            indent = 0;
            break;
        } else {
            break;
        }
    }

    if (!found_end_of_line) {
        return false;
    }

    uint16_t current = *array_back(&scanner->indents);

    // A deeper line starting with `|>` continues the line above, so the line
    // break is only whitespace. The token's end is already marked, so looking
    // past the `|` doesn't change what is produced otherwise.
    if (indent > current && lexer->lookahead == '|') {
        skip(lexer);
        if (lexer->lookahead == '>') {
            return false;
        }
    }

    if (valid_symbols[INDENT] && indent > current) {
        array_push(&scanner->indents, (uint16_t)indent);
        lexer->result_symbol = INDENT;
        return true;
    }

    // A dedent is produced even where the grammar doesn't expect one, as long
    // as the line can't simply end first, so that a broken line doesn't leave
    // the rest of the file nested in its block. A comment indented to the
    // block's level holds the block open until after it.
    if ((valid_symbols[DEDENT] || (!valid_symbols[NEWLINE] && !within_brackets)) &&
        indent < current && first_comment_indent < (int32_t)current) {
        array_pop(&scanner->indents);
        lexer->result_symbol = DEDENT;
        return true;
    }

    if (valid_symbols[NEWLINE] && !error_recovery) {
        lexer->result_symbol = NEWLINE;
        return true;
    }

    return false;
}
