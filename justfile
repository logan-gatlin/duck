grammar := "tree-sitter-duck"
helix_runtime := env("HELIX_RUNTIME", env("XDG_CONFIG_HOME", home_directory() / ".config") / "helix" / "runtime")

# Install duck, duck-lsp, and the Helix grammar
install: install-duck install-lsp install-grammar

# Install the duck CLI
install-duck:
    cargo install --locked --path crates/duck

# Install the language server
install-lsp:
    cargo install --locked --path crates/duck-lsp

# Compile the tree-sitter grammar into Helix's runtime, alongside its queries
install-grammar:
    mkdir -p "{{helix_runtime}}/grammars" "{{helix_runtime}}/queries/duck"
    cc -shared -fPIC -fno-exceptions -O3 -std=c11 -I {{grammar}}/src \
        {{grammar}}/src/parser.c {{grammar}}/src/scanner.c \
        -o "{{helix_runtime}}/grammars/duck.so"
    cp {{grammar}}/helix/queries/*.scm "{{helix_runtime}}/queries/duck/"
