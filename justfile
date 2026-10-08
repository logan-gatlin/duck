grammar := "tree-sitter-duck"
helix_runtime := env("HELIX_RUNTIME", env("XDG_CONFIG_HOME", home_directory() / ".config") / "helix" / "runtime")

# Install duck and the Helix grammar
install: install-duck install-grammar

# Install the duck CLI, which is also the language server
install-duck:
    cargo install --locked --path crates/duck

# Compile the tree-sitter grammar into Helix's runtime, alongside its queries
install-grammar:
    mkdir -p "{{helix_runtime}}/grammars" "{{helix_runtime}}/queries/duck"
    cc -shared -fPIC -fno-exceptions -O3 -std=c11 -I {{grammar}}/src \
        {{grammar}}/src/parser.c {{grammar}}/src/scanner.c \
        -o "{{helix_runtime}}/grammars/duck.so"
    cp {{grammar}}/helix/queries/*.scm "{{helix_runtime}}/queries/duck/"
