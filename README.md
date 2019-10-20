# llama
[ʎ](https://en.wikipedia.org/wiki/Ye%C3%ADsmo)ama is (will be) a playground for enumerating [smt-lib](http://smtlib.cs.uiowa.edu/index.shtml) functions.

# Prerequisites
- [OCaml](https://ocaml.org/)
- [dune](https://dune.build/)

# Build
```sh
# You can skip this if you want
dune build @install
```

# Run
```sh
# Builds and executes bin/llama.ml
dune exec llama 
```

# Clean
```sh
dune clean 
```