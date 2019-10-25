# llama-synth
![alt text](https://github.com/FedericoAureliano/llama-synth/blob/master/images/llama.PNG "llama-synth logo")

Lambda Loves Synthesis ([ʎ](https://en.wikipedia.org/wiki/Ye%C3%ADsmo) Ama Synthesis) is (will be) a playground for enumerating [smt-lib](http://smtlib.cs.uiowa.edu/index.shtml) functions.

# Prerequisites
- [OCaml](https://ocaml.org/)
- [Dune](https://dune.build/)

# Build
```sh
# You can skip this
dune build @install
```

# Run
```sh
# Executes bin/llama.ml
dune exec llama 
```

# Clean
```sh
dune clean 
```