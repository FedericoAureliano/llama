# llama-synth
![alt text](https://github.com/FedericoAureliano/llama-synth/blob/master/images/llama.jpg "Logo by Elizabeth Polgreen")

Lambda Loves Synthesis ([ʎ](https://en.wikipedia.org/wiki/Ye%C3%ADsmo) Ama Synthesis) is (will be) a playground for enumerating [smt-lib](http://smtlib.cs.uiowa.edu/index.shtml) functions.

# Run
```sh
# executes src/main.rs
# - parses examples/qflia.smt2
# - generates a dot file in qflia.dot
cargo run examples/qflia.smt2 qflia.dot

# to create an image from the dotfile
dot -T png -O qflia.dot
```