# λama
![alt text](https://github.com/FedericoAureliano/llama/blob/master/images/llama.jpg "Logo by Elizabeth Polgreen")

# Ubuntu 18.04
```sh
# You need cvc4 in your path. 
# The easiest way to get it is by running
sudo apt install cvc4

# Build llama by running
cargo build --release

# Run llama on a .synth file by running
./target/release/llama examples/fib.synth
```