# Simple Proof Assistant

This is a simple propositional prover written in OCaml. To try it you must have the ```ocaml``` package.

You can compile the code using the ```make``` command.

Then, try to proof something by running the following command:
```sh
./prover
```
and write it step by step.

I have prepared some examples in the [proofs](/proofs) directory that you can try like this:
```sh
cat proofs/andcomm.proof | ./prover
```