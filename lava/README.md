# Lava: Translating Liquid Haskell Programs to Rocq

## Installation

**Liquid Haskell.**
Make sure you have GHC version 9.12.2 installed.
The easiest is to install it from [GHCup](https://www.haskell.org/ghcup/).
Liquid Haskell (version 0.9.12.2) will be automatically installed with other dependencies.
You will also need an SMT solver in your path: one of
[Z3](https://github.com/Z3Prover/z3), [CVC4](https://cvc4.github.io/) or [MathSat](https://mathsat.fbk.eu/).

**Rocq.**
We recommand installing Rocq through [Opam](https://opam.ocaml.org/).
Install Opam by following [these instructions](https://opam.ocaml.org/doc/Install.html).
Initialise Opam by running:
```sh
opam init
eval $(opam env)
```
Second, install Rocq version 9.0.0.
For this, the easiest is to create a switch for the project:
```sh
opam switch create 4.14.2
opam pin add rocq-prover 9.0.0 -y
```
(If you already have a working OCaml install compatible with Rocq 9.0.0,
you can directly install Rocq without creating a switch.)
Finally, install the additional repositories necessary for some dependencies, and Lava.
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam update -y; eval $(opam env)
opam pin add -n -y -k path lava .
opam install --confirm-level=unsafe-yes -j 2 lava --deps-only
```

**Lava.**
To build Lava, you can use either Cabal or Stack (both installed through GHCup)
by running `cabal build` or `stack build`.
Documentation is generated through `cabal haddock` or `stack haddock`.

## Benchmarks

The benchmarks are in the folder [`lhExamples`](lhExamples).
To translate them to Rocq, use `cabal bench` or `stack bench`.
Their outputs are in the [`out`](out) folder, and have the extension `.v`.
To compile (and check proofs of) all the files, use `make rocq` from the root of the project.

### Adding benchmarks

To translate another Liquid Haskell file to Rocq, simply add it somewhere in `lhExamples`,
then add it to the `other-modules` field of `lh-examples-bench` in [`package.yaml`](package.yaml).
Then, run either `stack bench` or
```sh
hpack # rebuild lava.cabal
cabal bench
```

To run Rocq on the output, first make sure that the Rocq dependencies (in
[`coqDeps`](coqDeps)) are compiled (this is the case after `make rocq`).
Then, directly use Rocq's compiler `rocqc` on the file, or open it in an IDE
with support for Rocq.

### Measuring time

**Liquid Haskell verification + Lava translation.**
TODO

**Rocq translations.**
In the [`out`](out) folder, additional `.v.timing` files contain line-by-line
reports of each file's verification time.

**Generate a CSV file.**
TODO
