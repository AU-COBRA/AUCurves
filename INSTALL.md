Partial installation instructions:

git clone recursive for fiat-crypto and it's submodules.
opam install coq-bignums.8.15.0 
opam install coq-compcert coq-coqprime   (for hacspec)
Newer versions of hacspec depend on math-comp/jasmin machine integers instead of the compcert ones. 

We should be able to install coq-coqutil and coq-coqprime via opam, but they are already included as fiat git submodules.
