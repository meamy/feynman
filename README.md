This branch contains a script verifying a number of circuit constructions for
some small but non-trivial sizes, hard-coded up to 64 qubits but it can be
pushed higher. Verification is done in the path-sum framework (see, e.g., 
[arXiv:1805.06908](https://arxiv.org/abs/1805.06908v2)) with extensions to allow
the verification of channels.

To run the verification script, from the command line execute the following
command:

```
cabal run ar20
```
