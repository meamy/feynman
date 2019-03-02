# Feynman

Feynman is a toolkit for quantum circuit analysis in the path integral
model of quantum mechnics. The toolkit comprises synthesis, 
optimization and verification methods based around representations of 
circuit actions as sums-over-paths.

Two ways of interfacing with the Feynman project are possible. Standalone
tools built on Feynman, found in [tools](https://github.com/meamy/feynman/tree/master/tools), 
provide command-line interfaces for optimizing and/or verifying
quantum circuits, or the [Feynman](https://github.com/meamy/feynman/tree/master/src/Feynman) 
library can be imported and used directly in other Haskell projects.


## Prerequisites

The Feynman project requires GHC >=8.0.2 and Cabal >=1.24.0. Older versions of
GHC may work but have not been tested.

Feynman depends on a number of open-source packages hosted on Hackage. To
compile the dependencies locally execute the commands

```
cabal sandbox init
cabal install --dependencies-only
```

If global packages are installed or otherwise desired (not recommended!), the
user may omit the `cabal sandbox init` command.

## Building from source

Once all dependencies have been met, Feynman can be built from the top-level
directory with the command

```
cabal build
```

This will build the Feynman library, as well as binary tools for optimizing
(`feynopt`) and equivalence checking circuits (`feynver`), found in the 
`dist/build/` folder.

Alternatively, a Makefile is provided which will build Feynman and copy the
executables to the top-level directory. To compile with the makefile simply
execute the command

```
make
```

## Using feynopt

Feynman currently has frontends for
[openQASM](https://github.com/Qiskit/openqasm/blob/master/spec/qasm2.rst) and
[.qc](https://circuits.qsoft.iqc.uwaterloo.ca/about/spec).
Examples of both can be found in the
[benchmarks](https://github.com/meamy/feynman/tree/master/benchmarks) folder.

To run the Feynman optimizer `feynopt` on a .qc or openQASM file, execute the
command

```
feynopt <filename>.(qc | qasm)
```

`feynopt` automatically recognizes the extensions .qc and .qasm as .qc and
openQASM files, respectively.

For a list of all available optimizations and transformations, use the command

```
feynopt -h
```

## Using feynver

The `feynver` binary tool allows for equivalence checking of separate circuit
files. Standard usage is

```
feynver <filename1>.qc <filename2>.qc
```

The input circuits must agree on the names of the primary inputs (i.e. non-initialized qubits),
but they may use different ancillas.

*Note: `feynver` currently only supports the .qc frontend*

### Benchmarks

The Feynman repository comes with a suite of quantum circuit benchmarks, found
in the `benchmarks` folder. For more information on the benchmarks the user is
directed to [Formal Methods in Quantum Circuit
Design](http://hdl.handle.net/10012/14480).

The benchmark suite also includes example openQASM circuits, taken from the
openQASM github
[repository](https://github.com/Qiskit/openqasm/tree/master/examples).

# Authors

Matthew Amy
