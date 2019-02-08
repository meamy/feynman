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
cabal build feyn
```

This will place the compiled binary `feyn` in the folder `dist/build/feyn/`.

Alternatively, a Makefile is provided which will build Feynman and copy the
executable to the top-level directory. To compile with the makefile simply type

```
make
```

## Using Feynman

Feynman currently has a single frontend, DotQC, a quantum circuit description
language designed for use with [QCViewer](https://github.com/aparent/QCViewer/). 
A description of the .qc file format is available

To run feynman on a .qc file, execute the command

```
feyn <filename>.qc
```

Various optimization algorithms can be run on the input file, including the
[t-par](https://arxiv.org/abs/1303.2042) algorithm:

```
./feyn -tpar <filename>.qc
```

Other options include `-phasefold` and `-cnotmin`. The former applies a
variation of the t-par algorithm where circuits are not re-synthesized, while
the latter attempts to resynthesize circuits minimizing CNOT counts.

### Benchmarks

The Feynman repository comes with a suite of quantum circuit benchmarks, found
in the `benchmarks` folder. For more information on the benchmarks the user is
directed to [T-count optimization and Reed-Muller
codes](https://arxiv.org/abs/1601.07363) for instance.

# Authors

Matthew Amy
