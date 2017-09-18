# Feyman

## What is Feynman?

Feynman is a set of algorithms and tools designed to explore the use of
Richard Feynman's sum-over-paths technique in quantum circuit analysis,
optimization and simulation. More accurately it's the vessel for one lowly 
PhD student (Matthew Amy)'s research.

## Prerequisites

The Feynman project requires GHC >=8.0.2 and Cabal >=1.24.0. Older versions of
GHC may work but have not been tested.

Feynman depends on a number of open-source packages hosted on Hackage. To
compile the dependencies locally execute the commands

```
cabal sandbox init
cabal install --dependencies-only
```

If global packages are installed or otherwise desried (not recommended!), the
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

The [t-par](https://arxiv.org/abs/1303.2042) algorithm can be run with

```
./feyn -tpar *.qc
```

Other options include `-phasefold` and `-cnotmin`, which are very mysterious.

More to come...
