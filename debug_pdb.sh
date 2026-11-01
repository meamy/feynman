#!/usr/bin/env bash
set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR"

echo "=========================================================="
echo "    Feynman PDB-style Debugger (-qasm3 measure_assign)   "
echo "=========================================================="
echo "Commands to run inside GHCi:"
echo "1. Set breakpoint in FeynOpt:  :break Main 359"
echo "2. Set breakpoint in QASM3:    :break Feynman.Frontend.OpenQASM3.Utils 287"
echo "3. Run with QASM3:             :main -qasm3 benchmarks/qasm3/measure_assign.qasm"
echo ""
echo "While paused at breakpoint:"
echo "  :step         - step to next expression"
echo "  :trace        - trace evaluations"
echo "  :back / :fwd  - step backwards / forwards in time"
echo "  :print <var>  - inspect variable without forcing thunk"
echo "  :continue     - resume"
echo "  :quit         - exit debugger"
echo "=========================================================="

cabal repl exe:feynopt
