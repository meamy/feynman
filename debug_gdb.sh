#!/usr/bin/env bash
# Launch feynopt with GDB on OpenQASM 3 measure assignment
set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR"

echo "=== Starting GDB with feynopt (-qasm3 measure_assign.qasm) ==="
echo "Tips:"
echo "  b FeynOpt.hs:359      - break at parseArgs"
echo "  b Utils.hs:287        - break at OpenQASM 3 MeasureExpr handler"
echo "  b Utils.hs:249        - break at MeasureArrowAssignmentStmt handler"
echo "  r                     - run"
echo "  bt                    - backtrace"
echo "==============================================================="

gdb -ex "break FeynOpt.hs:359" -ex "break Utils.hs:287" --args ./bin/feynopt -qasm3 benchmarks/qasm3/measure_assign.qasm "$@"
