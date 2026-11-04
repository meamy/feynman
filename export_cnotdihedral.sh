#!/bin/bash
#
# 1. Runs  feynopt -purecircuit  on every circuit in benchmarks/qasm_cnotdihedral and
#    saves the result in pytket-dqc/examples/benchmarks/circuits/qasm_cnotdihedral
# 2. Runs  feynopt -purecircuit -inline -cnotmin -cxcz -simplify  on every circuit and
#    saves the result in pytket-dqc/examples/benchmarks/circuits/graysynth_qasm_cnotdihedral
#
# Usage (from the feynman project root):  ./export_cnotdihedral.sh

set -eu

FEYNMAN_DIR="/Users/duykhangnguyentruong/Development/feynman"
PYTKET_DQC_DIR="/Users/duykhangnguyentruong/Development/pytket-dqc"

SRC_DIR="${FEYNMAN_DIR}/benchmarks/qasm_cnotdihedral"
COPY_DIR="${PYTKET_DQC_DIR}/examples/benchmarks/circuits/qasm_cnotdihedral"
SYNTH_DIR="${PYTKET_DQC_DIR}/examples/benchmarks/circuits/graysynth_qasm_cnotdihedral"

# -purecircuit: treat every qubit as an input (unknown initial state). Without it,
# feynopt optimises QASM as if all qubits start in |0>, which collapses a
# CNOT-dihedral circuit to a few X gates.
PURE_FLAGS=(-purecircuit)
FEYNOPT_FLAGS=(-purecircuit -inline -cnotmin)

OK="✅"
BAD="❌"

cd "$FEYNMAN_DIR"

# --- Checks ---
if [ ! -d "${PYTKET_DQC_DIR}/examples/benchmarks" ]; then
    echo "${BAD} pytket-dqc benchmarks folder not found: ${PYTKET_DQC_DIR}/examples/benchmarks"
    exit 1
fi

shopt -s nullglob
CIRCUITS=("$SRC_DIR"/*.qasm)
shopt -u nullglob
if [ "${#CIRCUITS[@]}" -eq 0 ]; then
    echo "${BAD} No .qasm files in ${SRC_DIR} (run: cabal run gen-cnotdihedral)"
    exit 1
fi

# --- Build once; call the binary directly (same as 'cabal run feynopt --', without the per-call overhead) ---
echo "Building..."
cabal build -v0 feynopt
FEYNOPT="$(cabal list-bin feynopt)"
echo ""

mkdir -p "$COPY_DIR" "$SYNTH_DIR"

# Remove old .qasm files so circuits from earlier generations don't linger
rm -f "$COPY_DIR"/*.qasm "$SYNTH_DIR"/*.qasm

TOTAL=${#CIRCUITS[@]}
PURE_FAILED=()
FAILED=()

# Run feynopt with the given flags on every circuit, writing results to OUT_DIR.
# Failures are appended to the array named by FAILED_VAR.
#   usage: run_feynopt OUT_DIR FAILED_VAR FLAG...
run_feynopt() {
    local OUT_DIR="$1" FAILED_VAR="$2"
    shift 2
    local INDEX=0 SRC NAME OUT RC
    for SRC in "${CIRCUITS[@]}"; do
        INDEX=$((INDEX + 1))
        NAME="$(basename "$SRC")"
        OUT="${OUT_DIR}/${NAME}"

        RC=0
        "$FEYNOPT" "$@" "$SRC" > "$OUT" 2> "${OUT}.err" || RC=$?

        if [ "$RC" -eq 0 ] && [ -s "$OUT" ]; then
            printf "[%d/%d] %s %s\n" "$INDEX" "$TOTAL" "$OK" "$NAME"
            rm -f "${OUT}.err"
        else
            printf "[%d/%d] %s %s (exit %d, see %s)\n" "$INDEX" "$TOTAL" "$BAD" "$NAME" "$RC" "${OUT}.err"
            rm -f "$OUT"
            eval "${FAILED_VAR}+=(\"\$NAME\")"
        fi
    done
}

# Print "<label>: ok/total" and list any failures.
#   usage: report LABEL NAME...
report() {
    local LABEL="$1"
    shift
    printf "%s: %d/%d\n" "$LABEL" "$((TOTAL - $#))" "$TOTAL"
    if [ "$#" -gt 0 ]; then
        echo "Failed:"
        local F
        for F in "$@"; do
            echo "   ${BAD} ${F}"
        done
    fi
}

# --- Job 1: pure circuits (feynopt -purecircuit only) ---
echo "Job 1: feynopt ${PURE_FLAGS[*]}"
run_feynopt "$COPY_DIR" PURE_FAILED "${PURE_FLAGS[@]}"
echo ""

# --- Job 2: optimise each circuit ---
echo "Job 2: feynopt ${FEYNOPT_FLAGS[*]}"
run_feynopt "$SYNTH_DIR" FAILED "${FEYNOPT_FLAGS[@]}"

# --- Summary ---
echo ""
echo "────────────────────────────────────────"
report "Pure     " ${PURE_FAILED[@]+"${PURE_FAILED[@]}"}
report "Optimised" ${FAILED[@]+"${FAILED[@]}"}
echo "Originals: ${COPY_DIR}"
echo "Optimised: ${SYNTH_DIR}"
echo "────────────────────────────────────────"