#!/bin/bash
#
# 1. Copies benchmarks/qasm_cnotdihedral into pytket-dqc/examples/qasm_cnotdihedral
# 2. Runs  feynopt -purecircuit -inline -cnotmin -simplify -cxcz -simplify  on every circuit and
#    saves the result in pytket-dqc/examples/graysynth_qasm_cnotdihedral
#
# Usage (from the feynman project root):  ./export_cnotdihedral.sh

set -eu

FEYNMAN_DIR="/Users/duykhangnguyentruong/Development/feynman"
PYTKET_DQC_DIR="/Users/duykhangnguyentruong/Development/pytket-dqc"

SRC_DIR="${FEYNMAN_DIR}/benchmarks/qasm_cnotdihedral"
COPY_DIR="${PYTKET_DQC_DIR}/examples/qasm_cnotdihedral"
SYNTH_DIR="${PYTKET_DQC_DIR}/examples/graysynth_qasm_cnotdihedral"

# -purecircuit: treat every qubit as an input (unknown initial state). Without it,
# feynopt optimises QASM as if all qubits start in |0>, which collapses a
# CNOT-dihedral circuit to a few X gates.
FEYNOPT_FLAGS=(-purecircuit -inline -cnotmin)

OK="✅"
BAD="❌"

cd "$FEYNMAN_DIR"

# --- Checks ---
if [ ! -d "${PYTKET_DQC_DIR}/examples" ]; then
    echo "${BAD} pytket-dqc examples folder not found: ${PYTKET_DQC_DIR}/examples"
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

# --- Job 1: copy the original circuits ---
cp "${CIRCUITS[@]}" "$COPY_DIR"/
echo "${OK} Copied ${#CIRCUITS[@]} circuits to ${COPY_DIR}"
echo ""

# --- Job 2: optimise each circuit ---
TOTAL=${#CIRCUITS[@]}
INDEX=0
FAILED=()

for SRC in "${CIRCUITS[@]}"; do
    INDEX=$((INDEX + 1))
    NAME="$(basename "$SRC")"
    OUT="${SYNTH_DIR}/${NAME}"

    RC=0
    "$FEYNOPT" "${FEYNOPT_FLAGS[@]}" "$SRC" > "$OUT" 2> "${OUT}.err" || RC=$?

    if [ "$RC" -eq 0 ] && [ -s "$OUT" ]; then
        printf "[%d/%d] %s %s\n" "$INDEX" "$TOTAL" "$OK" "$NAME"
        rm -f "${OUT}.err"
    else
        printf "[%d/%d] %s %s (exit %d, see %s)\n" "$INDEX" "$TOTAL" "$BAD" "$NAME" "$RC" "${OUT}.err"
        rm -f "$OUT"
        FAILED+=("$NAME")
    fi
done

# --- Summary ---
echo ""
echo "────────────────────────────────────────"
printf "Optimised: %d/%d\n" "$((TOTAL - ${#FAILED[@]}))" "$TOTAL"
if [ "${#FAILED[@]}" -gt 0 ]; then
    echo "Failed:"
    for F in "${FAILED[@]}"; do
        echo "   ${BAD} ${F}"
    done
fi
echo "Originals: ${COPY_DIR}"
echo "Optimised: ${SYNTH_DIR}"
echo "────────────────────────────────────────"