#!/bin/bash

set -e

CIRCUITS=(
    # adder_8
    # barenco_tof_3
    # barenco_tof_4
    # barenco_tof_5
    # barenco_tof_10
    # csla_mux_3
    # csum_mux_9
    # "gf2^4_mult"
    # "gf2^5_mult"
    # "gf2^6_mult"
    # "gf2^7_mult"
    # "gf2^8_mult"
    #"gf2^9_mult"
    "gf2^10_mult"
    # "gf2^16_mult"
    # ham15-low
    # ham15-med
    # hwb6
    mod_adder_1024
    # mod_mult_55
    # mod_red_21
    # mod5_4
    # qcla_adder_10
    # qcla_com_7
    # qcla_mod_7
    # rc_adder_6
    # tof_3
    # tof_4
    # tof_5
    # tof_10
    # vbe_adder_3
)

FEYNMAN_DIR="/Users/duykhangnguyentruong/Development/feynman"
HYPERGRAPH_SRC_DIR="${FEYNMAN_DIR}/hypergraphpartitiondata"
BENCHMARKS_BASE="/Users/duykhangnguyentruong/Development/Benchmark_Analysis_Data/Partitions"

PARTITION=2

OK="✅"
BAD="❌"
WARN="⚠️ "

TOTAL=${#CIRCUITS[@]}
INDEX=0
PASSED=()
FAILED=()

# Print one aligned result row: icon, step label, detail
row() {
    printf "   %s  %-13s %s\n" "$1" "$2" "$3"
}

echo "Building..."
cabal build -v0
echo ""

for CIRCUIT in "${CIRCUITS[@]}"; do
    INDEX=$((INDEX + 1))
    printf "[%d/%d] %s\n" "$INDEX" "$TOTAL" "$CIRCUIT"

    TARGET_FILE="benchmarks/qc_customized/distributed_rankSynth_${PARTITION}_${CIRCUIT}.qc"

    # --- Step 1: optimise + distribute ---
    if ! cabal run -v0 feynopt -- -inline -simplify -distribute "${PARTITION}" "benchmarks/qc/${CIRCUIT}.qc" > "$TARGET_FILE"; then
        row "$BAD" "Optimize" "feynopt failed"
        row "-" "Verify" "skipped"
        echo ""
        FAILED+=("$CIRCUIT")
        continue
    fi

    # --- Step 2: distribution check (read from the generated .qc header) ---
    VERIFY_LINE=$(grep -m1 -E '^#[[:space:]]*Distribution:' "$TARGET_FILE" || true)
    VERIFY_STATUS=$(printf '%s' "$VERIFY_LINE" | sed -E 's/^#[[:space:]]*Distribution:[[:space:]]*//')

    if [ -z "$VERIFY_LINE" ]; then
        row "$WARN" "Distribution" "status not found in output"
    elif printf '%s' "$VERIFY_STATUS" | grep -q "FAIL"; then
        row "$BAD" "Distribution" "$VERIFY_STATUS"
        row "-" "Equivalence" "skipped"
        echo ""
        FAILED+=("$CIRCUIT")
        continue
    else
        row "$OK" "Distribution" "$VERIFY_STATUS"
    fi

    # --- Step 3: feynver equivalence check ---
    FEYNVER_RC=0
    FEYNVER_OUT=$(cabal run -v0 feynver -- -channel "benchmarks/qc/${CIRCUIT}.qc" "$TARGET_FILE" 2>&1) || FEYNVER_RC=$?
    FEYNVER_LINE=$(printf '%s\n' "$FEYNVER_OUT" | grep -v '^[[:space:]]*$' | tail -n 1)

    if [ "$FEYNVER_RC" -eq 0 ] && printf '%s' "$FEYNVER_LINE" | grep -q '^Equal'; then
        row "$OK" "Equivalence" "$FEYNVER_LINE"
        PASSED+=("$CIRCUIT")
    else
        row "$BAD" "Equivalence" "${FEYNVER_LINE:-feynver failed (exit ${FEYNVER_RC})}"
        FAILED+=("$CIRCUIT")
    fi

    # # Destination directory for this circuit
    # DEST_DIR="${BENCHMARKS_BASE}/${CIRCUIT}"

    # # Create destination directory if it doesn't exist
    # mkdir -p "${DEST_DIR}"

    # # Copy hypergraph files
    # cp "${HYPERGRAPH_SRC_DIR}/hypergraph.hgr" "${HYPERGRAPH_SRC_DIR}/partition.hgr" "${HYPERGRAPH_SRC_DIR}/optimalpartition.hgr" "${DEST_DIR}/"
    # cp "${HYPERGRAPH_SRC_DIR}/partition.hgr" "/Users/duykhangnguyentruong/Development/pytket-dqc/examples/partitions/${CIRCUIT}.hgr"

    echo ""
done

# --- Summary ---
echo "────────────────────────────────────────"
printf "Done: %s %d passed   %s %d failed   (of %d)\n" "$OK" "${#PASSED[@]}" "$BAD" "${#FAILED[@]}" "$TOTAL"
if [ "${#FAILED[@]}" -gt 0 ]; then
    echo "Failed circuits:"
    for C in "${FAILED[@]}"; do
        echo "   $BAD $C"
    done
fi
echo "────────────────────────────────────────"
