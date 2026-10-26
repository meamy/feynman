#!/bin/bash
#
# Usage:
#   ./run_dqc.sh                 # circuits listed in CIRCUITS below, from benchmarks/qc
#   ./run_dqc.sh cnotdihedral    # every .qc file in benchmarks/qc_cnotdihedral

set -e

CIRCUITS=(
    adder_8
    barenco_tof_3
    barenco_tof_4
    barenco_tof_5
    barenco_tof_10
    csla_mux_3
    csum_mux_9
    # cycle_17_3
    # fprenorm
    "gf2^4_mult"
    "gf2^5_mult"
    "gf2^6_mult"
    "gf2^7_mult"
    "gf2^8_mult"
    "gf2^9_mult"
    # "gf2^10_mult"
    # "gf2^16_mult"
    # grover_5
    ham15-high
    ham15-low
    ham15-med
    hwb6
    # hwb8
    # hwb10
    # hwb12
    mod_adder_1024
    # "mod_adder_1048576"
    mod_mult_55
    mod_red_21
    mod5_4
    qcla_adder_10
    qcla_com_7
    qcla_mod_7
    # qft_4
    rc_adder_6
    tof_3
    tof_4
    tof_5
    tof_10
    vbe_adder_3
)

FEYNMAN_DIR="/Users/duykhangnguyentruong/Development/feynman"
HYPERGRAPH_SRC_DIR="${FEYNMAN_DIR}/hypergraphpartitiondata"
BENCHMARKS_BASE="/Users/duykhangnguyentruong/Development/Benchmark_Analysis_Data/Partitions"

PARTITION=2

# --- Which benchmark set to run ---
SUITE="${1:-default}"
case "$SUITE" in
    default)
        SRC_DIR="benchmarks/qc"
        OUT_DIR="benchmarks/qc_customized"
        TIMINGS_CSV="pruned_algebraic_timings_distribute_${PARTITION}.csv"
        EBITS_CSV="ebits_distribute_${PARTITION}.csv"
        ;;
    cnotdihedral)
        SRC_DIR="benchmarks/qc_cnotdihedral"
        OUT_DIR="benchmarks/distributed_qc_cnotdihedral"
        TIMINGS_CSV="pruned_algebraic_timings_distribute_${PARTITION}_cnotdihedral.csv"
        EBITS_CSV="algebraic_ebits_distribute_${PARTITION}_cnotdihedral.csv"
        # Use every circuit in the folder (zero-padded names keep them in order)
        shopt -s nullglob
        CIRCUITS=()
        for f in "$SRC_DIR"/*.qc; do
            CIRCUITS+=("$(basename "$f" .qc)")
        done
        shopt -u nullglob
        if [ "${#CIRCUITS[@]}" -eq 0 ]; then
            echo "No .qc files found in $SRC_DIR (run: cabal run gen-cnotdihedral)"
            exit 1
        fi
        ;;
    *)
        echo "Unknown suite: $SUITE (use: cnotdihedral, or no argument)"
        exit 1
        ;;
esac

mkdir -p "$OUT_DIR"

OK="✅"
BAD="❌"
WARN="⚠️ "

TOTAL=${#CIRCUITS[@]}
INDEX=0
PASSED=()
FAILED=()
TIME_NAMES=()
TIME_VALUES=()
EBIT_VALUES=()

# Print one aligned result row: icon, step label, detail
row() {
    printf "   %s  %-13s %s\n" "$1" "$2" "$3"
}

# Wall-clock time in seconds with millisecond precision.
# (macOS `date` has no %N, so use perl, which ships with macOS.)
now() {
    perl -MTime::HiRes=time -e 'printf "%.3f\n", time'
}

# Difference of two timestamps, formatted as seconds
elapsed() {
    awk -v s="$1" -v e="$2" 'BEGIN { printf "%.3f", e - s }'
}

# E-bit count from a distributed .qc file: the "# Ebit cost: N" line of the report
read_ebits() {
    EBITS=$(grep -m1 -E '^#[[:space:]]*Ebit cost:' "$1" | grep -oE '[0-9]+' | head -n 1 || true)
}

# Append one row to the e-bit CSV:
#   circuit, ebits, seconds, distribution, equivalence
record() {
    echo "\"$1\",$2,$3,\"$4\",\"$5\"" >> "$EBITS_CSV"
}

echo "Building..."
cabal build -v0
# Call the built binaries directly so timings don't include cabal's startup overhead
FEYNOPT="$(cabal list-bin feynopt)"
FEYNVER="$(cabal list-bin feynver)"
echo "Input:  $SRC_DIR"
echo "Output: $OUT_DIR"
echo ""

echo "circuit,status,seconds" > "$TIMINGS_CSV"
echo "circuit,ebits,seconds,distribution,equivalence" > "$EBITS_CSV"

for CIRCUIT in "${CIRCUITS[@]}"; do
    INDEX=$((INDEX + 1))
    printf "[%d/%d] %s\n" "$INDEX" "$TOTAL" "$CIRCUIT"

    SOURCE_FILE="${SRC_DIR}/${CIRCUIT}.qc"
    TARGET_FILE="${OUT_DIR}/distributed_rankSynth_${PARTITION}_${CIRCUIT}.qc"

    # --- Step 1: optimise + distribute (timed) ---
    START=$(now)
    OPT_RC=0
    "$FEYNOPT" -inline -O2 -simplify -distribute "${PARTITION}" "$SOURCE_FILE" > "$TARGET_FILE" || OPT_RC=$?
    END=$(now)
    DURATION=$(elapsed "$START" "$END")

    TIME_NAMES+=("$CIRCUIT")
    TIME_VALUES+=("$DURATION")

    if [ "$OPT_RC" -ne 0 ]; then
        row "$BAD" "Optimize" "feynopt failed after ${DURATION}s (exit ${OPT_RC})"
        row "-" "Verify" "skipped"
        echo "\"${CIRCUIT}\",fail,${DURATION}" >> "$TIMINGS_CSV"
        record "$CIRCUIT" "" "$DURATION" "feynopt failed" "skipped"
        EBIT_VALUES+=("-")
        echo ""
        FAILED+=("$CIRCUIT")
        continue
    fi
    row "$OK" "Compiled" "${DURATION}s"
    echo "\"${CIRCUIT}\",ok,${DURATION}" >> "$TIMINGS_CSV"

    read_ebits "$TARGET_FILE"
    EBIT_VALUES+=("${EBITS:--}")
    row "$OK" "E-bits" "${EBITS:-not found}"

    # --- Step 2: distribution check (read from the generated .qc header) ---
    VERIFY_LINE=$(grep -m1 -E '^#[[:space:]]*Distribution:' "$TARGET_FILE" || true)
    VERIFY_STATUS=$(printf '%s' "$VERIFY_LINE" | sed -E 's/^#[[:space:]]*Distribution:[[:space:]]*//')

    if [ -z "$VERIFY_LINE" ]; then
        row "$WARN" "Distribution" "status not found in output"
    elif printf '%s' "$VERIFY_STATUS" | grep -q "FAIL"; then
        row "$BAD" "Distribution" "$VERIFY_STATUS"
        row "-" "Equivalence" "skipped"
        record "$CIRCUIT" "$EBITS" "$DURATION" "$VERIFY_STATUS" "skipped"
        echo ""
        FAILED+=("$CIRCUIT")
        continue
    else
        row "$OK" "Distribution" "$VERIFY_STATUS"
    fi

    # --- Step 3: feynver equivalence check ---
    FEYNVER_RC=0
    FEYNVER_OUT=$("$FEYNVER"  -ignore-global-phase -channel "$SOURCE_FILE" "$TARGET_FILE" 2>&1) || FEYNVER_RC=$?
    FEYNVER_LINE=$(printf '%s\n' "$FEYNVER_OUT" | grep -v '^[[:space:]]*$' | tail -n 1)

    if [ "$FEYNVER_RC" -eq 0 ] && printf '%s' "$FEYNVER_LINE" | grep -q '^Equal'; then
        row "$OK" "Equivalence" "$FEYNVER_LINE"
        PASSED+=("$CIRCUIT")
    else
        row "$BAD" "Equivalence" "${FEYNVER_LINE:-feynver failed (exit ${FEYNVER_RC})}"
        FAILED+=("$CIRCUIT")
    fi
    record "$CIRCUIT" "$EBITS" "$DURATION" \
           "${VERIFY_STATUS:-not found}" "${FEYNVER_LINE:-feynver failed (exit ${FEYNVER_RC})}"

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

echo ""
echo "E-bits and optimize + distribute time per circuit:"
printf "   %-28s %8s %11s\n" "circuit" "e-bits" "time"
TOTAL_TIME=0
for i in "${!TIME_NAMES[@]}"; do
    printf "   %-28s %8s %10ss\n" "${TIME_NAMES[$i]}" "${EBIT_VALUES[$i]}" "${TIME_VALUES[$i]}"
    TOTAL_TIME=$(awk -v a="$TOTAL_TIME" -v b="${TIME_VALUES[$i]}" 'BEGIN { printf "%.3f", a + b }')
done
printf "   %-28s %8s %10ss\n" "TOTAL" "" "$TOTAL_TIME"
echo "Timings saved to ${TIMINGS_CSV}"
echo "E-bits saved to  ${EBITS_CSV}"
echo "────────────────────────────────────────"