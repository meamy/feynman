#!/bin/bash

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
    fprenorm
    "gf2^4_mult"
    "gf2^5_mult"
    "gf2^6_mult"
    "gf2^7_mult"
    "gf2^8_mult"
    "gf2^9_mult"
    "gf2^10_mult"
    "gf2^16_mult"
    # "gf2^32_mult"
    # "gf2^64_mult"
    # grover_5
    ham15-high
    ham15-low
    ham15-med
    hwb6
    # hwb8
    # hwb10
    # mod_adder_1024
    # mod_adder_1048576
    mod_mult_55
    mod_red_21
    mod5_4
    qcla_adder_10
    qcla_com_7
    # qcla_mod_7
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
BENCHMARKS_BASE="/Users/duykhangnguyentruong/Development/Benchmark_Analysis_Report"

cabal build

for CIRCUIT in "${CIRCUITS[@]}"; do
    echo "============================================"
    echo "Processing circuit: ${CIRCUIT}"
    echo "============================================"

    # Run feynopt
    # cabal run feynopt -- -inline -cnotmin -simplify -distribute "benchmarks/qc/${CIRCUIT}.qc" | tee "benchmarks/qc_customized/distributed_cnot_${CIRCUIT}.qc" > "${BENCHMARKS_BASE}/synthesized_circuits/partition32/distributed_cnot_${CIRCUIT}.qc"

    # cabal run feynopt -- -purecircuit -inline -cnotmin -cxcz -simplify "benchmarks/qasm/${CIRCUIT}.qasm" > "/Users/duykhangnguyentruong/Development/pytket-dqc/examples/graysynth_qasm/${CIRCUIT}.qasm"

    # cabal run feynopt -- -purecircuit -inline -cnotmin -simplify "benchmarks/qasm/${CIRCUIT}.qasm" > "/Users/duykhangnguyentruong/Development/DISQCO/benchmarking/graysynth_qasm/${CIRCUIT}.qasm"

    # (Assuming your cabal run command redirects output to the customized file like this:)
    cabal run feynopt -- -inline -cnotmin -simplify -distribute 16 -simplify "benchmarks/qc/${CIRCUIT}.qc" > "benchmarks/qc_customized/distributed_cnot_${CIRCUIT}.qc"

    if [ $? -ne 0 ]; then
        echo "ERROR: cabal run failed for ${CIRCUIT}. Skipping copy step."
        continue
    fi

    TARGET_FILE="benchmarks/qc_customized/distributed_cnot_${CIRCUIT}.qc"

    # --- NEW VERIFICATION CHECK ---
    # Extract and print the verification status directly from the generated .qc file
    VERIFY_LINE=$(grep "# Distribution Verification:" "$TARGET_FILE")

    if [ -n "$VERIFY_LINE" ]; then
        # Print the exact line found in the file
        echo "$VERIFY_LINE"
        
        # Optional: You can also make the script halt if it fails
        if echo "$VERIFY_LINE" | grep -q "FAIL"; then
            echo "ERROR: Verification failed for ${CIRCUIT}. Halting."
            continue
        fi
    else
        echo "WARNING: Distribution Verification status not found in the output."
    fi
    # ------------------------------

    # Run feynver
    cabal run feynver -- -channel "benchmarks/qc/${CIRCUIT}.qc" "$TARGET_FILE"

    # # Destination directory for this circuit
    # DEST_DIR="${BENCHMARKS_BASE}/${CIRCUIT}/cnot_edgeweighted_hyp"

    # # Create destination directory if it doesn't exist
    # mkdir -p "${DEST_DIR}"

    # # Copy hypergraph files
    # echo "Copying hypergraph.hgr and partition.hgr to ${DEST_DIR}"
    # cp "${HYPERGRAPH_SRC_DIR}/hypergraph.hgr" "${HYPERGRAPH_SRC_DIR}/partition.hgr" "${DEST_DIR}/"

    # cp "${HYPERGRAPH_SRC_DIR}/partition.hgr" "/Users/duykhangnguyentruong/Development/pytket-dqc/examples/partitions/${CIRCUIT}.hgr"

    # if [ $? -eq 0 ]; then
    #     echo "Successfully copied files for ${CIRCUIT}"
    # else
    #     echo "ERROR: Failed to copy files for ${CIRCUIT}"
    # fi

    # echo ""
done

echo "============================================"
echo "All circuits processed."
echo "============================================"
