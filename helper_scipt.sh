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
    grover_5
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
    # qcla_com_7
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
BENCHMARKS_BASE="/Users/duykhangnguyentruong/Development/benchmarks"

for CIRCUIT in "${CIRCUITS[@]}"; do
    echo "============================================"
    echo "Processing circuit: ${CIRCUIT}"
    echo "============================================"

    # Run feynopt
    cabal run feynopt -- -inline -cnotmin -simplify -distribute "benchmarks/qc/${CIRCUIT}.qc" > "benchmarks/qc_customized/distributed_cnot_${CIRCUIT}.qc"

    # cabal run feynopt -- -inline -phasefold -simplify -cxcz -distribute "benchmarks/qc/${CIRCUIT}.qc"

    if [ $? -ne 0 ]; then
        echo "ERROR: cabal run failed for ${CIRCUIT}. Skipping copy step."
        continue
    fi

    # # Run feynver
    cabal run feynver -- -channel "benchmarks/qc/${CIRCUIT}.qc" "benchmarks/qc_customized/distributed_cnot_${CIRCUIT}.qc"

    # # Destination directory for this circuit
    # DEST_DIR="${BENCHMARKS_BASE}/${CIRCUIT}/cnot_edgeweighted_hyp"

    # # Create destination directory if it doesn't exist
    # mkdir -p "${DEST_DIR}"

    # # Copy hypergraph files
    # echo "Copying hypergraph.hgr and partition.hgr to ${DEST_DIR}"
    # cp "${HYPERGRAPH_SRC_DIR}/hypergraph.hgr" "${HYPERGRAPH_SRC_DIR}/partition.hgr" "${DEST_DIR}/"

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
