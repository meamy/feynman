# 2-Qubit Clifford Learning Benchmark
# Demonstrates Bell state preparation, redundant CNOT cancellation, and Clifford normal forms
.v q0 q1
.i q0 q1

BEGIN

# Prepare Bell pair (|00> + |11>) / sqrt(2)
H q0
tof q0 q1

# Redundant CNOT pair (adjacent identical CNOTs cancel to Identity)
tof q0 q1
tof q0 q1

# Phase rotations in Clifford group
S q0
Z q1

# Entanglement basis change
tof q0 q1
H q0

END
