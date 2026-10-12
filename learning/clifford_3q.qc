# 3-Qubit Clifford Learning Benchmark
# Demonstrates 3-qubit GHZ state preparation, CNOT propagation, and stabilizer identities
.v q0 q1 q2
.i q0 q1 q2

BEGIN

# Prepare 3-qubit GHZ state (|000> + |111>) / sqrt(2)
H q0
tof q0 q1
tof q1 q2

# Clifford phase and control interactions
S q0
S q1
cz q0 q2
tof q0 q1

# Redundant Hadamard pair (H*H = I)
H q2
H q2

# Uncompute GHZ state
tof q1 q2
tof q0 q1
H q0

END
