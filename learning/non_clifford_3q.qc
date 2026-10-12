# 3-Qubit Non-Clifford (Clifford+T) Learning Benchmark
# Demonstrates 3-qubit Toffoli decomposition, CCZ, and T-count / T-depth reduction
.v q0 q1 q2
.i q0 q1 q2

BEGIN

H q0
H q1

# 3-qubit Toffoli gate (synthesizes to 7 T gates)
tof q0 q1 q2

# Phase rotation on target
T q2

# Controlled-Controlled-Z (CCZ) gate
Z q0 q1 q2

# Uncompute Toffoli
tof q0 q1 q2

END
