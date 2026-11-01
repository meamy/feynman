# 1-Qubit Clifford Learning Benchmark
# Demonstrates 1-qubit Clifford algebra: H*Z*H = X, S*S = Z, S*S* = I
.v q0
.i q0

BEGIN

H q0
Z q0
H q0
S q0
S q0
S* q0
S q0

END
