# 2-Qubit Non-Clifford (Clifford+T) Learning Benchmark
# Demonstrates Phase Folding across CNOT gates (affine parity domain y0 ^ y1)
.v q0 q1
.i q0 q1

BEGIN

H q0

# Individual rotations
T q0
T q1

# Entangle: qubit q1 carries parity (q0 ^ q1)
tof q0 q1

# Phase rotation on joint parity (q0 ^ q1)
T q1

# Disentangle
tof q0 q1

# Conjugate parity again
tof q0 q1
T q1
tof q0 q1

# The two T gates on parity (q0 ^ q1) fold into a single S gate!

END
