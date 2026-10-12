# 1-Qubit Non-Clifford (Clifford+T) Learning Benchmark
# Demonstrates Phase Folding: T*T = S, T*T* = I, and basis-separated T gates
.v q0
.i q0

BEGIN

# These two T gates fold into an S gate (T-count: 2 -> 0)
T q0
T q0

# Basis transformation
H q0

# These two T gates cancel out: T followed by T* (T-count: 2 -> 0)
T q0
T* q0

# Rotation in transformed basis
T q0

# Return to computational basis
H q0

# Final T rotation (cannot fold across H with previous T)
T q0

END
