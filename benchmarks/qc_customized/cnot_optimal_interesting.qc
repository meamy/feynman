# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/interesting.qc):
#   Qubits: 4
#   H: 1
#   T: 1
#   cnot: 5
#   Depth: 4
#   T depth: 1
# Result (1.166ms):
#   Qubits: 4
#   H: 1
#   T: 1
#   cnot: 6
#   Depth: 6
#   T depth: 1


# Result Circuit
.v a b c d
.i a b c d
.o a b c d
BEGIN 
cnot c b
cnot c d
cnot a d
H c
T b
cnot c a
cnot c b
cnot a b
END
