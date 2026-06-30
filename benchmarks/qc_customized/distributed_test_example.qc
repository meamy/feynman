
# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/test_example.qc):
#   Qubits: 3
#   cnot: 2
#   Depth: 2
#   T depth: 0
# Result (1.991ms):
#   Qubits: 3
#   cnot: 3
#   Depth: 3
#   T depth: 0


# Result Circuit
.v a b c
.i a b c
.o a b c
BEGIN 
cnot b c
cnot a b
cnot b c
END
