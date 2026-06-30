# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/interesting.qc):
#   Qubits: 4
#   H: 1
#   T: 1
#   cnot: 5
#   Depth: 4
#   T depth: 1
# Result (1.942ms):
#   Qubits: 4
#   H: 9
#   T: 1
#   cz: 6
#   Depth: 9
#   T depth: 1


# Result Circuit
.v a b c d
.i a b c d
.o a b c d
BEGIN 
H b
cz c b
H b
H d
cz c d
cz a d
H d
H c
T b
H a
cz c a
H a
H b
cz c b
cz a b
H b
END
