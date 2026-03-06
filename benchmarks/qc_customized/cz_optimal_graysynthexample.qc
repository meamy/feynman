# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/graysynthexample.qc):
#   Qubits: 4
#   T: 6
#   cnot: 9
#   Depth: 12
#   T depth: 5
# Result (2.245ms):
#   Qubits: 4
#   H: 14
#   T: 6
#   cz: 8
#   Depth: 22
#   T depth: 5


# Result Circuit
.v a b c d
.i a b c d
.o a b c d
BEGIN 
H c
cz b c
H c
T c
T a
H a
cz b a
H a
T a
H a
cz d a
H a
T a
H a
cz b a
H a
T a
H a
cz c a
cz d a
H a
T a
H a
cz b a
H a
H c
cz b c
H c
END
