# Hyperedge cut (ebits): 2

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/graysynthexample.qc):
#   Qubits: 4
#   T: 6
#   cnot: 9
#   Depth: 12
#   T depth: 5
# Result (11.046ms):
#   Qubits: 8
#   H: 18
#   T: 6
#   cnot: 6
#   cz: 10
#   measure: 4
#   reset: 4
#   Depth: 27
#   T depth: 5


# Result Circuit
.v a b c d bell0 bell1 bell2 bell3
.i a b c d
.o a b c d
BEGIN 
H c
cz b c
H c
T c
T a
H a
H bell0
cnot bell0 bell1
cnot b bell1
measure bell1
cnot bell1 bell0
cz bell0 a
H a
T a
H a
cz d a
H a
T a
H a
cz bell0 a
H a
T a
H a
H bell2
cnot bell2 bell3
cnot c bell3
measure bell3
cnot bell3 bell2
cz bell2 a
H bell2
measure bell2
cz bell2 c
cz d a
H a
T a
H a
cz bell0 a
H a
H c
cz b c
H bell0
measure bell0
cz bell0 b
H c
reset bell0
reset bell1
reset bell2
reset bell3
END
