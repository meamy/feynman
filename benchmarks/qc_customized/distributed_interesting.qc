# Hyperedge cut (ebits): 3

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/interesting.qc):
#   Qubits: 4
#   H: 1
#   T: 1
#   cnot: 5
#   Depth: 4
#   T depth: 1
# Result (11.517ms):
#   Qubits: 10
#   H: 15
#   T: 1
#   cnot: 9
#   cz: 9
#   measure: 6
#   reset: 6
#   Depth: 19
#   T depth: 1


# Result Circuit
.v a b c d bell0 bell1 bell2 bell3 bell4 bell5
.i a b c d
.o a b c d
BEGIN 
H b
H bell0
cnot bell0 bell1
cnot c bell1
measure bell1
cnot bell1 bell0
cz bell0 b
H b
H d
cz bell0 d
H bell0
measure bell0
cz bell0 c
H bell2
cnot bell2 bell3
cnot a bell3
measure bell3
cnot bell3 bell2
cz bell2 d
H bell2
measure bell2
cz bell2 a
H d
H c
T b
H a
H bell4
cnot bell4 bell5
cnot c bell5
measure bell5
cnot bell5 bell4
cz bell4 a
H a
H b
cz bell4 b
H bell4
measure bell4
cz bell4 c
cz a b
H b
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
END
