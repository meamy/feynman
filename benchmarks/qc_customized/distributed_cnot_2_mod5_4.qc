# Hyperedge cut (ebits): 3

# Actual ebits used (Synthesis): 3
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod5_4.qc):
#   Qubits: 5
#   H: 6
#   T: 28
#   X: 1
#   cnot: 28
#   Depth: 36
#   T depth: 13
# Result (11.665ms):
#   Qubits: 11
#   H: 12
#   T: 16
#   X: 1
#   cnot: 37
#   cz: 3
#   measure: 6
#   reset: 6
#   Depth: 60
#   T depth: 15


# Result Circuit
.v b c d e a bell0 bell1 bell2 bell3 bell4 bell5
.i b c d e
.o b c d e a
BEGIN 
X a
H a
H bell0
cnot bell0 bell1
cnot b bell1
measure bell1
cnot bell1 bell0
cnot bell0 a
T* a
cnot e a
T a
cnot bell0 a
cnot d a
T* a
cnot e a
T a
cnot d a
H a
cnot e a
H a
T a
H bell2
cnot bell2 bell3
cnot c bell3
measure bell3
cnot bell3 bell2
cnot bell2 a
T* a
cnot d a
T a
cnot bell2 a
T* a
cnot d a
H a
cnot d a
H a
T* a
cnot bell0 a
T a
cnot bell2 a
T* a
cnot bell0 a
T a
cnot bell2 a
H bell2
measure bell2
cz bell2 c
H a
cnot b c
T c
H bell4
cnot bell4 bell5
cnot c bell5
measure bell5
cnot bell5 bell4
cnot bell4 d
cnot bell0 d
T* d
cnot bell0 e
T* e
cnot d e
cnot bell4 e
T e
cnot bell4 a
cnot bell4 d
H bell4
measure bell4
cz bell4 c
cnot d e
cnot bell0 e
cnot bell0 d
H bell0
measure bell0
cz bell0 b
cnot b c
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
END
