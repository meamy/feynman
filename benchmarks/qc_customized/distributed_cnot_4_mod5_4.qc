# Hyperedge cut (ebits): 5

# Actual ebits used (Synthesis): 10
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
# Result (15.024ms):
#   Qubits: 25
#   H: 26
#   T: 16
#   X: 1
#   cnot: 58
#   cz: 10
#   measure: 20
#   reset: 20
#   Depth: 81
#   T depth: 15


# Result Circuit
.v b c d e a bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
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
H bell2
cnot bell2 bell3
cnot e bell3
measure bell3
cnot bell3 bell2
cnot bell2 a
T a
cnot bell0 a
H bell4
cnot bell4 bell5
cnot d bell5
measure bell5
cnot bell5 bell4
cnot bell4 a
T* a
cnot bell2 a
T a
cnot bell4 a
H a
cnot bell2 a
H bell2
measure bell2
cz bell2 e
H a
T a
H bell6
cnot bell6 bell7
cnot c bell7
measure bell7
cnot bell7 bell6
cnot bell6 a
T* a
cnot bell4 a
T a
cnot bell6 a
T* a
cnot bell4 a
H a
cnot bell4 a
H bell4
measure bell4
cz bell4 d
H a
T* a
cnot bell0 a
T a
cnot bell6 a
T* a
cnot bell0 a
H bell0
measure bell0
cz bell0 b
T a
cnot bell6 a
H bell6
measure bell6
cz bell6 c
H a
H bell8
cnot bell8 bell9
cnot b bell9
measure bell9
cnot bell9 bell8
cnot bell8 c
H bell8
measure bell8
cz bell8 b
T c
H bell10
cnot bell10 bell11
cnot c bell11
measure bell11
cnot bell11 bell10
cnot bell10 d
H bell12
cnot bell12 bell13
cnot b bell13
measure bell13
cnot bell13 bell12
cnot bell12 d
T* d
cnot bell12 e
T* e
cnot d e
cnot bell10 e
H bell10
measure bell10
cz bell10 c
T e
H bell14
cnot bell14 bell15
cnot c bell15
measure bell15
cnot bell15 bell14
cnot bell14 a
H bell14
measure bell14
cz bell14 c
H bell16
cnot bell16 bell17
cnot c bell17
measure bell17
cnot bell17 bell16
cnot bell16 d
H bell16
measure bell16
cz bell16 c
cnot d e
cnot bell12 e
cnot bell12 d
H bell12
measure bell12
cz bell12 b
H bell18
cnot bell18 bell19
cnot b bell19
measure bell19
cnot bell19 bell18
cnot bell18 c
H bell18
measure bell18
cz bell18 b
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
reset bell6
reset bell7
reset bell8
reset bell9
reset bell10
reset bell11
reset bell12
reset bell13
reset bell14
reset bell15
reset bell16
reset bell17
reset bell18
reset bell19
END
