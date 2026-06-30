# Hyperedge cut (ebits): 8

# Actual ebits used (Synthesis): 8
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^4_mult.qc):
#   Qubits: 12
#   H: 14
#   T: 112
#   cnot: 99
#   Depth: 85
#   T depth: 41
# Result (18.766ms):
#   Qubits: 28
#   H: 30
#   S: 2
#   T: 68
#   Z: 3
#   cnot: 130
#   cz: 8
#   measure: 16
#   reset: 16
#   Depth: 125
#   T depth: 39


# Result Circuit
.v a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i a0 a1 a2 a3 b0 b1 b2 b3
.o a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
BEGIN 
H c0
H c1
H c2
T* c0
Z c0
H bell0
cnot bell0 bell1
cnot a3 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
H bell2
cnot bell2 bell3
cnot b1 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
T c0
cnot bell0 c0
T* c0
H bell4
cnot bell4 bell5
cnot a2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
cnot bell2 c0
T* c0
H bell6
cnot bell6 bell7
cnot b2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
T c0
cnot bell4 c0
T* c0
cnot a1 c0
cnot bell6 c0
T* c0
H bell8
cnot bell8 bell9
cnot b3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
T c0
cnot a1 c0
T* c0
cnot bell8 c0
H c0
S* c1
cnot bell0 c1
T c1
cnot bell6 c1
T* c1
cnot bell0 c1
T c1
cnot bell4 c1
cnot bell6 c1
T c1
cnot bell8 c1
T* c1
cnot bell4 c1
T c1
cnot bell8 c1
H c1
T c2
cnot bell0 c2
T* c2
cnot bell8 c2
T c2
cnot bell0 c2
T* c2
cnot bell8 c2
H c2
cnot c2 c3
cnot c1 c2
cnot c0 c1
H c0
H c1
H c2
H c3
T c0
cnot a0 c0
T* c0
H bell10
cnot bell10 bell11
cnot b0 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
T c0
cnot a0 c0
T* c0
cnot bell10 c0
H c0
S* c1
cnot a1 c1
T c1
cnot bell10 c1
T* c1
cnot a1 c1
T c1
cnot a0 c1
cnot bell10 c1
T c1
cnot bell2 c1
T* c1
cnot a0 c1
T c1
cnot bell2 c1
H c1
T* c2
Z c2
cnot bell4 c2
T* c2
cnot bell10 c2
T c2
cnot bell4 c2
T* c2
cnot a1 c2
cnot bell10 c2
T* c2
cnot bell2 c2
T c2
cnot a1 c2
T* c2
cnot a0 c2
cnot bell2 c2
T* c2
cnot bell6 c2
T c2
cnot a0 c2
T* c2
cnot bell6 c2
H c2
Z c3
cnot bell0 c3
T c3
cnot bell10 c3
T* c3
cnot bell0 c3
H bell0
measure bell0
cz bell0 a3
T c3
cnot bell4 c3
cnot bell10 c3
H bell10
measure bell10
cz bell10 b0
T c3
cnot bell2 c3
T* c3
cnot bell4 c3
H bell4
measure bell4
cz bell4 a2
T c3
cnot a1 c3
cnot bell2 c3
H bell2
measure bell2
cz bell2 b1
T c3
cnot bell6 c3
T* c3
cnot a1 c3
T c3
cnot a0 c3
cnot bell6 c3
H bell6
measure bell6
cz bell6 b2
T c3
cnot bell8 c3
T* c3
cnot a0 c3
T c3
cnot bell8 c3
H bell8
measure bell8
cz bell8 b3
H c3
H bell12
cnot bell12 bell13
cnot a0 bell13
measure bell13
cnot bell13 bell12
cnot bell12 b0
T* b0
H bell14
cnot bell14 bell15
cnot a1 bell15
measure bell15
cnot bell15 bell14
cnot bell14 b0
cnot bell12 b0
T b0
cnot bell12 b1
T b1
cnot bell14 b1
cnot bell12 b1
T* b1
cnot b0 a2
cnot bell14 a2
T* a2
cnot b1 a2
cnot b0 a2
T a2
cnot bell12 b2
T* b2
cnot bell14 b2
cnot bell12 b2
T b2
cnot b1 b2
cnot a2 b2
T* b2
cnot b0 a3
cnot bell14 a3
T a3
cnot b1 a3
cnot b0 a3
T* a3
cnot b2 a3
cnot a2 a3
T a3
cnot bell12 b3
T b3
cnot bell14 b3
cnot bell12 b3
H bell12
measure bell12
cz bell12 a0
T* b3
cnot b1 b3
cnot a2 b3
T b3
cnot b2 b3
cnot a3 b3
T* b3
cnot b1 a2
cnot b2 a3
cnot a2 a3
cnot a3 b3
cnot a2 b2
cnot bell14 b3
cnot bell14 b2
cnot bell14 b1
cnot bell14 b0
cnot bell14 a3
cnot bell14 a2
H bell14
measure bell14
cz bell14 a1
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
END
