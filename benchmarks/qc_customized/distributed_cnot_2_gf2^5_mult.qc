# Hyperedge cut (ebits): 10

# Actual ebits used (Synthesis): 10
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^5_mult.qc):
#   Qubits: 15
#   H: 18
#   T: 175
#   cnot: 154
#   Depth: 111
#   T depth: 54
# Result (19.492ms):
#   Qubits: 35
#   H: 38
#   T: 115
#   Z: 3
#   cnot: 196
#   cz: 10
#   measure: 20
#   reset: 20
#   Depth: 159
#   T depth: 51


# Result Circuit
.v a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
.o a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
BEGIN 
H c0
H c1
H c2
H c3
H bell0
cnot bell0 bell1
cnot a4 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
cnot b1 c0
T c0
cnot bell0 c0
T* c0
H bell2
cnot bell2 bell3
cnot a3 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
cnot b1 c0
T* c0
H bell4
cnot bell4 bell5
cnot b2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
T c0
cnot bell2 c0
T* c0
H bell6
cnot bell6 bell7
cnot a2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
cnot bell4 c0
T c0
H bell8
cnot bell8 bell9
cnot b3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
T* c0
cnot bell6 c0
T c0
cnot a1 c0
cnot bell8 c0
T c0
H bell10
cnot bell10 bell11
cnot b4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
T* c0
cnot a1 c0
T c0
cnot bell10 c0
H c0
T c1
cnot bell0 c1
T* c1
cnot bell4 c1
T c1
cnot bell0 c1
T* c1
cnot bell2 c1
cnot bell4 c1
T c1
cnot bell8 c1
T* c1
cnot bell2 c1
T c1
cnot bell6 c1
cnot bell8 c1
T* c1
cnot bell10 c1
T c1
cnot bell6 c1
T* c1
cnot bell10 c1
H c1
cnot bell0 c2
T* c2
cnot bell8 c2
T c2
cnot bell0 c2
T* c2
cnot bell2 c2
cnot bell8 c2
T c2
cnot bell10 c2
T* c2
cnot bell2 c2
T c2
cnot bell10 c2
H c2
T* c3
cnot bell0 c3
T c3
cnot bell10 c3
T* c3
cnot bell0 c3
T c3
cnot bell10 c3
H c3
cnot c3 c0
cnot c2 c4
cnot c1 c3
cnot c0 c2
H c0
H c1
H c2
H c3
H c4
T c0
cnot a0 c0
T* c0
H bell12
cnot bell12 bell13
cnot b0 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
T c0
cnot a0 c0
T* c0
cnot bell12 c0
H c0
cnot a1 c1
T* c1
cnot bell12 c1
T c1
cnot a1 c1
T* c1
cnot a0 c1
cnot bell12 c1
T c1
cnot b1 c1
T* c1
cnot a0 c1
T c1
cnot b1 c1
H c1
T c2
cnot bell6 c2
T* c2
cnot bell12 c2
T c2
cnot bell6 c2
T* c2
cnot a1 c2
cnot bell12 c2
T c2
cnot b1 c2
T* c2
cnot a1 c2
T c2
cnot a0 c2
cnot b1 c2
T* c2
cnot bell4 c2
T c2
cnot a0 c2
T* c2
cnot bell4 c2
H c2
cnot bell2 c3
T* c3
cnot bell12 c3
T c3
cnot bell2 c3
T* c3
cnot bell6 c3
cnot bell12 c3
T* c3
cnot b1 c3
T c3
cnot bell6 c3
T* c3
cnot a1 c3
cnot b1 c3
T c3
cnot bell4 c3
T* c3
cnot a1 c3
T c3
cnot a0 c3
cnot bell4 c3
T c3
cnot bell8 c3
T* c3
cnot a0 c3
T c3
cnot bell8 c3
H c3
T* c4
Z c4
cnot bell0 c4
T* c4
cnot bell12 c4
T c4
cnot bell0 c4
H bell0
measure bell0
cz bell0 a4
T* c4
cnot bell2 c4
cnot bell12 c4
H bell12
measure bell12
cz bell12 b0
T* c4
cnot b1 c4
T c4
cnot bell2 c4
H bell2
measure bell2
cz bell2 a3
T* c4
cnot bell6 c4
cnot b1 c4
T c4
cnot bell4 c4
T* c4
cnot bell6 c4
H bell6
measure bell6
cz bell6 a2
T c4
cnot a1 c4
cnot bell4 c4
H bell4
measure bell4
cz bell4 b2
T* c4
cnot bell8 c4
T c4
cnot a1 c4
T* c4
cnot a0 c4
cnot bell8 c4
H bell8
measure bell8
cz bell8 b3
T* c4
cnot bell10 c4
T c4
cnot a0 c4
T* c4
cnot bell10 c4
H bell10
measure bell10
cz bell10 b4
H c4
T a0
T* a1
T b0
Z b0
H bell14
cnot bell14 bell15
cnot a0 bell15
measure bell15
cnot bell15 bell14
cnot bell14 b0
T* b0
H bell16
cnot bell16 bell17
cnot a1 bell17
measure bell17
cnot bell17 bell16
cnot bell16 b0
cnot bell14 b0
T* b0
T b1
cnot a0 b1
T b1
cnot a1 b1
cnot a0 b1
T b1
T a2
cnot b0 a2
cnot bell16 a2
T* a2
H bell18
cnot bell18 bell19
cnot b1 bell19
measure bell19
cnot bell19 bell18
cnot bell18 a2
cnot b0 a2
T* a2
T b2
cnot bell14 b2
T* b2
cnot bell16 b2
cnot bell14 b2
T b2
cnot bell18 b2
cnot a2 b2
T b2
T a3
cnot b0 a3
cnot bell16 a3
T* a3
cnot bell18 a3
cnot b0 a3
T* a3
cnot b2 a3
cnot a2 a3
T* a3
T* b3
cnot bell14 b3
T b3
cnot bell16 b3
cnot bell14 b3
T* b3
cnot bell18 b3
cnot a2 b3
T b3
cnot b2 b3
cnot a3 b3
T b3
T* a4
Z a4
cnot b0 a4
cnot bell16 a4
T* a4
cnot bell18 a4
cnot b0 a4
T* a4
cnot b2 a4
cnot a2 a4
T* a4
cnot b3 a4
cnot a3 a4
T* a4
T* b4
cnot bell14 b4
T* b4
cnot bell16 b4
cnot bell14 b4
H bell14
measure bell14
cz bell14 a0
T b4
cnot bell18 b4
cnot a2 b4
T* b4
cnot b2 b4
cnot a3 b4
T b4
cnot b3 b4
cnot a4 b4
T b4
cnot bell18 a2
H bell18
measure bell18
cz bell18 b1
cnot b2 a3
cnot b3 a4
cnot a4 b4
cnot a2 a3
cnot a3 b4
cnot a3 b3
cnot a2 b2
cnot a3 a4
cnot bell16 b4
cnot bell16 b3
cnot bell16 b2
cnot a1 b1
cnot bell16 b0
cnot bell16 a4
cnot bell16 a3
cnot bell16 a2
H bell16
measure bell16
cz bell16 a1
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
