# Hyperedge cut (ebits): 14

# Actual ebits used (Synthesis): 14
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^7_mult.qc):
#   Qubits: 21
#   H: 26
#   T: 343
#   cnot: 300
#   Depth: 166
#   T depth: 80
# Result (35.776ms):
#   Qubits: 49
#   H: 54
#   S: 4
#   T: 217
#   Z: 6
#   cnot: 361
#   cz: 14
#   measure: 28
#   reset: 28
#   Depth: 230
#   T depth: 75


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6
.o a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6
BEGIN 
H c0
H c1
H c2
H c3
H c4
H c5
S* c0
H bell0
cnot bell0 bell1
cnot a6 bell1
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
cnot a5 bell3
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
cnot a4 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
cnot bell4 c0
T* c0
H bell8
cnot bell8 bell9
cnot b3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
T c0
cnot bell6 c0
T* c0
H bell10
cnot bell10 bell11
cnot a3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
cnot bell8 c0
T* c0
H bell12
cnot bell12 bell13
cnot b4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
T c0
cnot bell10 c0
T* c0
H bell14
cnot bell14 bell15
cnot a2 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
cnot bell12 c0
T* c0
H bell16
cnot bell16 bell17
cnot b5 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
T c0
cnot bell14 c0
T* c0
cnot a1 c0
cnot bell16 c0
T* c0
H bell18
cnot bell18 bell19
cnot b6 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c0
T c0
cnot a1 c0
T* c0
cnot bell18 c0
H c0
T c1
Z c1
cnot bell0 c1
T* c1
cnot bell4 c1
T c1
cnot bell0 c1
T* c1
cnot bell2 c1
cnot bell4 c1
T* c1
cnot bell8 c1
T c1
cnot bell2 c1
T* c1
cnot bell6 c1
cnot bell8 c1
T* c1
cnot bell12 c1
T c1
cnot bell6 c1
T* c1
cnot bell10 c1
cnot bell12 c1
T* c1
cnot bell16 c1
T c1
cnot bell10 c1
T* c1
cnot bell14 c1
cnot bell16 c1
T* c1
cnot bell18 c1
T c1
cnot bell14 c1
T* c1
cnot bell18 c1
H c1
Z c2
cnot bell0 c2
T* c2
cnot bell8 c2
T c2
cnot bell0 c2
T* c2
cnot bell2 c2
cnot bell8 c2
T* c2
cnot bell12 c2
T c2
cnot bell2 c2
T* c2
cnot bell6 c2
cnot bell12 c2
T* c2
cnot bell16 c2
T c2
cnot bell6 c2
T* c2
cnot bell10 c2
cnot bell16 c2
T* c2
cnot bell18 c2
T c2
cnot bell10 c2
T* c2
cnot bell18 c2
H c2
T* c3
Z c3
cnot bell0 c3
T* c3
cnot bell12 c3
T c3
cnot bell0 c3
T* c3
cnot bell2 c3
cnot bell12 c3
T* c3
cnot bell16 c3
T c3
cnot bell2 c3
T* c3
cnot bell6 c3
cnot bell16 c3
T* c3
cnot bell18 c3
T c3
cnot bell6 c3
T* c3
cnot bell18 c3
H c3
S c4
cnot bell0 c4
T* c4
cnot bell16 c4
T c4
cnot bell0 c4
T* c4
cnot bell2 c4
cnot bell16 c4
T* c4
cnot bell18 c4
T c4
cnot bell2 c4
T* c4
cnot bell18 c4
H c4
T c5
cnot bell0 c5
T* c5
cnot bell18 c5
T c5
cnot bell0 c5
T* c5
cnot bell18 c5
H c5
cnot c5 c6
cnot c4 c5
cnot c3 c4
cnot c2 c3
cnot c1 c2
cnot c0 c1
H c0
H c1
H c2
H c3
H c4
H c5
H c6
T c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T* c0
cnot b0 c0
H c0
S c1
cnot a1 c1
T* c1
cnot b0 c1
T c1
cnot a1 c1
T* c1
cnot a0 c1
cnot b0 c1
T* c1
cnot b1 c1
T c1
cnot a0 c1
T* c1
cnot b1 c1
H c1
T* c2
Z c2
cnot bell14 c2
T* c2
cnot b0 c2
T c2
cnot bell14 c2
T* c2
cnot a1 c2
cnot b0 c2
T* c2
cnot b1 c2
T c2
cnot a1 c2
T* c2
cnot a0 c2
cnot b1 c2
T* c2
cnot bell4 c2
T c2
cnot a0 c2
T* c2
cnot bell4 c2
H c2
Z c3
cnot bell10 c3
T* c3
cnot b0 c3
T c3
cnot bell10 c3
T* c3
cnot bell14 c3
cnot b0 c3
T* c3
cnot b1 c3
T c3
cnot bell14 c3
T* c3
cnot a1 c3
cnot b1 c3
T* c3
cnot bell4 c3
T c3
cnot a1 c3
T* c3
cnot a0 c3
cnot bell4 c3
T* c3
cnot bell8 c3
T c3
cnot a0 c3
T* c3
cnot bell8 c3
H c3
T c4
Z c4
cnot bell6 c4
T* c4
cnot b0 c4
T c4
cnot bell6 c4
T* c4
cnot bell10 c4
cnot b0 c4
T* c4
cnot b1 c4
T c4
cnot bell10 c4
T* c4
cnot bell14 c4
cnot b1 c4
T* c4
cnot bell4 c4
T c4
cnot bell14 c4
T* c4
cnot a1 c4
cnot bell4 c4
T* c4
cnot bell8 c4
T c4
cnot a1 c4
T* c4
cnot a0 c4
cnot bell8 c4
T* c4
cnot bell12 c4
T c4
cnot a0 c4
T* c4
cnot bell12 c4
H c4
S* c5
cnot bell2 c5
T* c5
cnot b0 c5
T c5
cnot bell2 c5
T* c5
cnot bell6 c5
cnot b0 c5
T* c5
cnot b1 c5
T c5
cnot bell6 c5
T* c5
cnot bell10 c5
cnot b1 c5
T* c5
cnot bell4 c5
T c5
cnot bell10 c5
T* c5
cnot bell14 c5
cnot bell4 c5
T* c5
cnot bell8 c5
T c5
cnot bell14 c5
T* c5
cnot a1 c5
cnot bell8 c5
T* c5
cnot bell12 c5
T c5
cnot a1 c5
T* c5
cnot a0 c5
cnot bell12 c5
T* c5
cnot bell16 c5
T c5
cnot a0 c5
T* c5
cnot bell16 c5
H c5
T* c6
cnot bell0 c6
T* c6
cnot b0 c6
T c6
cnot bell0 c6
H bell0
measure bell0
cz bell0 a6
T* c6
cnot bell2 c6
cnot b0 c6
T* c6
cnot b1 c6
T c6
cnot bell2 c6
H bell2
measure bell2
cz bell2 a5
T* c6
cnot bell6 c6
cnot b1 c6
T* c6
cnot bell4 c6
T c6
cnot bell6 c6
H bell6
measure bell6
cz bell6 a4
T* c6
cnot bell10 c6
cnot bell4 c6
H bell4
measure bell4
cz bell4 b2
T* c6
cnot bell8 c6
T c6
cnot bell10 c6
H bell10
measure bell10
cz bell10 a3
T* c6
cnot bell14 c6
cnot bell8 c6
H bell8
measure bell8
cz bell8 b3
T* c6
cnot bell12 c6
T c6
cnot bell14 c6
H bell14
measure bell14
cz bell14 a2
T* c6
cnot a1 c6
cnot bell12 c6
H bell12
measure bell12
cz bell12 b4
T* c6
cnot bell16 c6
T c6
cnot a1 c6
T* c6
cnot a0 c6
cnot bell16 c6
H bell16
measure bell16
cz bell16 b5
T* c6
cnot bell18 c6
T c6
cnot a0 c6
T* c6
cnot bell18 c6
H bell18
measure bell18
cz bell18 b6
H c6
T* a0
T* a1
T* b0
cnot a0 b0
T* b0
cnot a1 b0
cnot a0 b0
T* b0
T* b1
cnot a0 b1
T* b1
cnot a1 b1
cnot a0 b1
T* b1
T* a2
H bell20
cnot bell20 bell21
cnot b0 bell21
measure bell21
cnot bell21 bell20
cnot bell20 a2
H bell22
cnot bell22 bell23
cnot a1 bell23
measure bell23
cnot bell23 bell22
cnot bell22 a2
T* a2
H bell24
cnot bell24 bell25
cnot b1 bell25
measure bell25
cnot bell25 bell24
cnot bell24 a2
cnot bell20 a2
T* a2
T* b2
H bell26
cnot bell26 bell27
cnot a0 bell27
measure bell27
cnot bell27 bell26
cnot bell26 b2
T* b2
cnot bell22 b2
cnot bell26 b2
T* b2
cnot bell24 b2
cnot a2 b2
T* b2
T* a3
cnot bell20 a3
cnot bell22 a3
T* a3
cnot bell24 a3
cnot bell20 a3
T* a3
cnot b2 a3
cnot a2 a3
T* a3
T* b3
cnot bell26 b3
T* b3
cnot bell22 b3
cnot bell26 b3
T* b3
cnot bell24 b3
cnot a2 b3
T* b3
cnot b2 b3
cnot a3 b3
T* b3
T* a4
cnot bell20 a4
cnot bell22 a4
T* a4
cnot bell24 a4
cnot bell20 a4
T* a4
cnot b2 a4
cnot a2 a4
T* a4
cnot b3 a4
cnot a3 a4
T* a4
T* b4
cnot bell26 b4
T* b4
cnot bell22 b4
cnot bell26 b4
T* b4
cnot bell24 b4
cnot a2 b4
T* b4
cnot b2 b4
cnot a3 b4
T* b4
cnot b3 b4
cnot a4 b4
T* b4
T* a5
cnot bell20 a5
cnot bell22 a5
T* a5
cnot bell24 a5
cnot bell20 a5
T* a5
cnot b2 a5
cnot a2 a5
T* a5
cnot b3 a5
cnot a3 a5
T* a5
cnot b4 a5
cnot a4 a5
T* a5
T* b5
cnot bell26 b5
T* b5
cnot bell22 b5
cnot bell26 b5
T* b5
cnot bell24 b5
cnot a2 b5
T* b5
cnot b2 b5
cnot a3 b5
T* b5
cnot b3 b5
cnot a4 b5
T* b5
cnot b4 b5
cnot a5 b5
T* b5
T* a6
cnot bell20 a6
cnot bell22 a6
T* a6
cnot bell24 a6
cnot bell20 a6
H bell20
measure bell20
cz bell20 b0
T* a6
cnot b2 a6
cnot a2 a6
T* a6
cnot b3 a6
cnot a3 a6
T* a6
cnot b4 a6
cnot a4 a6
T* a6
cnot b5 a6
cnot a5 a6
T* a6
T* b6
cnot bell26 b6
T* b6
cnot bell22 b6
cnot bell26 b6
H bell26
measure bell26
cz bell26 a0
T* b6
cnot bell24 b6
cnot a2 b6
T* b6
cnot b2 b6
cnot a3 b6
T* b6
cnot b3 b6
cnot a4 b6
T* b6
cnot b4 b6
cnot a5 b6
T* b6
cnot b5 b6
cnot a6 b6
T* b6
cnot bell24 a2
H bell24
measure bell24
cz bell24 b1
cnot b2 a3
cnot b3 a4
cnot b4 a5
cnot b5 a6
cnot a6 b6
cnot a4 a5
cnot a3 a5
cnot a3 a4
cnot a5 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a5 a6
cnot bell22 a2
H bell22
measure bell22
cz bell22 a1
cnot a2 b6
cnot a2 b5
cnot a2 b4
cnot a2 b3
cnot a2 b2
cnot a1 b1
cnot a1 b0
cnot a2 a6
cnot a2 a5
cnot a2 a4
cnot a2 a3
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
reset bell20
reset bell21
reset bell22
reset bell23
reset bell24
reset bell25
reset bell26
reset bell27
END
