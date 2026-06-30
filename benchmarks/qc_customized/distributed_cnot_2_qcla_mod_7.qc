# Hyperedge cut (ebits): 14

# Actual ebits used (Synthesis): 14
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/qcla_mod_7.qc):
#   Qubits: 26
#   H: 82
#   T: 413
#   X: 7
#   cnot: 382
#   Depth: 172
#   T depth: 77
# Result (121.960ms):
#   Qubits: 54
#   H: 110
#   S: 24
#   T: 237
#   X: 7
#   cnot: 420
#   cz: 14
#   measure: 28
#   reset: 28
#   Depth: 204
#   T depth: 64


# Result Circuit
.v e a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6
.o e a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6
BEGIN 
H e
H c0
H d0
H c1
H d1
H c2
H d2
H c3
H c4
H d4
H c5
H d5
T c0
cnot b0 c0
H bell0
cnot bell0 bell1
cnot a0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
cnot b1 c0
cnot a1 c0
T c0
cnot b0 c0
cnot bell0 c0
T* c0
cnot b1 c0
cnot a6 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a1 c0
cnot a2 b2
cnot a1 b1
cnot bell0 b0
H c0
T d0
cnot bell0 d0
T* d0
cnot b0 d0
T* d0
cnot bell0 d0
T d0
cnot b0 d0
H d0
T c2
cnot b2 c2
T* c2
cnot b3 c2
T c2
cnot b2 c2
T* c2
cnot b3 c2
H c2
T d2
cnot a2 d2
T* d2
cnot b2 d2
T* d2
cnot a2 d2
T d2
cnot b2 d2
H d2
T c4
cnot b4 c4
T* c4
cnot b5 c4
T c4
cnot b4 c4
T* c4
cnot b5 c4
H c4
T d4
cnot a4 d4
T* d4
cnot b4 d4
T* d4
cnot a4 d4
T d4
cnot b4 d4
H d4
T c1
cnot c0 c1
T* c1
cnot c2 c1
T c1
cnot c0 c1
T* c1
cnot c2 c1
H c1
S d1
cnot a1 d1
T* d1
cnot b1 d1
T* d1
cnot a1 d1
cnot d0 d1
T d1
cnot b1 d1
T* d1
cnot d0 d1
H d1
T c5
cnot b6 c5
T* c5
cnot c4 c5
T c5
cnot b6 c5
T* c5
cnot c4 c5
H c5
S d5
cnot a5 d5
T* d5
cnot b5 d5
T* d5
cnot a5 d5
cnot d4 d5
T d5
cnot b5 d5
T* d5
cnot d4 d5
H d5
T c3
H bell2
cnot bell2 bell3
cnot a3 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c3
T* c3
H bell4
cnot bell4 bell5
cnot b3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c3
T* c3
cnot bell2 c3
H bell6
cnot bell6 bell7
cnot c2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c3
cnot bell4 c3
T c3
H bell8
cnot bell8 bell9
cnot d1 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c3
T* c3
cnot bell6 c3
H bell6
measure bell6
cz bell6 c2
T c3
H bell10
cnot bell10 bell11
cnot d2 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c3
cnot bell8 c3
H bell8
measure bell8
cz bell8 d1
T* c3
cnot bell4 c3
T c3
cnot bell10 c3
H bell10
measure bell10
cz bell10 d2
cnot bell4 c3
H bell4
measure bell4
cz bell4 b3
H c3
S* e
cnot a6 e
T* e
cnot b6 e
T* e
cnot a6 e
S e
H bell12
cnot bell12 bell13
cnot c1 bell13
measure bell13
cnot bell13 bell12
cnot bell12 e
cnot b6 e
T e
cnot c5 e
T* e
cnot bell12 e
S e
cnot c3 e
T* e
cnot c5 e
T e
cnot d5 e
cnot c3 e
T e
cnot b6 e
T* e
cnot d5 e
cnot b6 e
H e
T* c3
cnot c5 c3
T c3
cnot c5 c3
H c3
T* c3
cnot bell12 c3
T c3
cnot e c3
T* c3
cnot bell12 c3
H bell12
measure bell12
cz bell12 c1
T c3
cnot e c3
H c3
T* d1
cnot c2 d1
T d1
cnot c2 d1
H d1
S* c1
H bell14
cnot bell14 bell15
cnot c5 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c1
T c1
H bell16
cnot bell16 bell17
cnot e bell17
measure bell17
cnot bell17 bell16
cnot bell16 c1
cnot bell14 c1
H bell14
measure bell14
cz bell14 c5
T c1
cnot bell16 c1
H c1
T d0
cnot b1 d0
T* d0
cnot b1 d0
H d0
T d4
cnot b5 d4
T* d4
cnot b5 d4
H d4
S* c5
H c5
T* d5
cnot b6 d5
T d5
cnot b6 d5
H d5
T* d0
cnot b0 d0
T d0
cnot bell16 d0
T* d0
cnot b0 d0
T d0
cnot bell16 d0
H d0
T* d1
cnot c0 d1
T d1
cnot bell16 d1
T* d1
cnot c0 d1
T d1
cnot bell16 d1
H d1
T* d4
cnot b4 d4
T d4
cnot c3 d4
T* d4
cnot b4 d4
T d4
cnot c3 d4
H d4
T* d5
cnot c3 d5
T d5
cnot c4 d5
T* d5
cnot c3 d5
T d5
cnot c4 d5
H d5
T* c0
cnot c1 c0
T c0
cnot c2 c0
T* c0
cnot c1 c0
cnot bell16 c0
cnot c2 c0
T c0
cnot bell16 c0
H c0
T* c2
cnot c1 c2
T c2
cnot c1 c2
H c2
T d2
cnot b3 d2
T* d2
cnot b3 d2
H d2
T* c4
cnot b6 c4
cnot c5 c4
T* c4
cnot b6 c4
T c4
cnot c3 c4
cnot c5 c4
T c4
cnot c3 c4
H c4
T* d2
cnot b2 d2
T d2
cnot d1 d2
T* d2
cnot b2 d2
T d2
cnot d1 d2
H d2
cnot b2 b3
cnot c2 b3
T* b3
cnot b2 b3
T b3
cnot a3 b3
cnot c2 b3
T b3
cnot d0 b1
cnot bell16 b0
cnot c3 b4
cnot d1 b2
cnot d2 b3
cnot d4 b5
cnot d5 b6
cnot a6 b6
cnot a5 b5
cnot a4 b4
cnot a2 b2
cnot a1 b1
cnot bell0 b0
H d2
cnot b0 c0
T c0
cnot b1 c0
T c0
cnot b0 c0
T c0
cnot d0 c0
cnot a1 c0
T c0
cnot bell16 c0
cnot b0 c0
cnot bell0 c0
T* c0
cnot d0 c0
cnot b1 c0
cnot a1 c0
T c0
cnot bell16 c0
cnot b0 c0
cnot bell0 c0
H c0
cnot b2 c2
T c2
cnot b3 c2
T c2
cnot b2 c2
T c2
cnot d1 c2
cnot b3 c2
cnot b2 c2
cnot a2 c2
T c2
cnot d1 c2
cnot b2 c2
cnot a2 c2
H c2
T d2
cnot b2 d2
T d2
cnot d1 d2
T* d2
cnot b2 d2
T* d2
cnot d1 d2
H d2
cnot b4 c4
T c4
cnot b5 c4
T c4
cnot b4 c4
T c4
cnot c3 c4
cnot b5 c4
cnot b4 c4
cnot a4 c4
T c4
cnot d4 c4
cnot b5 c4
cnot a5 c4
T* c4
cnot c3 c4
cnot b4 c4
cnot a4 c4
T c4
cnot d4 c4
cnot b5 c4
cnot a5 c4
H c4
cnot b1 d0
T d0
cnot a1 d0
cnot bell16 d0
cnot b0 d0
cnot bell0 d0
cnot bell16 d0
cnot b1 d0
cnot b0 d0
cnot a1 d0
cnot bell0 d0
H d0
cnot b2 d1
S d1
cnot a2 d1
S* d1
cnot b2 d1
cnot a2 d1
H d1
cnot b5 d4
T d4
cnot a5 d4
cnot c3 d4
cnot b4 d4
cnot a4 d4
cnot c3 d4
cnot b5 d4
cnot b4 d4
cnot a5 d4
cnot a4 d4
H d4
cnot b6 d5
T d5
cnot a6 d5
S* d5
cnot c5 d5
T d5
cnot c5 d5
cnot b6 d5
cnot a6 d5
H d5
T d1
cnot c0 d1
T* d1
cnot bell16 d1
T d1
cnot c0 d1
T* d1
cnot bell16 d1
H d1
cnot c0 c1
T* c1
cnot c2 c1
T c1
cnot c0 c1
T* c1
cnot c2 c1
H c1
T d0
cnot b0 d0
T d0
cnot bell16 d0
T* d0
cnot b0 d0
T* d0
cnot bell16 d0
H bell16
measure bell16
cz bell16 e
H d0
T d4
cnot b4 d4
T d4
cnot c3 d4
T* d4
cnot b4 d4
T* d4
cnot c3 d4
H d4
cnot b6 c5
T c5
cnot c4 c5
T* c5
cnot b6 c5
T* c5
cnot c4 c5
H c5
T d5
cnot c3 d5
T* d5
cnot c4 d5
T d5
cnot c3 d5
T* d5
cnot c4 d5
H d5
cnot b4 c3
S c3
cnot a4 c3
S* c3
cnot c4 c3
cnot b4 c3
cnot a4 c3
T* c3
cnot c4 c3
H c3
H bell18
cnot bell18 bell19
cnot c1 bell19
measure bell19
cnot bell19 bell18
cnot bell18 e
T* e
cnot c3 e
T e
cnot bell18 e
T* e
H bell20
cnot bell20 bell21
cnot b0 bell21
measure bell21
cnot bell21 bell20
cnot bell20 e
cnot c3 e
S e
cnot a0 e
S* e
H bell22
cnot bell22 bell23
cnot c0 bell23
measure bell23
cnot bell23 bell22
cnot bell22 e
cnot bell20 e
H bell20
measure bell20
cz bell20 b0
cnot a0 e
T* e
cnot bell22 e
H bell22
measure bell22
cz bell22 c0
H e
T c3
cnot bell18 c3
T* c3
cnot bell18 c3
H bell18
measure bell18
cz bell18 c1
H c3
T c3
cnot c5 c3
T* c3
cnot e c3
T c3
cnot c5 c3
T* c3
cnot e c3
H c3
T c1
H c1
T d1
cnot c2 d1
T* d1
H bell24
cnot bell24 bell25
cnot c3 bell25
measure bell25
cnot bell25 bell24
cnot bell24 d1
T d1
cnot c2 d1
T* d1
cnot bell24 d1
H d1
T c5
cnot e c5
T* c5
cnot e c5
H c5
T d5
cnot b6 d5
T d5
cnot e d5
T* d5
cnot b6 d5
T* d5
cnot e d5
H d5
T c0
cnot c1 c0
T c0
cnot c2 c0
T* c0
cnot c1 c0
cnot c2 c0
H c0
T* d0
cnot b1 d0
T* d0
cnot d1 d0
T d0
cnot b1 d0
T d0
cnot d1 d0
H d0
T c2
cnot c1 c2
T c2
cnot bell24 c2
cnot c1 c2
T* c2
cnot bell24 c2
H c2
T* d2
cnot b3 d2
T* d2
cnot bell24 d2
T d2
cnot b3 d2
T d2
cnot bell24 d2
H bell24
measure bell24
cz bell24 c3
H d2
T c4
cnot b6 c4
cnot c5 c4
T c4
cnot b6 c4
T c4
cnot c5 c4
H c4
T* d4
cnot b5 d4
T* d4
cnot d5 d4
T d4
cnot b5 d4
T d4
cnot d5 d4
H d4
T e
cnot a6 e
T e
cnot b6 e
T* e
cnot a6 e
S e
cnot b6 e
cnot a6 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a2 b2
cnot a1 b1
cnot bell0 b0
H e
T* c0
cnot b0 c0
cnot bell0 c0
T* c0
cnot b1 c0
cnot a1 c0
T* c0
cnot b0 c0
cnot bell0 c0
T* c0
cnot b1 c0
cnot a1 c0
H c0
T* d0
cnot bell0 d0
T d0
cnot b0 d0
T d0
cnot bell0 d0
T* d0
cnot b0 d0
H d0
T* c1
H c1
S* d1
cnot a1 d1
T d1
cnot b1 d1
cnot a1 d1
T* d1
cnot b1 d1
H d1
T* c2
cnot b2 c2
cnot a2 c2
T* c2
cnot b3 c2
cnot a3 c2
T* c2
cnot b2 c2
cnot a2 c2
T* c2
cnot b3 c2
cnot a3 c2
H c2
T* d2
cnot a2 d2
T d2
cnot b2 d2
T d2
cnot a2 d2
T* d2
cnot b2 d2
H d2
T* c3
cnot bell2 c3
T c3
H bell26
cnot bell26 bell27
cnot b3 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c3
cnot bell2 c3
H bell2
measure bell2
cz bell2 a3
T* c3
cnot bell26 c3
H bell26
measure bell26
cz bell26 b3
H c3
T* c4
cnot b4 c4
cnot a4 c4
T* c4
cnot b5 c4
cnot a5 c4
T* c4
cnot b4 c4
cnot a4 c4
T* c4
cnot b5 c4
cnot a5 c4
H c4
T* d4
cnot a4 d4
T d4
cnot b4 d4
T d4
cnot a4 d4
T* d4
cnot b4 d4
H d4
T* c5
cnot b6 c5
cnot a6 c5
T* c5
cnot b6 c5
cnot a6 c5
H c5
S* d5
cnot a5 d5
T d5
cnot b5 d5
cnot a5 d5
T* d5
cnot b5 d5
H d5
S b0
cnot bell0 b0
S* b0
T b1
S b2
cnot a2 b2
S* b2
T b3
S b4
cnot a4 b4
S* b4
T b5
T b6
cnot a6 b6
S* b6
cnot a6 b6
cnot a4 b4
cnot a2 b2
cnot bell0 b0
H bell0
measure bell0
cz bell0 a0
X b0
X b1
X b2
X b3
X b4
X b5
X b6
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
