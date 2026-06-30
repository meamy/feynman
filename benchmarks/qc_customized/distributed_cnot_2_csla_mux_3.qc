# Hyperedge cut (ebits): 14

# Actual ebits used (Synthesis): 14
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/csla_mux_3.qc):
#   Qubits: 15
#   H: 20
#   T: 70
#   cnot: 80
#   Depth: 58
#   T depth: 26
# Result (18.838ms):
#   Qubits: 43
#   H: 48
#   T: 62
#   cnot: 158
#   cz: 14
#   measure: 28
#   reset: 28
#   swap: 7
#   Depth: 128
#   T depth: 29


# Result Circuit
.v cin a0 b0 c0 d0 a1 b1 c1 d1 e1 a2 b2 c2 d2 e2 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i cin a0 b0 a1 b1 a2 b2
.o cin a0 b0 c0 d0 a1 b1 c1 d1 e1 a2 b2 c2 d2 e2
BEGIN 
H c0
H c1
H c2
T c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T* c0
cnot b0 c0
H c0
T c1
H bell0
cnot bell0 bell1
cnot a1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c1
T* c1
H bell2
cnot bell2 bell3
cnot b1 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c1
T c1
cnot bell0 c1
T* c1
cnot bell2 c1
H bell2
measure bell2
cz bell2 b1
H c1
T c2
cnot a2 c2
T* c2
cnot b2 c2
T c2
cnot a2 c2
T* c2
cnot b2 c2
H c2
cnot c2 e2
H bell4
cnot bell4 bell5
cnot c1 bell5
measure bell5
cnot bell5 bell4
cnot bell4 e1
H bell4
measure bell4
cz bell4 c1
cnot c0 d0
cnot a2 b2
cnot a1 b1
cnot a0 b0
H c1
H e1
H c2
H e2
T e1
cnot b1 e1
T* e1
cnot c0 e1
T e1
cnot b1 e1
T* e1
swap d0 d2
cnot c0 e1
H bell6
cnot bell6 bell7
cnot c0 bell7
measure bell7
cnot bell7 bell6
cnot bell6 d2
H bell6
measure bell6
cz bell6 c0
cnot c0 d0
cnot d2 b2
cnot b2 d2
cnot b0 c0
H e1
T* c1
H bell8
cnot bell8 bell9
cnot b1 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c1
T c1
H bell10
cnot bell10 bell11
cnot c0 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c1
T* c1
cnot bell8 c1
H bell8
measure bell8
cz bell8 b1
T c1
cnot bell10 c1
H c1
T c2
cnot b2 c2
T* c2
cnot c1 c2
T c2
cnot b2 c2
T* c2
cnot c0 b1
cnot d2 b2
cnot d1 c1
cnot d1 c2
cnot d2 d1
H bell12
cnot bell12 bell13
cnot e1 bell13
measure bell13
cnot bell13 bell12
cnot bell12 d2
cnot c1 d1
cnot c1 c2
swap b2 d1
H bell14
cnot bell14 bell15
cnot b1 bell15
measure bell15
cnot bell15 bell14
cnot bell14 d1
H bell14
measure bell14
cz bell14 b1
H bell16
cnot bell16 bell17
cnot b0 bell17
measure bell17
cnot bell17 bell16
cnot bell16 d1
H c2
T* e2
cnot c1 e2
cnot b2 e2
T e2
cnot d2 e2
T e2
cnot c1 e2
cnot b2 e2
T* e2
cnot d2 e2
H e2
cnot d2 b2
cnot bell12 c1
cnot e2 c2
cnot bell12 d1
H bell12
measure bell12
cz bell12 e1
swap d1 e1
swap c1 d1
cnot b2 d1
cnot b2 c1
cnot b1 e1
swap b1 d1
cnot b0 e1
cnot bell16 d1
cnot b0 b1
H e2
T d2
cnot b2 d2
T* d2
cnot c1 d2
T* d2
cnot a2 d2
T d2
cnot c1 d2
cnot b2 d2
cnot a2 d2
H d2
T* d1
cnot bell16 d1
T d1
cnot bell10 d1
T* d1
cnot bell0 d1
T d1
cnot bell10 d1
H bell10
measure bell10
cz bell10 c0
cnot bell16 d1
cnot bell0 d1
H bell0
measure bell0
cz bell0 a1
H d1
T e2
cnot c2 e2
T* e2
cnot cin e2
T e2
cnot c2 e2
T* e2
cnot cin e2
H e2
T* d2
cnot b2 d2
T d2
cnot cin d2
T* d2
cnot b2 d2
T d2
cnot cin d2
H d2
T d1
cnot bell16 d1
T* d1
cnot cin d1
T d1
cnot bell16 d1
H bell16
measure bell16
cz bell16 b0
T* d1
cnot cin d1
H d1
T a0
cnot a0 b0
T b0
T cin
H bell18
cnot bell18 bell19
cnot b0 bell19
measure bell19
cnot bell19 bell18
cnot bell18 cin
H bell20
cnot bell20 bell21
cnot a0 bell21
measure bell21
cnot bell21 bell20
cnot bell20 cin
T* cin
T* b2
cnot cin b2
cnot bell18 b2
cnot bell20 b2
T b2
T* c0
cnot b0 c0
cnot a0 c0
T c0
T c1
cnot cin c1
cnot b2 c1
cnot bell18 c1
cnot bell20 c1
T* c1
T c2
cnot cin c2
cnot bell18 c2
H bell18
measure bell18
cz bell18 b0
cnot bell20 c2
H bell20
measure bell20
cz bell20 a0
T* c2
T a1
T a2
H bell22
cnot bell22 bell23
cnot d1 bell23
measure bell23
cnot bell23 bell22
cnot bell22 a0
cnot b1 b0
cnot bell22 b1
cnot d2 b2
cnot bell22 c0
H bell22
measure bell22
cz bell22 d1
cnot d2 c1
cnot d1 cin
cnot e2 c2
cnot cin c2
cnot cin d1
cnot cin b2
H bell24
cnot bell24 bell25
cnot b1 bell25
measure bell25
cnot bell25 bell24
cnot bell24 b2
cnot bell24 cin
cnot bell24 c2
H bell24
measure bell24
cz bell24 b1
cnot b2 c1
cnot b1 c0
swap b0 d1
H bell26
cnot bell26 bell27
cnot d1 bell27
measure bell27
cnot bell27 bell26
cnot bell26 a0
H bell26
measure bell26
cz bell26 d1
swap a0 d1
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
