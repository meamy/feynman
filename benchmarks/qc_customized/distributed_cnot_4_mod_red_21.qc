# Hyperedge cut (ebits): 11

# Actual ebits used (Synthesis): 17
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_red_21.qc):
#   Qubits: 11
#   H: 30
#   T: 119
#   X: 24
#   cnot: 105
#   Depth: 141
#   T depth: 57
# Result (21.976ms):
#   Qubits: 45
#   H: 64
#   S: 1
#   T: 73
#   cnot: 151
#   cz: 17
#   measure: 34
#   reset: 34
#   Depth: 209
#   T depth: 59


# Result Circuit
.v x0 x1 c1 x2 c2 x3 c3 x4 c4 d4 z bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell4 bell5 bell6 bell7 bell8 bell9
.i x0 x1 x2 x3 x4 z
.o x0 x1 c1 x2 c2 x3 c3 x4 c4 d4 z
BEGIN 
H c2
T c2
H bell0
cnot bell0 bell1
cnot x1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c2
T* c2
cnot x2 c2
T c2
cnot bell0 c2
H bell0
measure bell0
cz bell0 x1
T* c2
cnot x2 c2
H c2
H c3
T c3
H bell2
cnot bell2 bell3
cnot c2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c3
T c3
H bell4
cnot bell4 bell5
cnot x3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c3
T c3
cnot bell2 c3
H bell2
measure bell2
cz bell2 c2
T c3
cnot bell4 c3
H bell4
measure bell4
cz bell4 x3
H c3
H d4
T d4
cnot c3 d4
T d4
cnot x4 d4
T* d4
cnot c3 d4
T* d4
cnot x4 d4
H d4
T* c3
cnot x4 c3
T c3
cnot x4 c3
H c3
H c4
T c4
H bell6
cnot bell6 bell7
cnot d4 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c4
T* c4
cnot z c4
T c4
cnot bell6 c4
T* c4
cnot z c4
H c4
H bell8
cnot bell8 bell9
cnot c3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c2
T* c2
cnot x3 c2
T* c2
cnot bell8 c2
H bell8
measure bell8
cz bell8 c3
cnot x3 c2
H c2
H c1
T c1
cnot x0 c1
H bell10
cnot bell10 bell11
cnot c4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c1
T* c1
cnot x1 c1
cnot bell10 c1
T c1
cnot x0 c1
cnot bell10 c1
H bell10
measure bell10
cz bell10 c4
T* c1
H bell12
cnot bell12 bell13
cnot c4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 x3
H bell12
measure bell12
cz bell12 c4
H bell14
cnot bell14 bell15
cnot c4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 x1
cnot bell14 x0
H bell14
measure bell14
cz bell14 c4
cnot x1 c1
H c1
H bell16
cnot bell16 bell17
cnot c1 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c2
T c2
cnot x2 c2
T* c2
cnot bell16 c2
H bell18
cnot bell18 bell19
cnot x1 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c2
H bell20
cnot bell20 bell21
cnot c4 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c2
T* c2
cnot x2 c2
T c2
cnot bell20 c2
H bell20
measure bell20
cz bell20 c4
cnot bell18 c2
H c2
H bell22
cnot bell22 bell23
cnot c2 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c3
T c3
H bell24
cnot bell24 bell25
cnot x3 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c3
T* c3
cnot bell22 c3
T* c3
H bell26
cnot bell26 bell27
cnot c4 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c3
T* c3
cnot bell24 c3
cnot bell26 c3
H c3
T x4
H x4
T x4
cnot c3 x4
T x4
cnot bell26 x4
T* x4
cnot c3 x4
T* x4
cnot bell26 x4
H x4
T* c3
cnot bell26 c3
T c3
cnot bell26 c3
H bell26
measure bell26
cz bell26 c4
H c3
T* c3
cnot bell22 c3
T* c3
cnot bell24 c3
T c3
cnot bell22 c3
H bell22
measure bell22
cz bell22 c2
T c3
cnot bell24 c3
H bell24
measure bell24
cz bell24 x3
H c3
cnot c2 x3
H bell28
cnot bell28 bell29
cnot c4 bell29
measure bell29
cnot bell29 bell28
cnot bell28 x3
cnot c2 x3
cnot bell28 x3
H x3
T* x3
cnot c2 x3
T x3
cnot bell28 x3
T* x3
cnot c2 x3
T x3
cnot bell28 x3
H x3
T* c2
cnot bell28 c2
T c2
cnot bell28 c2
H c2
T* c2
cnot bell16 c2
T* c2
cnot x2 c2
T c2
cnot bell16 c2
T c2
cnot x2 c2
H c2
cnot bell16 x2
cnot bell18 x2
cnot bell28 x2
cnot bell16 x2
cnot bell18 x2
H bell18
measure bell18
cz bell18 x1
cnot bell28 x2
H x2
T* x2
cnot bell16 x2
T* x2
cnot bell28 x2
T x2
cnot bell16 x2
H bell16
measure bell16
cz bell16 c1
T x2
cnot bell28 x2
H bell28
measure bell28
cz bell28 c4
H x2
T c1
H bell30
cnot bell30 bell31
cnot c4 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c1
T* c1
cnot bell30 c1
H c1
T* c1
cnot x0 c1
T c1
cnot x1 c1
T* c1
cnot x0 c1
T c1
cnot x1 c1
H c1
cnot bell30 x1
cnot x0 x1
cnot bell30 x1
cnot x0 x1
H x1
T* x1
cnot bell30 x1
T x1
cnot x0 x1
T x1
cnot bell30 x1
H bell30
measure bell30
cz bell30 c4
T* x1
cnot x0 x1
H x1
S* c4
H bell32
cnot bell32 bell33
cnot x0 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c4
T* c4
cnot bell32 c4
H bell32
measure bell32
cz bell32 x0
H c4
T* c4
cnot bell6 c4
T c4
cnot z c4
T* c4
cnot bell6 c4
H bell6
measure bell6
cz bell6 d4
T c4
cnot z c4
H c4
T x0
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
reset bell28
reset bell29
reset bell30
reset bell31
reset bell32
reset bell33
END
