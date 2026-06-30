# Hyperedge cut (ebits): 11

# Actual ebits used (Synthesis): 11
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/adder_8.qc):
#   Qubits: 24
#   H: 80
#   T: 399
#   X: 12
#   cnot: 409
#   Depth: 191
#   T depth: 82
# Result (102.501ms):
#   Qubits: 46
#   H: 102
#   S: 44
#   T: 215
#   Z: 23
#   cnot: 432
#   cz: 11
#   measure: 22
#   reset: 22
#   Depth: 251
#   T depth: 74


# Result Circuit
.v b0 a0 b1 a1 c1 b2 a2 b3 a3 c3 d3 b4 a4 b5 a5 c5 d5 e5 b6 a6 b7 a7 z c7 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i b0 a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 b6 a6 b7 a7 z
.o b0 a0 b1 a1 c1 b2 a2 b3 a3 c3 d3 b4 a4 b5 a5 c5 d5 e5 b6 a6 b7 a7 z c7
BEGIN 
cnot a7 z
cnot a7 b7
cnot a5 c5
cnot a3 c3
cnot a5 b5
cnot a3 b3
cnot a1 c1
cnot a1 b1
H a1
H a3
H a5
H a7
T a1
cnot a0 a1
T* a1
cnot b0 a1
T a1
cnot a0 a1
T* a1
cnot b0 a1
H a1
T a3
cnot a2 a3
T* a3
cnot b2 a3
T a3
cnot a2 a3
T* a3
cnot b2 a3
H a3
T a5
H bell0
cnot bell0 bell1
cnot a4 bell1
measure bell1
cnot bell1 bell0
cnot bell0 a5
T* a5
cnot b4 a5
T a5
cnot bell0 a5
T* a5
cnot b4 a5
H a5
T a7
cnot a6 a7
T* a7
cnot b6 a7
T a7
cnot a6 a7
T* a7
cnot b6 a7
H a7
H c1
H c3
H c5
H z
H d3
H d5
H c7
T c1
cnot a1 c1
T* c1
cnot b1 c1
T c1
cnot a1 c1
T* c1
cnot b2 a3
cnot b4 a5
cnot b6 a7
cnot b1 c1
cnot a6 a7
cnot a6 b6
cnot bell0 a5
cnot bell0 b4
cnot a2 b2
cnot a2 a3
H c1
S d3
cnot a3 d3
T* d3
cnot b3 d3
T d3
cnot a3 d3
S* d3
cnot b2 d3
cnot a3 d3
T d3
cnot b3 d3
T* d3
cnot b2 d3
cnot a3 d3
H d3
T c5
cnot b4 c5
cnot a5 c5
T* c5
cnot b5 c5
T c5
cnot b4 c5
cnot a5 c5
T* c5
cnot b5 c5
H c5
S d5
cnot a5 d5
T* d5
cnot b5 d5
T d5
cnot a5 d5
S* d5
cnot b4 d5
cnot a5 d5
T d5
cnot b5 d5
T* d5
cnot b4 d5
cnot a5 d5
H d5
S c7
cnot a7 c7
T* c7
cnot b7 c7
T c7
cnot a7 c7
S* c7
cnot b6 c7
cnot a7 c7
T c7
cnot b7 c7
T* c7
cnot b6 c7
cnot a7 c7
H c7
H e5
T e5
cnot c7 e5
T* e5
cnot d5 e5
T e5
cnot c7 e5
T* e5
cnot d5 e5
H e5
S c3
cnot b2 c3
cnot a3 c3
T* c3
cnot b3 c3
T c3
cnot b2 c3
cnot a3 c3
T* c3
cnot c1 c3
cnot b3 c3
T* c3
cnot d3 c3
T c3
cnot c1 c3
T* c3
cnot d3 c3
H c3
T c5
cnot c7 c5
T* c5
cnot z c5
T c5
cnot c7 c5
T* c5
cnot z c5
H c5
T c5
H bell2
cnot bell2 bell3
cnot c3 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c5
T* c5
cnot d5 c5
T c5
cnot bell2 c5
T* c5
cnot d5 c5
H c5
T* z
Z z
cnot b6 z
cnot a7 z
T* z
cnot b7 z
T z
cnot b6 z
cnot a7 z
T* z
cnot bell2 z
cnot b7 z
T* z
cnot e5 z
T z
cnot bell2 z
T* z
cnot c7 z
cnot e5 z
T* z
cnot c7 z
H z
T e5
cnot bell2 e5
T* e5
cnot bell2 e5
H e5
T e5
cnot c7 e5
T* e5
cnot d5 e5
T e5
cnot c7 e5
T* e5
cnot d5 e5
H e5
T d3
cnot c1 d3
T* d3
cnot c1 d3
H d3
T* d5
Z d5
cnot bell2 d5
T* d5
cnot c7 d5
cnot bell2 d5
S* d5
cnot c7 d5
H d5
T* c7
Z c7
H c7
S c7
cnot a7 c7
T* c7
cnot b7 c7
T c7
cnot a7 c7
S* c7
cnot b6 c7
cnot a7 c7
T c7
cnot b7 c7
T* c7
cnot b2 a3
cnot b4 a5
cnot b6 a7
cnot a7 c7
cnot a6 b6
cnot bell0 b4
cnot a2 b2
H c7
T a1
cnot b1 a1
T* a1
cnot b1 a1
H a1
T* a3
Z a3
cnot b2 a3
cnot a2 a3
S a3
cnot b3 a3
S* a3
cnot b2 a3
cnot a2 a3
T a3
Z a3
cnot d3 a3
T a3
cnot b2 a3
cnot a2 a3
T a3
cnot b3 a3
T* a3
cnot b2 a3
cnot a2 a3
T* a3
cnot d3 a3
H a3
T* a5
Z a5
cnot b4 a5
cnot bell0 a5
S a5
cnot b5 a5
S* a5
cnot b4 a5
cnot bell0 a5
T a5
Z a5
cnot d5 a5
T a5
cnot b4 a5
cnot bell0 a5
T a5
cnot b5 a5
T* a5
cnot b4 a5
cnot bell0 a5
T* a5
cnot d5 a5
H a5
T* a7
Z a7
cnot b6 a7
cnot a6 a7
S a7
cnot b7 a7
S* a7
cnot b6 a7
cnot a6 a7
T a7
Z a7
cnot b7 a7
H a7
T a1
cnot a0 a1
T* a1
cnot b0 a1
T a1
cnot a0 a1
T* a1
cnot b0 a1
H a1
T a3
cnot a2 a3
T* a3
cnot b2 a3
T a3
cnot a2 a3
T* a3
cnot b2 a3
H a3
T a5
cnot bell0 a5
T* a5
cnot b4 a5
T a5
cnot bell0 a5
H bell0
measure bell0
cz bell0 a4
T* a5
cnot b4 a5
H a5
T a7
cnot a6 a7
T* a7
cnot b6 a7
T a7
cnot a6 a7
T* a7
cnot b6 a7
H a7
T b1
cnot c1 a2
cnot c1 a3
cnot c3 a4
cnot bell2 a5
cnot c5 a6
cnot c5 a7
cnot c1 b2
cnot c1 b3
cnot c5 b6
cnot bell2 b4
cnot bell2 b5
H bell2
measure bell2
cz bell2 c3
cnot c5 b7
cnot a7 b7
cnot a6 a7
cnot a6 b6
cnot a5 b5
H bell4
cnot bell4 bell5
cnot a4 bell5
measure bell5
cnot bell5 bell4
cnot bell4 a5
cnot bell4 b4
cnot a3 b3
cnot a2 b2
cnot a1 b1
cnot a2 a3
H a1
cnot b3 c1
cnot a3 c1
cnot a2 c1
T c1
Z c1
cnot d3 c1
S* c1
cnot d3 c1
cnot b3 c1
cnot a3 c1
cnot a2 c1
H a3
H bell6
cnot bell6 bell7
cnot b5 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c3
H bell8
cnot bell8 bell9
cnot a5 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c3
cnot a4 c3
T c3
Z c3
H bell10
cnot bell10 bell11
cnot d5 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c3
S* c3
cnot bell10 c3
H bell10
measure bell10
cz bell10 d5
cnot bell6 c3
H bell6
measure bell6
cz bell6 b5
cnot bell8 c3
H bell8
measure bell8
cz bell8 a5
cnot a4 c3
H a5
cnot b7 c5
cnot a7 c5
cnot a6 c5
T c5
Z c5
cnot b7 c5
cnot a7 c5
cnot a6 c5
H a7
T a1
cnot a0 a1
T* a1
cnot b0 a1
T a1
cnot a0 a1
T* a1
cnot b0 a1
H a1
T a3
cnot a2 a3
T* a3
cnot b2 a3
T a3
cnot a2 a3
T* a3
cnot b2 a3
H a3
T a5
cnot bell4 a5
T* a5
cnot b4 a5
T a5
cnot bell4 a5
T* a5
cnot b4 a5
H a5
T a7
cnot a6 a7
T* a7
cnot b6 a7
T a7
cnot a6 a7
T* a7
cnot b6 a7
H a7
cnot a7 b7
cnot a5 b5
cnot a3 b3
cnot a1 b1
H a1
H a3
H a5
H a7
T a1
cnot a0 a1
T* a1
cnot b0 a1
T a1
cnot a0 a1
T* a1
cnot b0 a1
H a1
T a3
cnot a2 a3
T* a3
cnot b2 a3
T a3
cnot a2 a3
T* a3
cnot b2 a3
H a3
T a5
cnot bell4 a5
T* a5
cnot b4 a5
T a5
cnot bell4 a5
H bell4
measure bell4
cz bell4 a4
T* a5
cnot b4 a5
H a5
T a7
cnot a6 a7
T* a7
cnot b6 a7
T a7
cnot a6 a7
T* a7
cnot b6 a7
H a7
cnot c1 a2
cnot c3 a4
cnot c5 a6
cnot c1 b2
H bell12
cnot bell12 bell13
cnot c3 bell13
measure bell13
cnot bell13 bell12
cnot bell12 b4
H bell12
measure bell12
cz bell12 c3
cnot c5 b6
cnot a6 a7
H bell14
cnot bell14 bell15
cnot a4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 a5
cnot a5 b5
cnot a3 b3
cnot a2 b3
cnot a1 b1
cnot a0 b0
cnot a2 a3
H a1
H a3
H a5
T a1
cnot a0 a1
T* a1
cnot b0 a1
T* a1
cnot a0 a1
T a1
cnot b0 a1
H a1
T a3
cnot a2 a3
T* a3
cnot b2 a3
T* a3
cnot a2 a3
T a3
cnot b2 a3
H a3
T a5
cnot bell14 a5
T* a5
cnot b4 a5
T* a5
cnot bell14 a5
T a5
cnot b4 a5
H a5
Z d3
cnot a3 d3
T* d3
cnot b3 d3
T* d3
cnot a3 d3
S d3
cnot b2 d3
cnot a3 d3
cnot a2 d3
T d3
cnot b3 d3
T d3
cnot b2 a3
cnot b4 a5
cnot bell14 a5
cnot a3 d3
cnot bell14 b4
cnot a2 d3
cnot a2 b2
cnot a2 a3
H d3
Z d5
cnot a5 d5
T d5
cnot b5 d5
T d5
cnot a5 d5
S d5
cnot b4 d5
cnot a5 d5
T* d5
cnot b5 d5
T* d5
cnot b4 d5
cnot a5 d5
H d5
cnot a6 c5
S c5
cnot b6 c5
S c5
cnot a6 c5
cnot b6 c5
H c5
T* c3
Z c3
cnot a4 c3
S c3
H bell16
cnot bell16 bell17
cnot b4 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c3
cnot a4 c3
S c3
H bell18
cnot bell18 bell19
cnot c5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c3
cnot bell16 c3
H bell16
measure bell16
cz bell16 b4
T* c3
H bell20
cnot bell20 bell21
cnot d5 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c3
T c3
cnot bell18 c3
H bell18
measure bell18
cz bell18 c5
T* c3
cnot bell20 c3
H bell20
measure bell20
cz bell20 d5
H c3
S c1
cnot a2 c1
S c1
cnot b2 c1
cnot a2 c1
S c1
cnot c3 c1
cnot b2 c1
T* c1
cnot d3 c1
T c1
cnot c3 c1
T* c1
cnot d3 c1
H c1
T d3
cnot c3 d3
T* d3
cnot c3 d3
H d3
T d5
cnot c5 d5
T* d5
cnot c5 d5
H d5
T c1
cnot a1 c1
T* c1
cnot b1 c1
T* c1
cnot a1 c1
T c1
cnot b2 a3
cnot b4 a5
cnot b1 c1
cnot bell14 b4
cnot a2 b2
H c1
S c3
cnot a3 c3
T* c3
cnot b3 c3
T* c3
cnot a3 c3
T c3
cnot b3 c3
H c3
S d3
cnot a3 d3
T* d3
cnot b3 d3
T* d3
cnot a3 d3
S d3
cnot b2 d3
cnot a3 d3
cnot a2 d3
T d3
cnot b3 d3
T d3
cnot b2 d3
cnot a3 d3
cnot a2 d3
H d3
S c5
cnot a5 c5
T* c5
cnot b5 c5
T* c5
cnot a5 c5
T c5
cnot b5 c5
H c5
S d5
cnot a5 d5
T* d5
cnot b5 d5
T* d5
cnot a5 d5
S d5
cnot b4 d5
cnot a5 d5
cnot bell14 d5
T d5
cnot b5 d5
T d5
cnot b4 d5
cnot a5 d5
cnot bell14 d5
H d5
T a1
cnot b1 a1
T a1
cnot b1 a1
H a1
T* a3
Z a3
cnot b2 a3
cnot a2 a3
S* a3
cnot b3 a3
S* a3
cnot b2 a3
cnot a2 a3
T* a3
Z a3
cnot b3 a3
H a3
T* a5
Z a5
cnot b4 a5
cnot bell14 a5
S* a5
cnot b5 a5
S* a5
cnot b4 a5
cnot bell14 a5
T* a5
Z a5
cnot b5 a5
H a5
T a1
cnot a0 a1
T* a1
cnot b0 a1
T* a1
cnot a0 a1
T a1
cnot b0 a1
H a1
T a3
cnot a2 a3
T* a3
cnot b2 a3
T* a3
cnot a2 a3
T a3
cnot b2 a3
H a3
T a5
cnot bell14 a5
T* a5
cnot b4 a5
T* a5
cnot bell14 a5
H bell14
measure bell14
cz bell14 a4
T a5
cnot b4 a5
H a5
S* a0
S b0
cnot a0 b0
S* b0
Z a2
S* b2
Z a4
S* b4
S a6
T* b1
T* b3
Z b3
T* b5
Z b5
cnot a6 b6
S* b6
cnot a6 b6
cnot a5 c5
cnot a3 c3
cnot a5 b5
cnot a3 b3
cnot a1 c1
cnot a1 b1
cnot a0 b0
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
END
