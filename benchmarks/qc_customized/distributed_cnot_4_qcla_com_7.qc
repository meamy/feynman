# Hyperedge cut (ebits): 10

# Actual ebits used (Synthesis): 11
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/qcla_com_7.qc):
#   Qubits: 24
#   H: 39
#   T: 203
#   X: 15
#   cnot: 186
#   Depth: 70
#   T depth: 31
# Result (55.389ms):
#   Qubits: 46
#   H: 59
#   S: 6
#   T: 95
#   X: 1
#   Z: 2
#   cnot: 175
#   cz: 11
#   measure: 22
#   reset: 22
#   Depth: 81
#   T depth: 25


# Result Circuit
.v a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6
.o a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6
BEGIN 
H c0
H c1
H c2
H d2
H c3
H c4
H d4
H d5
H c6
T c0
cnot a0 c0
T c0
cnot b0 c0
T* c0
cnot a0 c0
T* c0
cnot b0 c0
cnot a6 b6
H bell0
cnot bell0 bell1
cnot a5 bell1
measure bell1
cnot bell1 bell0
cnot bell0 b5
cnot a4 b4
H bell2
cnot bell2 bell3
cnot a3 bell3
measure bell3
cnot bell3 bell2
cnot bell2 b3
cnot a2 b2
cnot a1 b1
H c0
T c2
cnot b2 c2
T c2
cnot b3 c2
T c2
cnot b2 c2
T c2
cnot b3 c2
H c2
T d2
cnot a2 d2
T d2
cnot b2 d2
T* d2
cnot a2 d2
T* d2
cnot b2 d2
H d2
T c4
cnot b4 c4
T c4
cnot b5 c4
T c4
cnot b4 c4
T c4
cnot b5 c4
H c4
T d4
cnot a4 d4
T d4
cnot b4 d4
T* d4
cnot a4 d4
T* d4
cnot b4 d4
H d4
S c1
cnot a1 c1
T c1
cnot b1 c1
T* c1
cnot a1 c1
cnot c0 c1
T* c1
cnot b1 c1
T* c1
cnot c0 c1
H c1
T c5
cnot b6 c5
T c5
H bell4
cnot bell4 bell5
cnot c4 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c5
T* c5
cnot b6 c5
T* c5
cnot bell4 c5
H bell4
measure bell4
cz bell4 c4
H c5
S d5
cnot bell0 d5
T d5
cnot b5 d5
T* d5
cnot bell0 d5
cnot d4 d5
T* d5
cnot b5 d5
T* d5
cnot d4 d5
H d5
T* c3
Z c3
cnot bell2 c3
T c3
cnot b3 c3
T* c3
cnot bell2 c3
H bell6
cnot bell6 bell7
cnot c1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c3
cnot b3 c3
T* c3
cnot c2 c3
T c3
cnot bell6 c3
H bell6
measure bell6
cz bell6 c1
T* c3
cnot d2 c3
cnot c2 c3
T* c3
cnot b3 c3
T* c3
cnot d2 c3
cnot b3 c3
H c3
T c3
H bell8
cnot bell8 bell9
cnot c5 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c3
T* c3
H bell10
cnot bell10 bell11
cnot c6 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c3
T c3
cnot bell8 c3
H bell8
measure bell8
cz bell8 c5
T* c3
cnot bell10 c3
H bell10
measure bell10
cz bell10 c6
H c3
T c5
cnot c6 c5
T* c5
cnot c6 c5
H c5
T* d5
H bell12
cnot bell12 bell13
cnot b6 bell13
measure bell13
cnot bell13 bell12
cnot bell12 d5
T* d5
H bell14
cnot bell14 bell15
cnot c6 bell15
measure bell15
cnot bell15 bell14
cnot bell14 d5
T d5
cnot bell12 d5
T d5
cnot bell14 d5
H bell14
measure bell14
cz bell14 c6
H d5
H bell16
cnot bell16 bell17
cnot c2 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c1
H bell18
cnot bell18 bell19
cnot c3 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c1
T* c1
cnot bell16 c1
H bell16
measure bell16
cz bell16 c2
T c1
cnot bell18 c1
H bell18
measure bell18
cz bell18 c3
H c1
cnot b1 c0
cnot c1 c0
T c0
cnot b1 c0
T c0
cnot c1 c0
H c0
cnot c3 c2
T c2
cnot c3 c2
H c2
cnot b3 d2
cnot c3 d2
T d2
cnot b3 d2
T d2
cnot c3 d2
H d2
cnot bell12 c4
H bell20
cnot bell20 bell21
cnot c5 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c4
T c4
cnot bell12 c4
H bell12
measure bell12
cz bell12 b6
T c4
cnot bell20 c4
H bell20
measure bell20
cz bell20 c5
H c4
cnot b5 d4
cnot d5 d4
T d4
cnot b5 d4
T d4
cnot d5 d4
H d4
T* c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T c0
cnot b0 c0
cnot a6 b6
cnot bell0 b5
cnot a4 b4
cnot bell2 b3
cnot a2 b2
cnot a1 b1
H c0
S* c1
cnot a1 c1
T* c1
cnot b1 c1
cnot a1 c1
T c1
cnot b1 c1
H c1
T* c2
cnot b2 c2
cnot a2 c2
T* c2
cnot b3 c2
cnot bell2 c2
T* c2
cnot b2 c2
cnot a2 c2
T* c2
cnot b3 c2
cnot bell2 c2
H c2
T* d2
cnot a2 d2
T* d2
cnot b2 d2
T d2
cnot a2 d2
T d2
cnot b2 d2
H d2
T c3
Z c3
cnot bell2 c3
T* c3
cnot b3 c3
cnot bell2 c3
H bell2
measure bell2
cz bell2 a3
T c3
cnot b3 c3
H c3
T* c4
cnot b4 c4
cnot a4 c4
T* c4
cnot b5 c4
cnot bell0 c4
T* c4
cnot b4 c4
cnot a4 c4
T* c4
cnot b5 c4
cnot bell0 c4
H c4
T* d4
cnot a4 d4
T* d4
cnot b4 d4
T d4
cnot a4 d4
T d4
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
cnot bell0 d5
T* d5
cnot b5 d5
cnot bell0 d5
H bell0
measure bell0
cz bell0 a5
T d5
cnot b5 d5
H d5
T c6
cnot a6 c6
T c6
cnot b6 c6
S* c6
cnot a6 c6
T* c6
cnot b6 c6
H c6
T* a6
T b6
cnot a6 b6
S b6
cnot a6 b6
X c6
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
