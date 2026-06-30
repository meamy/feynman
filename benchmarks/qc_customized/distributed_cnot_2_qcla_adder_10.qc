# Hyperedge cut (ebits): 7

# Actual ebits used (Synthesis): 7
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/qcla_adder_10.qc):
#   Qubits: 36
#   H: 50
#   T: 238
#   cnot: 233
#   Depth: 64
#   T depth: 30
# Result (119.446ms):
#   Qubits: 50
#   H: 64
#   S: 10
#   T: 162
#   cnot: 243
#   cz: 7
#   measure: 14
#   reset: 14
#   Depth: 92
#   T depth: 28


# Result Circuit
.v a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 d6 a7 b7 c7 a8 b8 c8 d8 a9 b9 c9 e bell0 bell1 bell10 bell11 bell12 bell13 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9
.o a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 d6 a7 b7 c7 a8 b8 c8 d8 a9 b9 c9 e
BEGIN 
H c0
H c1
H c2
H d2
H c3
H c4
H d4
H c5
H d5
H c6
H d6
H c7
H c8
H d8
H c9
T c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T* c0
cnot b0 c0
cnot a9 b9
cnot a8 b8
cnot a7 b7
cnot a6 b6
cnot a5 b5
H bell0
cnot bell0 bell1
cnot a4 bell1
measure bell1
cnot bell1 bell0
cnot bell0 b4
cnot a3 b3
cnot a2 b2
cnot a1 b1
H c0
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
H bell2
cnot bell2 bell3
cnot b4 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c4
T* c4
H bell4
cnot bell4 bell5
cnot b5 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c4
T c4
cnot bell2 c4
T* c4
cnot bell4 c4
H c4
T d4
cnot bell0 d4
T* d4
cnot b4 d4
T* d4
cnot bell0 d4
H bell0
measure bell0
cz bell0 a4
T d4
cnot b4 d4
H d4
T c6
cnot b6 c6
T* c6
cnot b7 c6
T c6
cnot b6 c6
T* c6
cnot b7 c6
H c6
T d6
cnot a6 d6
T* d6
cnot b6 d6
T* d6
cnot a6 d6
T d6
cnot b6 d6
H d6
T c8
cnot b8 c8
T* c8
cnot b9 c8
T c8
cnot b8 c8
T* c8
cnot b9 c8
H c8
T d8
cnot a8 d8
T* d8
cnot b8 d8
T* d8
cnot a8 d8
T d8
cnot b8 d8
H d8
cnot a1 c1
T* c1
cnot b1 c1
T* c1
cnot a1 c1
S c1
cnot c0 c1
T* c1
cnot b1 c1
T c1
cnot c0 c1
H c1
T* c5
cnot c4 c5
T c5
cnot c6 c5
T* c5
cnot c4 c5
T c5
cnot c6 c5
H c5
H bell6
cnot bell6 bell7
cnot a5 bell7
measure bell7
cnot bell7 bell6
cnot bell6 d5
T* d5
cnot bell4 d5
T* d5
cnot bell6 d5
H bell6
measure bell6
cz bell6 a5
S d5
H bell8
cnot bell8 bell9
cnot d4 bell9
measure bell9
cnot bell9 bell8
cnot bell8 d5
T* d5
cnot bell4 d5
T d5
cnot bell8 d5
H bell8
measure bell8
cz bell8 d4
H d5
T c3
cnot a3 c3
T* c3
cnot b3 c3
T* c3
cnot a3 c3
S c3
cnot c1 c3
cnot b3 c3
T* c3
cnot c2 c3
T c3
cnot c1 c3
T* c3
cnot d2 c3
cnot c2 c3
T c3
cnot b3 c3
T* c3
cnot d2 c3
cnot b3 c3
H c3
T d5
cnot c6 d5
T* d5
cnot c7 d5
T d5
cnot c6 d5
T* d5
cnot c7 d5
H d5
cnot a7 c7
T* c7
cnot b7 c7
T* c7
cnot a7 c7
S c7
H bell10
cnot bell10 bell11
cnot c3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c7
cnot b7 c7
T c7
cnot c5 c7
T* c7
cnot bell10 c7
T c7
cnot d6 c7
cnot c5 c7
T c7
cnot b7 c7
T* c7
cnot c6 c7
cnot d6 c7
cnot b7 c7
T* c7
cnot c6 c7
H c7
T d5
cnot bell10 d5
T* d5
cnot c4 d5
T d5
cnot bell10 d5
T* d5
cnot c4 d5
H d5
T* d2
cnot b3 d2
T d2
cnot b3 d2
H d2
T* d4
cnot b5 d4
T d4
cnot b5 d4
H d4
T* d6
cnot b7 d6
T d6
cnot b7 d6
H d6
T* d8
cnot b9 d8
T d8
cnot c9 d8
T* d8
cnot b9 d8
T d8
cnot c9 d8
H d8
T* c5
cnot bell10 c5
T c5
cnot bell10 c5
H c5
T c2
cnot c1 c2
T* c2
cnot c1 c2
H c2
T c4
cnot c5 c4
T* c4
cnot c6 c4
T c4
cnot c5 c4
cnot bell10 c4
cnot c6 c4
T* c4
cnot bell10 c4
H bell10
measure bell10
cz bell10 c3
H c4
T c6
cnot c5 c6
T* c6
cnot c5 c6
H c6
T c8
cnot c7 c8
T* c8
cnot c9 c8
T c8
cnot c7 c8
T* c8
cnot c9 c8
H c8
T* d2
cnot b2 d2
T d2
cnot c1 d2
T* d2
cnot b2 d2
T d2
cnot c1 d2
H d2
T* d4
cnot b4 d4
T d4
cnot c3 d4
T* d4
cnot b4 d4
T d4
cnot c3 d4
H d4
T* d6
cnot b6 d6
T d6
cnot d5 d6
T* d6
cnot b6 d6
T d6
cnot d5 d6
H d6
T* d8
cnot b8 d8
T d8
cnot c7 d8
T* d8
cnot b8 d8
T d8
cnot c7 d8
H d8
T c9
cnot a9 c9
T* c9
cnot b9 c9
T* c9
cnot a9 c9
S c9
cnot c7 c9
cnot b9 c9
T* c9
cnot c7 c9
H c9
T c5
H c5
T c2
cnot b2 c2
T* c2
cnot b3 c2
T c2
cnot b2 c2
T* c2
cnot b3 c2
H c2
T c4
cnot bell2 c4
T* c4
cnot bell4 c4
T c4
cnot bell2 c4
H bell2
measure bell2
cz bell2 b4
T* c4
cnot bell4 c4
H bell4
measure bell4
cz bell4 b5
H c4
T c6
cnot b6 c6
T* c6
cnot b7 c6
T c6
cnot b6 c6
T* c6
cnot b7 c6
H c6
T c8
cnot b8 c8
T* c8
cnot b9 c8
T c8
cnot b8 c8
T* c8
cnot b9 c8
H c8
T a2
cnot a2 b2
T b2
cnot b2 b3
cnot a2 b3
S* b3
T a3
cnot b3 a3
cnot b2 a3
cnot a2 a3
T a3
T a4
H bell12
cnot bell12 bell13
cnot a4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 b4
T b4
cnot b4 b5
cnot bell12 b5
S* b5
T a5
cnot b5 a5
cnot b4 a5
cnot bell12 a5
T a5
T a6
cnot a6 b6
T b6
cnot b6 b7
cnot a6 b7
S* b7
T a7
cnot b7 a7
cnot b6 a7
cnot a6 a7
T a7
T a8
cnot a8 b8
T b8
cnot b8 b9
cnot a8 b9
S* b9
T a9
cnot b9 a9
cnot b8 a9
cnot a8 a9
T a9
T a0
T b0
cnot a0 b0
T* b0
T a1
S* b1
cnot a1 b1
T b1
T* c0
cnot b1 c0
cnot a1 c0
T c0
cnot b2 c1
cnot a2 c1
T c1
T* c3
cnot b4 c3
cnot bell12 c3
T c3
cnot b8 c7
cnot a8 c7
T c7
T* d5
cnot b6 d5
cnot a6 d5
T d5
cnot b8 b9
cnot b9 c8
cnot b6 b7
cnot b7 d6
cnot b5 d4
cnot b2 b3
cnot b4 d4
cnot b3 d2
cnot b4 b5
cnot b9 a9
cnot b0 e
cnot a9 b9
cnot b7 a7
cnot a7 b7
cnot a6 a7
cnot a6 d6
cnot a8 c8
cnot a8 a9
cnot b5 a5
cnot a5 b5
cnot bell12 a5
cnot b3 a3
cnot bell12 d4
H bell12
measure bell12
cz bell12 a4
cnot a3 b3
cnot a2 d2
cnot a0 b0
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
END
