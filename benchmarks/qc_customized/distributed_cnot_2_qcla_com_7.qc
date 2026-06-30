# Hyperedge cut (ebits): 3

# Actual ebits used (Synthesis): 3
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
# Result (57.106ms):
#   Qubits: 30
#   H: 43
#   S: 6
#   T: 95
#   X: 1
#   Z: 2
#   cnot: 151
#   cz: 3
#   measure: 6
#   reset: 6
#   Depth: 75
#   T depth: 25


# Result Circuit
.v a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 bell0 bell1 bell2 bell3 bell4 bell5
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
H bell0
cnot bell0 bell1
cnot b0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
cnot a0 c0
T* c0
cnot bell0 c0
cnot a6 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
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
cnot c4 c5
T* c5
cnot b6 c5
T* c5
cnot c4 c5
H c5
S d5
cnot a5 d5
T d5
cnot b5 d5
T* d5
cnot a5 d5
cnot d4 d5
T* d5
cnot b5 d5
T* d5
cnot d4 d5
H d5
T* c3
Z c3
cnot a3 c3
T c3
cnot b3 c3
T* c3
cnot a3 c3
cnot c1 c3
cnot b3 c3
T* c3
cnot c2 c3
T c3
cnot c1 c3
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
H bell2
cnot bell2 bell3
cnot c5 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c3
T* c3
H bell4
cnot bell4 bell5
cnot c6 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c3
T c3
cnot bell2 c3
H bell2
measure bell2
cz bell2 c5
T* c3
cnot bell4 c3
H bell4
measure bell4
cz bell4 c6
H c3
T c5
cnot c6 c5
T* c5
cnot c6 c5
H c5
T* d5
cnot b6 d5
T* d5
cnot c6 d5
T d5
cnot b6 d5
T d5
cnot c6 d5
H d5
cnot c2 c1
cnot c3 c1
T* c1
cnot c2 c1
T c1
cnot c3 c1
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
cnot b6 c4
cnot c5 c4
T c4
cnot b6 c4
T c4
cnot c5 c4
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
cnot bell0 c0
T c0
cnot a0 c0
T c0
cnot bell0 c0
H bell0
measure bell0
cz bell0 b0
cnot a6 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
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
T* d2
cnot b2 d2
T d2
cnot a2 d2
T d2
cnot b2 d2
H d2
T c3
Z c3
cnot a3 c3
T* c3
cnot b3 c3
cnot a3 c3
T c3
cnot b3 c3
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
cnot a5 d5
T* d5
cnot b5 d5
cnot a5 d5
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
END
