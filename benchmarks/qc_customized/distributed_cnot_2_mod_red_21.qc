# Hyperedge cut (ebits): 5

# Actual ebits used (Synthesis): 5
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
# Result (21.281ms):
#   Qubits: 21
#   H: 40
#   S: 1
#   T: 73
#   cnot: 115
#   cz: 5
#   measure: 10
#   reset: 10
#   Depth: 179
#   T depth: 59


# Result Circuit
.v x0 x1 c1 x2 c2 x3 c3 x4 c4 d4 z bell0 bell1 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
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
cnot c2 c3
T c3
cnot x3 c3
T c3
cnot c2 c3
T c3
cnot x3 c3
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
H bell2
cnot bell2 bell3
cnot d4 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c4
T* c4
cnot z c4
T c4
cnot bell2 c4
T* c4
cnot z c4
H c4
cnot c3 c2
T* c2
cnot x3 c2
T* c2
cnot c3 c2
cnot x3 c2
H c2
H c1
T c1
cnot x0 c1
cnot c4 c1
T* c1
cnot x1 c1
cnot c4 c1
T c1
cnot x0 c1
cnot c4 c1
T* c1
H bell4
cnot bell4 bell5
cnot c4 bell5
measure bell5
cnot bell5 bell4
cnot bell4 x3
cnot c4 x1
cnot c4 x0
cnot x1 c1
H c1
H bell6
cnot bell6 bell7
cnot c1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c2
T c2
cnot x2 c2
T* c2
cnot bell6 c2
H bell8
cnot bell8 bell9
cnot x1 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c2
cnot bell4 c2
T* c2
cnot x2 c2
T c2
cnot bell4 c2
cnot bell8 c2
H c2
cnot c2 c3
T c3
cnot x3 c3
T* c3
cnot c2 c3
T* c3
cnot bell4 c3
T* c3
cnot x3 c3
cnot bell4 c3
H c3
T x4
H x4
T x4
cnot c3 x4
T x4
cnot bell4 x4
T* x4
cnot c3 x4
T* x4
cnot bell4 x4
H x4
T* c3
cnot bell4 c3
T c3
cnot bell4 c3
H c3
T* c3
cnot c2 c3
T* c3
cnot x3 c3
T c3
cnot c2 c3
T c3
cnot x3 c3
H c3
cnot c2 x3
cnot bell4 x3
cnot c2 x3
cnot bell4 x3
H x3
T* x3
cnot c2 x3
T x3
cnot bell4 x3
T* x3
cnot c2 x3
T x3
cnot bell4 x3
H x3
T* c2
cnot bell4 c2
T c2
cnot bell4 c2
H c2
T* c2
cnot bell6 c2
T* c2
cnot x2 c2
T c2
cnot bell6 c2
T c2
cnot x2 c2
H c2
cnot bell6 x2
cnot bell8 x2
cnot bell4 x2
cnot bell6 x2
cnot bell8 x2
H bell8
measure bell8
cz bell8 x1
cnot bell4 x2
H x2
T* x2
cnot bell6 x2
T* x2
cnot bell4 x2
T x2
cnot bell6 x2
H bell6
measure bell6
cz bell6 c1
T x2
cnot bell4 x2
H bell4
measure bell4
cz bell4 c4
H x2
T c1
cnot c4 c1
T* c1
cnot c4 c1
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
cnot c4 x1
cnot x0 x1
cnot c4 x1
cnot x0 x1
H x1
T* x1
cnot c4 x1
T x1
cnot x0 x1
T x1
cnot c4 x1
T* x1
cnot x0 x1
H x1
S* c4
cnot x0 c4
T* c4
cnot x0 c4
H c4
T* c4
cnot bell2 c4
T c4
cnot z c4
T* c4
cnot bell2 c4
H bell2
measure bell2
cz bell2 d4
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
END
