# Hyperedge cut (ebits): 6

# Actual ebits used (Synthesis): 7
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_mult_55.qc):
#   Qubits: 9
#   H: 14
#   T: 49
#   X: 8
#   cnot: 48
#   Depth: 43
#   T depth: 19
# Result (20.190ms):
#   Qubits: 23
#   H: 28
#   S: 1
#   T: 35
#   cnot: 61
#   cz: 7
#   measure: 14
#   reset: 14
#   swap: 3
#   Depth: 68
#   T depth: 20


# Result Circuit
.v x0 x1 x2 y0 y1 y2 y3 y4 y5 bell0 bell1 bell10 bell11 bell12 bell13 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i x0 x1 x2
.o x0 x1 x2 y0 y1 y2 y3 y4 y5
BEGIN 
H y4
T y4
H bell0
cnot bell0 bell1
cnot x0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 y4
T* y4
H bell2
cnot bell2 bell3
cnot x2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 y4
T* y4
cnot bell0 y4
T y4
cnot bell2 y4
H y4
H y3
H y5
T y5
cnot bell0 y5
T y5
cnot bell2 y5
T* y5
cnot bell0 y5
T* y5
cnot bell2 y5
H y5
T y3
H bell4
cnot bell4 bell5
cnot x1 bell5
measure bell5
cnot bell5 bell4
cnot bell4 y3
T* y3
H bell6
cnot bell6 bell7
cnot y4 bell7
measure bell7
cnot bell7 bell6
cnot bell6 y3
T y3
cnot bell4 y3
T* y3
cnot bell6 y3
H bell6
measure bell6
cz bell6 y4
swap y0 y1
H y3
cnot y3 y0
cnot y3 y1
cnot y5 y4
swap y2 y3
swap y1 y3
H y0
H y3
T y3
cnot bell4 y3
T y3
H bell8
cnot bell8 bell9
cnot y5 bell9
measure bell9
cnot bell9 bell8
cnot bell8 y3
T* y3
cnot bell4 y3
T* y3
cnot bell8 y3
H bell8
measure bell8
cz bell8 y5
H y3
T* y0
cnot bell4 y0
T* y0
H bell10
cnot bell10 bell11
cnot y4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 y0
T* y0
cnot bell4 y0
H bell4
measure bell4
cz bell4 x1
T* y0
cnot bell10 y0
H bell10
measure bell10
cz bell10 y4
H y0
T y5
H bell12
cnot bell12 bell13
cnot x1 bell13
measure bell13
cnot bell13 bell12
cnot bell12 y5
T y5
cnot y4 y5
T* y5
cnot bell12 y5
T y5
cnot y3 y1
cnot y4 y5
cnot y2 y5
H y2
H y5
T* y5
cnot bell0 y5
T* y5
cnot bell2 y5
T y5
cnot bell0 y5
H bell0
measure bell0
cz bell0 x0
T y5
cnot bell2 y5
H bell2
measure bell2
cz bell2 x2
H y5
T* y2
cnot bell12 y2
T y2
cnot y4 y2
T y2
cnot bell12 y2
H bell12
measure bell12
cz bell12 x1
T* y2
cnot y4 y2
H y2
T x0
T* x2
cnot x0 x2
T x2
S y4
cnot y2 y5
cnot x0 x2
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
