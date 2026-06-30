# Hyperedge cut (ebits): 4

# Actual ebits used (Synthesis): 4
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
# Result (20.056ms):
#   Qubits: 17
#   H: 22
#   S: 1
#   T: 35
#   cnot: 52
#   cz: 4
#   measure: 8
#   reset: 8
#   swap: 3
#   Depth: 59
#   T depth: 20


# Result Circuit
.v x0 x1 x2 y0 y1 y2 y3 y4 y5 bell0 bell1 bell2 bell3 bell4 bell5 bell6 bell7
.i x0 x1 x2
.o x0 x1 x2 y0 y1 y2 y3 y4 y5
BEGIN 
H y4
T y4
cnot x0 y4
T* y4
cnot x2 y4
T* y4
cnot x0 y4
T y4
cnot x2 y4
H y4
H y3
H y5
T y5
cnot x0 y5
T y5
cnot x2 y5
T* y5
cnot x0 y5
T* y5
cnot x2 y5
H y5
T y3
cnot x1 y3
T* y3
H bell0
cnot bell0 bell1
cnot y4 bell1
measure bell1
cnot bell1 bell0
cnot bell0 y3
T y3
cnot x1 y3
T* y3
cnot bell0 y3
H bell0
measure bell0
cz bell0 y4
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
cnot x1 y3
T y3
H bell2
cnot bell2 bell3
cnot y5 bell3
measure bell3
cnot bell3 bell2
cnot bell2 y3
T* y3
cnot x1 y3
T* y3
cnot bell2 y3
H bell2
measure bell2
cz bell2 y5
H y3
T* y0
cnot x1 y0
T* y0
H bell4
cnot bell4 bell5
cnot y4 bell5
measure bell5
cnot bell5 bell4
cnot bell4 y0
T* y0
cnot x1 y0
T* y0
cnot bell4 y0
H bell4
measure bell4
cz bell4 y4
H y0
T y5
H bell6
cnot bell6 bell7
cnot x1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 y5
T y5
cnot y4 y5
T* y5
cnot bell6 y5
T y5
cnot y3 y1
cnot y4 y5
cnot y2 y5
H y2
H y5
T* y5
cnot x0 y5
T* y5
cnot x2 y5
T y5
cnot x0 y5
T y5
cnot x2 y5
H y5
T* y2
cnot bell6 y2
T y2
cnot y4 y2
T y2
cnot bell6 y2
H bell6
measure bell6
cz bell6 x1
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
END
