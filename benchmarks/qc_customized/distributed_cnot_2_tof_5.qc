# Hyperedge cut (ebits): 1

# Actual ebits used (Synthesis): 1
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_5.qc):
#   Qubits: 9
#   H: 14
#   T: 49
#   cnot: 42
#   Depth: 53
#   T depth: 22
# Result (10.804ms):
#   Qubits: 11
#   H: 16
#   T: 31
#   cnot: 33
#   cz: 1
#   measure: 2
#   reset: 2
#   Depth: 65
#   T depth: 24


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 bell0 bell1
.i 1 2 3 4 5 9
.o 1 2 3 4 5 6 7 8 9
BEGIN 
H 6
T 6
cnot 1 6
T* 6
cnot 2 6
T 6
cnot 1 6
T* 6
cnot 2 6
H 6
H 7
T 7
cnot 3 7
T* 7
cnot 6 7
T 7
cnot 3 7
T* 7
cnot 6 7
H 7
H 8
T 8
cnot 4 8
T* 8
H bell0
cnot bell0 bell1
cnot 7 bell1
measure bell1
cnot bell1 bell0
cnot bell0 8
T 8
cnot 4 8
T* 8
cnot bell0 8
H 8
H 9
T 9
cnot 5 9
T* 9
cnot 8 9
T 9
cnot 5 9
T* 9
cnot 8 9
H 9
T 8
cnot 5 8
T* 8
cnot 5 8
H 8
T* 8
cnot 4 8
T 8
cnot bell0 8
T* 8
cnot 4 8
T 8
cnot bell0 8
H bell0
measure bell0
cz bell0 7
H 8
H 7
T* 7
cnot 3 7
T 7
cnot 6 7
T* 7
cnot 3 7
T 7
cnot 6 7
H 7
H 6
T* 6
cnot 1 6
T 6
cnot 2 6
T* 6
cnot 1 6
T 6
cnot 2 6
H 6
T 5
reset bell0
reset bell1
END
