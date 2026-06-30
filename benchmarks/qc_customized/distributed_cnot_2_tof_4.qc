# Hyperedge cut (ebits): 1

# Actual ebits used (Synthesis): 1
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_4.qc):
#   Qubits: 7
#   H: 10
#   T: 35
#   cnot: 30
#   Depth: 38
#   T depth: 16
# Result (9.686ms):
#   Qubits: 9
#   H: 12
#   T: 23
#   cnot: 25
#   cz: 1
#   measure: 2
#   reset: 2
#   Depth: 50
#   T depth: 18


# Result Circuit
.v 1 2 3 4 5 6 7 bell0 bell1
.i 1 2 3 4 7
.o 1 2 3 4 5 6 7
BEGIN 
H 5
T 5
cnot 1 5
T* 5
cnot 2 5
T 5
cnot 1 5
T* 5
cnot 2 5
H 5
H 6
T 6
cnot 3 6
T* 6
H bell0
cnot bell0 bell1
cnot 5 bell1
measure bell1
cnot bell1 bell0
cnot bell0 6
T 6
cnot 3 6
T* 6
cnot bell0 6
H 6
H 7
T 7
cnot 4 7
T* 7
cnot 6 7
T 7
cnot 4 7
T* 7
cnot 6 7
H 7
T 6
cnot 4 6
T* 6
cnot 4 6
H 6
T* 6
cnot 3 6
T 6
cnot bell0 6
T* 6
cnot 3 6
T 6
cnot bell0 6
H bell0
measure bell0
cz bell0 5
H 6
H 5
T* 5
cnot 1 5
T 5
cnot 2 5
T* 5
cnot 1 5
T 5
cnot 2 5
H 5
T 4
reset bell0
reset bell1
END
