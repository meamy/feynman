# Hyperedge cut (ebits): 3

# Actual ebits used (Synthesis): 3
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_5.qc):
#   Qubits: 9
#   H: 14
#   T: 49
#   cnot: 42
#   Depth: 53
#   T depth: 22
# Result (12.091ms):
#   Qubits: 15
#   H: 20
#   T: 31
#   cnot: 39
#   cz: 3
#   measure: 6
#   reset: 6
#   Depth: 71
#   T depth: 24


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 bell0 bell1 bell2 bell3 bell4 bell5
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
H bell0
cnot bell0 bell1
cnot 6 bell1
measure bell1
cnot bell1 bell0
cnot bell0 7
T 7
cnot 3 7
T* 7
cnot bell0 7
H 7
H 8
T 8
cnot 4 8
T* 8
H bell2
cnot bell2 bell3
cnot 7 bell3
measure bell3
cnot bell3 bell2
cnot bell2 8
T 8
cnot 4 8
T* 8
cnot bell2 8
H 8
H 9
T 9
H bell4
cnot bell4 bell5
cnot 5 bell5
measure bell5
cnot bell5 bell4
cnot bell4 9
T* 9
cnot 8 9
T 9
cnot bell4 9
T* 9
cnot 8 9
H 9
T 8
cnot bell4 8
T* 8
cnot bell4 8
H bell4
measure bell4
cz bell4 5
H 8
T* 8
cnot 4 8
T 8
cnot bell2 8
T* 8
cnot 4 8
T 8
cnot bell2 8
H bell2
measure bell2
cz bell2 7
H 8
H 7
T* 7
cnot 3 7
T 7
cnot bell0 7
T* 7
cnot 3 7
T 7
cnot bell0 7
H bell0
measure bell0
cz bell0 6
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
reset bell2
reset bell3
reset bell4
reset bell5
END
