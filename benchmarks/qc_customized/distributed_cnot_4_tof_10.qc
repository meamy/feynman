# Hyperedge cut (ebits): 4

# Actual ebits used (Synthesis): 4
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_10.qc):
#   Qubits: 19
#   H: 34
#   T: 119
#   cnot: 102
#   Depth: 128
#   T depth: 52
# Result (32.672ms):
#   Qubits: 27
#   H: 42
#   T: 71
#   cnot: 82
#   cz: 4
#   measure: 8
#   reset: 8
#   Depth: 152
#   T depth: 54


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 bell0 bell1 bell2 bell3 bell4 bell5 bell6 bell7
.i 1 2 3 4 5 6 7 8 9 10 19
.o 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
BEGIN 
H 11
T 11
cnot 1 11
T* 11
cnot 2 11
T 11
cnot 1 11
T* 11
cnot 2 11
H 11
H 12
T 12
cnot 11 12
T* 12
cnot 3 12
T 12
cnot 11 12
T* 12
cnot 3 12
H 12
H 13
T 13
H bell0
cnot bell0 bell1
cnot 12 bell1
measure bell1
cnot bell1 bell0
cnot bell0 13
T* 13
cnot 4 13
T 13
cnot bell0 13
T* 13
cnot 4 13
H 13
H 14
T 14
cnot 13 14
T* 14
cnot 5 14
T 14
cnot 13 14
T* 14
cnot 5 14
H 14
H 15
T 15
H bell2
cnot bell2 bell3
cnot 14 bell3
measure bell3
cnot bell3 bell2
cnot bell2 15
T* 15
cnot 6 15
T 15
cnot bell2 15
T* 15
cnot 6 15
H 15
H 16
T 16
cnot 15 16
T* 16
cnot 7 16
T 16
cnot 15 16
T* 16
cnot 7 16
H 16
H 17
T 17
H bell4
cnot bell4 bell5
cnot 16 bell5
measure bell5
cnot bell5 bell4
cnot bell4 17
T* 17
cnot 8 17
T 17
cnot bell4 17
T* 17
cnot 8 17
H 17
H 18
T 18
cnot 17 18
T* 18
H bell6
cnot bell6 bell7
cnot 9 bell7
measure bell7
cnot bell7 bell6
cnot bell6 18
T 18
cnot 17 18
T* 18
cnot bell6 18
H 18
H 19
T 19
cnot 10 19
T* 19
cnot 18 19
T 19
cnot 10 19
T* 19
cnot 18 19
H 19
T 18
cnot 10 18
T* 18
cnot 10 18
H 18
T* 18
cnot 17 18
T 18
cnot bell6 18
T* 18
cnot 17 18
T 18
cnot bell6 18
H bell6
measure bell6
cz bell6 9
H 18
H 17
T* 17
cnot bell4 17
T 17
cnot 8 17
T* 17
cnot bell4 17
H bell4
measure bell4
cz bell4 16
T 17
cnot 8 17
H 17
H 16
T* 16
cnot 15 16
T 16
cnot 7 16
T* 16
cnot 15 16
T 16
cnot 7 16
H 16
H 15
T* 15
cnot bell2 15
T 15
cnot 6 15
T* 15
cnot bell2 15
H bell2
measure bell2
cz bell2 14
T 15
cnot 6 15
H 15
H 14
T* 14
cnot 13 14
T 14
cnot 5 14
T* 14
cnot 13 14
T 14
cnot 5 14
H 14
H 13
T* 13
cnot bell0 13
T 13
cnot 4 13
T* 13
cnot bell0 13
H bell0
measure bell0
cz bell0 12
T 13
cnot 4 13
H 13
H 12
T* 12
cnot 11 12
T 12
cnot 3 12
T* 12
cnot 11 12
T 12
cnot 3 12
H 12
H 11
T* 11
cnot 1 11
T 11
cnot 2 11
T* 11
cnot 1 11
T 11
cnot 2 11
H 11
T 10
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
reset bell6
reset bell7
END
