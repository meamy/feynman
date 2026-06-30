# Hyperedge cut (ebits): 4

# Actual ebits used (Synthesis): 4
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_4.qc):
#   Qubits: 7
#   H: 10
#   T: 35
#   cnot: 30
#   Depth: 38
#   T depth: 16
# Result (9.901ms):
#   Qubits: 15
#   H: 18
#   T: 23
#   cnot: 34
#   cz: 4
#   measure: 8
#   reset: 8
#   Depth: 60
#   T depth: 18


# Result Circuit
.v 1 2 3 4 5 6 7 bell0 bell1 bell2 bell3 bell4 bell5 bell6 bell7
.i 1 2 3 4 7
.o 1 2 3 4 5 6 7
BEGIN 
H 5
T 5
cnot 1 5
T* 5
H bell0
cnot bell0 bell1
cnot 2 bell1
measure bell1
cnot bell1 bell0
cnot bell0 5
T 5
cnot 1 5
T* 5
cnot bell0 5
H 5
H 6
T 6
cnot 3 6
T* 6
H bell2
cnot bell2 bell3
cnot 5 bell3
measure bell3
cnot bell3 bell2
cnot bell2 6
T 6
cnot 3 6
T* 6
cnot bell2 6
H 6
H 7
T 7
cnot 4 7
T* 7
H bell4
cnot bell4 bell5
cnot 6 bell5
measure bell5
cnot bell5 bell4
cnot bell4 7
T 7
cnot 4 7
T* 7
cnot bell4 7
H bell4
measure bell4
cz bell4 6
H 7
T 6
H bell6
cnot bell6 bell7
cnot 4 bell7
measure bell7
cnot bell7 bell6
cnot bell6 6
T* 6
cnot bell6 6
H bell6
measure bell6
cz bell6 4
H 6
T* 6
cnot 3 6
T 6
cnot bell2 6
T* 6
cnot 3 6
T 6
cnot bell2 6
H bell2
measure bell2
cz bell2 5
H 6
H 5
T* 5
cnot 1 5
T 5
cnot bell0 5
T* 5
cnot 1 5
T 5
cnot bell0 5
H bell0
measure bell0
cz bell0 2
H 5
T 4
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
reset bell6
reset bell7
END
