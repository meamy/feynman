# Hyperedge cut (ebits): 6

# Actual ebits used (Synthesis): 6
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_4.qc):
#   Qubits: 7
#   H: 10
#   T: 56
#   cnot: 48
#   Depth: 61
#   T depth: 25
# Result (12.608ms):
#   Qubits: 19
#   H: 22
#   T: 28
#   cnot: 54
#   cz: 6
#   measure: 12
#   reset: 12
#   Depth: 78
#   T depth: 26


# Result Circuit
.v 1 2 3 4 5 6 7 bell0 bell1 bell10 bell11 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i 1 2 3 4 5 6 7
.o 1 2 3 4 5 6 7
BEGIN 
H 7
T 6
H bell0
cnot bell0 bell1
cnot 4 bell1
measure bell1
cnot bell1 bell0
cnot bell0 6
T* 6
H bell2
cnot bell2 bell3
cnot 7 bell3
measure bell3
cnot bell3 bell2
cnot bell2 6
T 6
cnot bell0 6
T* 6
cnot bell2 6
H bell2
measure bell2
cz bell2 7
H 6
T 5
H bell4
cnot bell4 bell5
cnot 3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 5
T* 5
cnot 6 5
T 5
cnot bell4 5
T* 5
cnot 6 5
H 5
T 5
H bell6
cnot bell6 bell7
cnot 1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 5
T* 5
H bell8
cnot bell8 bell9
cnot 2 bell9
measure bell9
cnot bell9 bell8
cnot bell8 5
T 5
cnot bell6 5
T* 5
cnot bell8 5
H 5
cnot bell4 6
cnot 5 6
T* 6
cnot bell4 6
T 6
cnot 5 6
H 6
cnot 4 7
H bell10
cnot bell10 bell11
cnot 6 bell11
measure bell11
cnot bell11 bell10
cnot bell10 7
T* 7
cnot 4 7
T 7
cnot bell10 7
H bell10
measure bell10
cz bell10 6
H 7
T* 6
cnot bell0 6
T 6
cnot bell0 6
H bell0
measure bell0
cz bell0 4
H 6
cnot bell4 5
cnot 6 5
T 5
cnot bell4 5
T* 5
cnot 6 5
H 5
T* 5
cnot bell6 5
T 5
cnot bell8 5
T* 5
cnot bell6 5
H bell6
measure bell6
cz bell6 1
T 5
cnot bell8 5
H bell8
measure bell8
cz bell8 2
H 5
cnot bell4 6
cnot 5 6
T* 6
cnot bell4 6
T 6
cnot 5 6
H 6
T* 5
cnot bell4 5
T 5
cnot bell4 5
H bell4
measure bell4
cz bell4 3
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
END
