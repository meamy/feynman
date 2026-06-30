# Hyperedge cut (ebits): 7

# Actual ebits used (Synthesis): 7
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_5.qc):
#   Qubits: 9
#   H: 14
#   T: 84
#   cnot: 72
#   Depth: 91
#   T depth: 37
# Result (16.736ms):
#   Qubits: 23
#   H: 28
#   T: 40
#   cnot: 75
#   cz: 7
#   measure: 14
#   reset: 14
#   Depth: 102
#   T depth: 34


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 bell0 bell1 bell10 bell11 bell12 bell13 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i 1 2 3 4 5 6 7 8 9
.o 1 2 3 4 5 6 7 8 9
BEGIN 
H 9
T 8
H bell0
cnot bell0 bell1
cnot 5 bell1
measure bell1
cnot bell1 bell0
cnot bell0 8
T* 8
H bell2
cnot bell2 bell3
cnot 9 bell3
measure bell3
cnot bell3 bell2
cnot bell2 8
T 8
cnot bell0 8
T* 8
cnot bell2 8
H bell2
measure bell2
cz bell2 9
H 8
T 7
H bell4
cnot bell4 bell5
cnot 4 bell5
measure bell5
cnot bell5 bell4
cnot bell4 7
T* 7
cnot 8 7
T 7
cnot bell4 7
T* 7
cnot 8 7
H 7
T 6
H bell6
cnot bell6 bell7
cnot 3 bell7
measure bell7
cnot bell7 bell6
cnot bell6 6
T* 6
cnot 7 6
T 6
cnot bell6 6
T* 6
cnot 7 6
H 6
T 6
H bell8
cnot bell8 bell9
cnot 1 bell9
measure bell9
cnot bell9 bell8
cnot bell8 6
T* 6
H bell10
cnot bell10 bell11
cnot 2 bell11
measure bell11
cnot bell11 bell10
cnot bell10 6
T 6
cnot bell8 6
T* 6
cnot bell10 6
H 6
cnot bell6 7
cnot 6 7
T* 7
cnot bell6 7
T 7
cnot 6 7
H 7
cnot bell4 8
cnot 7 8
T* 8
cnot bell4 8
T 8
cnot 7 8
H 8
cnot 5 9
H bell12
cnot bell12 bell13
cnot 8 bell13
measure bell13
cnot bell13 bell12
cnot bell12 9
T* 9
cnot 5 9
T 9
cnot bell12 9
H bell12
measure bell12
cz bell12 8
H 9
T* 8
cnot bell0 8
T 8
cnot bell0 8
H bell0
measure bell0
cz bell0 5
H 8
cnot bell4 7
cnot 8 7
T 7
cnot bell4 7
T* 7
cnot 8 7
H 7
cnot bell6 6
cnot 7 6
T 6
cnot bell6 6
T* 6
cnot 7 6
H 6
T* 6
cnot bell8 6
T 6
cnot bell10 6
T* 6
cnot bell8 6
H bell8
measure bell8
cz bell8 1
T 6
cnot bell10 6
H bell10
measure bell10
cz bell10 2
H 6
cnot bell6 7
cnot 6 7
T* 7
cnot bell6 7
T 7
cnot 6 7
H 7
cnot bell4 8
cnot 7 8
T* 8
cnot bell4 8
T 8
cnot 7 8
H 8
T* 6
cnot bell6 6
T 6
T* 7
cnot bell4 7
T 7
cnot bell4 7
H bell4
measure bell4
cz bell4 4
cnot bell6 6
H bell6
measure bell6
cz bell6 3
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
