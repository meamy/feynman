# Hyperedge cut (ebits): 8

# Actual ebits used (Synthesis): 8
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_10.qc):
#   Qubits: 19
#   H: 34
#   T: 119
#   cnot: 102
#   Depth: 128
#   T depth: 52
# Result (30.003ms):
#   Qubits: 35
#   H: 50
#   T: 71
#   cnot: 94
#   cz: 8
#   measure: 16
#   reset: 16
#   Depth: 176
#   T depth: 54


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
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
H bell0
cnot bell0 bell1
cnot 11 bell1
measure bell1
cnot bell1 bell0
cnot bell0 12
T* 12
cnot 3 12
T 12
cnot bell0 12
T* 12
cnot 3 12
H 12
H 13
T 13
H bell2
cnot bell2 bell3
cnot 12 bell3
measure bell3
cnot bell3 bell2
cnot bell2 13
T* 13
cnot 4 13
T 13
cnot bell2 13
T* 13
cnot 4 13
H 13
H 14
T 14
H bell4
cnot bell4 bell5
cnot 13 bell5
measure bell5
cnot bell5 bell4
cnot bell4 14
T* 14
cnot 5 14
T 14
cnot bell4 14
T* 14
cnot 5 14
H 14
H 15
T 15
H bell6
cnot bell6 bell7
cnot 14 bell7
measure bell7
cnot bell7 bell6
cnot bell6 15
T* 15
cnot 6 15
T 15
cnot bell6 15
T* 15
cnot 6 15
H 15
H 16
T 16
H bell8
cnot bell8 bell9
cnot 15 bell9
measure bell9
cnot bell9 bell8
cnot bell8 16
T* 16
cnot 7 16
T 16
cnot bell8 16
T* 16
cnot 7 16
H 16
H 17
T 17
H bell10
cnot bell10 bell11
cnot 16 bell11
measure bell11
cnot bell11 bell10
cnot bell10 17
T* 17
cnot 8 17
T 17
cnot bell10 17
T* 17
cnot 8 17
H 17
H 18
T 18
H bell12
cnot bell12 bell13
cnot 17 bell13
measure bell13
cnot bell13 bell12
cnot bell12 18
T* 18
cnot 9 18
T 18
cnot bell12 18
T* 18
cnot 9 18
H 18
H 19
T 19
H bell14
cnot bell14 bell15
cnot 10 bell15
measure bell15
cnot bell15 bell14
cnot bell14 19
T* 19
cnot 18 19
T 19
cnot bell14 19
T* 19
cnot 18 19
H 19
T 18
cnot bell14 18
T* 18
cnot bell14 18
H bell14
measure bell14
cz bell14 10
H 18
T* 18
cnot bell12 18
T 18
cnot 9 18
T* 18
cnot bell12 18
H bell12
measure bell12
cz bell12 17
T 18
cnot 9 18
H 18
H 17
T* 17
cnot bell10 17
T 17
cnot 8 17
T* 17
cnot bell10 17
H bell10
measure bell10
cz bell10 16
T 17
cnot 8 17
H 17
H 16
T* 16
cnot bell8 16
T 16
cnot 7 16
T* 16
cnot bell8 16
H bell8
measure bell8
cz bell8 15
T 16
cnot 7 16
H 16
H 15
T* 15
cnot bell6 15
T 15
cnot 6 15
T* 15
cnot bell6 15
H bell6
measure bell6
cz bell6 14
T 15
cnot 6 15
H 15
H 14
T* 14
cnot bell4 14
T 14
cnot 5 14
T* 14
cnot bell4 14
H bell4
measure bell4
cz bell4 13
T 14
cnot 5 14
H 14
H 13
T* 13
cnot bell2 13
T 13
cnot 4 13
T* 13
cnot bell2 13
H bell2
measure bell2
cz bell2 12
T 13
cnot 4 13
H 13
H 12
T* 12
cnot bell0 12
T 12
cnot 3 12
T* 12
cnot bell0 12
H bell0
measure bell0
cz bell0 11
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
reset bell8
reset bell9
reset bell10
reset bell11
reset bell12
reset bell13
reset bell14
reset bell15
END
