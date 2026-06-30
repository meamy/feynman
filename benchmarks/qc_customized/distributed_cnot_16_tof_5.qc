# Hyperedge cut (ebits): 8

# Actual ebits used (Synthesis): 9
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_5.qc):
#   Qubits: 9
#   H: 14
#   T: 49
#   cnot: 42
#   Depth: 53
#   T depth: 22
# Result (11.513ms):
#   Qubits: 27
#   H: 32
#   T: 31
#   cnot: 57
#   cz: 9
#   measure: 18
#   reset: 18
#   Depth: 83
#   T depth: 24


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i 1 2 3 4 5 9
.o 1 2 3 4 5 6 7 8 9
BEGIN 
H 6
T 6
H bell0
cnot bell0 bell1
cnot 1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 6
T* 6
H bell2
cnot bell2 bell3
cnot 2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 6
T 6
cnot bell0 6
T* 6
cnot bell2 6
H 6
H 7
T 7
H bell4
cnot bell4 bell5
cnot 3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 7
T* 7
H bell6
cnot bell6 bell7
cnot 6 bell7
measure bell7
cnot bell7 bell6
cnot bell6 7
T 7
cnot bell4 7
T* 7
cnot bell6 7
H 7
H 8
T 8
H bell8
cnot bell8 bell9
cnot 4 bell9
measure bell9
cnot bell9 bell8
cnot bell8 8
T* 8
H bell10
cnot bell10 bell11
cnot 7 bell11
measure bell11
cnot bell11 bell10
cnot bell10 8
T 8
cnot bell8 8
T* 8
cnot bell10 8
H 8
H 9
T 9
H bell12
cnot bell12 bell13
cnot 5 bell13
measure bell13
cnot bell13 bell12
cnot bell12 9
T* 9
H bell14
cnot bell14 bell15
cnot 8 bell15
measure bell15
cnot bell15 bell14
cnot bell14 9
T 9
cnot bell12 9
H bell12
measure bell12
cz bell12 5
T* 9
cnot bell14 9
H bell14
measure bell14
cz bell14 8
H 9
T 8
H bell16
cnot bell16 bell17
cnot 5 bell17
measure bell17
cnot bell17 bell16
cnot bell16 8
T* 8
cnot bell16 8
H bell16
measure bell16
cz bell16 5
H 8
T* 8
cnot bell8 8
T 8
cnot bell10 8
T* 8
cnot bell8 8
H bell8
measure bell8
cz bell8 4
T 8
cnot bell10 8
H bell10
measure bell10
cz bell10 7
H 8
H 7
T* 7
cnot bell4 7
T 7
cnot bell6 7
T* 7
cnot bell4 7
H bell4
measure bell4
cz bell4 3
T 7
cnot bell6 7
H bell6
measure bell6
cz bell6 6
H 7
H 6
T* 6
cnot bell0 6
T 6
cnot bell2 6
T* 6
cnot bell0 6
H bell0
measure bell0
cz bell0 1
T 6
cnot bell2 6
H bell2
measure bell2
cz bell2 2
H 6
T 5
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
reset bell16
reset bell17
END
