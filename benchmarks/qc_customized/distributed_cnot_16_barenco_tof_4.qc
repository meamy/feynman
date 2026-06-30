# Hyperedge cut (ebits): 10

# Actual ebits used (Synthesis): 16
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_4.qc):
#   Qubits: 7
#   H: 10
#   T: 56
#   cnot: 48
#   Depth: 61
#   T depth: 25
# Result (11.016ms):
#   Qubits: 39
#   H: 42
#   T: 28
#   cnot: 84
#   cz: 16
#   measure: 32
#   reset: 32
#   Depth: 93
#   T depth: 26


# Result Circuit
.v 1 2 3 4 5 6 7 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell4 bell5 bell6 bell7 bell8 bell9
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
H bell0
measure bell0
cz bell0 4
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
H bell6
cnot bell6 bell7
cnot 6 bell7
measure bell7
cnot bell7 bell6
cnot bell6 5
T 5
cnot bell4 5
H bell4
measure bell4
cz bell4 3
T* 5
cnot bell6 5
H bell6
measure bell6
cz bell6 6
H 5
T 5
H bell8
cnot bell8 bell9
cnot 1 bell9
measure bell9
cnot bell9 bell8
cnot bell8 5
T* 5
H bell10
cnot bell10 bell11
cnot 2 bell11
measure bell11
cnot bell11 bell10
cnot bell10 5
T 5
cnot bell8 5
T* 5
cnot bell10 5
H 5
H bell12
cnot bell12 bell13
cnot 3 bell13
measure bell13
cnot bell13 bell12
cnot bell12 6
H bell14
cnot bell14 bell15
cnot 5 bell15
measure bell15
cnot bell15 bell14
cnot bell14 6
T* 6
cnot bell12 6
H bell12
measure bell12
cz bell12 3
T 6
cnot bell14 6
H bell14
measure bell14
cz bell14 5
H 6
H bell16
cnot bell16 bell17
cnot 4 bell17
measure bell17
cnot bell17 bell16
cnot bell16 7
H bell18
cnot bell18 bell19
cnot 6 bell19
measure bell19
cnot bell19 bell18
cnot bell18 7
T* 7
cnot bell16 7
H bell16
measure bell16
cz bell16 4
T 7
cnot bell18 7
H bell18
measure bell18
cz bell18 6
H 7
T* 6
H bell20
cnot bell20 bell21
cnot 4 bell21
measure bell21
cnot bell21 bell20
cnot bell20 6
T 6
cnot bell20 6
H bell20
measure bell20
cz bell20 4
H 6
H bell22
cnot bell22 bell23
cnot 3 bell23
measure bell23
cnot bell23 bell22
cnot bell22 5
H bell24
cnot bell24 bell25
cnot 6 bell25
measure bell25
cnot bell25 bell24
cnot bell24 5
T 5
cnot bell22 5
H bell22
measure bell22
cz bell22 3
T* 5
cnot bell24 5
H bell24
measure bell24
cz bell24 6
H 5
T* 5
cnot bell8 5
T 5
cnot bell10 5
T* 5
cnot bell8 5
H bell8
measure bell8
cz bell8 1
T 5
cnot bell10 5
H bell10
measure bell10
cz bell10 2
H 5
H bell26
cnot bell26 bell27
cnot 3 bell27
measure bell27
cnot bell27 bell26
cnot bell26 6
H bell28
cnot bell28 bell29
cnot 5 bell29
measure bell29
cnot bell29 bell28
cnot bell28 6
T* 6
cnot bell26 6
H bell26
measure bell26
cz bell26 3
T 6
cnot bell28 6
H bell28
measure bell28
cz bell28 5
H 6
T* 5
H bell30
cnot bell30 bell31
cnot 3 bell31
measure bell31
cnot bell31 bell30
cnot bell30 5
T 5
cnot bell30 5
H bell30
measure bell30
cz bell30 3
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
reset bell18
reset bell19
reset bell20
reset bell21
reset bell22
reset bell23
reset bell24
reset bell25
reset bell26
reset bell27
reset bell28
reset bell29
reset bell30
reset bell31
END
