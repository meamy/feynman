# Hyperedge cut (ebits): 11

# Actual ebits used (Synthesis): 17
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_5.qc):
#   Qubits: 9
#   H: 14
#   T: 84
#   cnot: 72
#   Depth: 91
#   T depth: 37
# Result (13.598ms):
#   Qubits: 43
#   H: 48
#   T: 40
#   cnot: 105
#   cz: 17
#   measure: 34
#   reset: 34
#   Depth: 117
#   T depth: 34


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell4 bell5 bell6 bell7 bell8 bell9
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
H bell0
measure bell0
cz bell0 5
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
H bell6
cnot bell6 bell7
cnot 8 bell7
measure bell7
cnot bell7 bell6
cnot bell6 7
T 7
cnot bell4 7
H bell4
measure bell4
cz bell4 4
T* 7
cnot bell6 7
H bell6
measure bell6
cz bell6 8
H 7
T 6
H bell8
cnot bell8 bell9
cnot 3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 6
T* 6
cnot 7 6
T 6
cnot bell8 6
T* 6
cnot 7 6
H 6
T 6
H bell10
cnot bell10 bell11
cnot 1 bell11
measure bell11
cnot bell11 bell10
cnot bell10 6
T* 6
H bell12
cnot bell12 bell13
cnot 2 bell13
measure bell13
cnot bell13 bell12
cnot bell12 6
T 6
cnot bell10 6
T* 6
cnot bell12 6
H 6
cnot bell8 7
cnot 6 7
T* 7
cnot bell8 7
T 7
cnot 6 7
H 7
H bell14
cnot bell14 bell15
cnot 4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 8
H bell16
cnot bell16 bell17
cnot 7 bell17
measure bell17
cnot bell17 bell16
cnot bell16 8
T* 8
cnot bell14 8
H bell14
measure bell14
cz bell14 4
T 8
cnot bell16 8
H bell16
measure bell16
cz bell16 7
H 8
H bell18
cnot bell18 bell19
cnot 5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 9
H bell20
cnot bell20 bell21
cnot 8 bell21
measure bell21
cnot bell21 bell20
cnot bell20 9
T* 9
cnot bell18 9
H bell18
measure bell18
cz bell18 5
T 9
cnot bell20 9
H bell20
measure bell20
cz bell20 8
H 9
T* 8
H bell22
cnot bell22 bell23
cnot 5 bell23
measure bell23
cnot bell23 bell22
cnot bell22 8
T 8
cnot bell22 8
H bell22
measure bell22
cz bell22 5
H 8
H bell24
cnot bell24 bell25
cnot 4 bell25
measure bell25
cnot bell25 bell24
cnot bell24 7
H bell26
cnot bell26 bell27
cnot 8 bell27
measure bell27
cnot bell27 bell26
cnot bell26 7
T 7
cnot bell24 7
H bell24
measure bell24
cz bell24 4
T* 7
cnot bell26 7
H bell26
measure bell26
cz bell26 8
H 7
cnot bell8 6
cnot 7 6
T 6
cnot bell8 6
T* 6
cnot 7 6
H 6
T* 6
cnot bell10 6
T 6
cnot bell12 6
T* 6
cnot bell10 6
H bell10
measure bell10
cz bell10 1
T 6
cnot bell12 6
H bell12
measure bell12
cz bell12 2
H 6
cnot bell8 7
cnot 6 7
T* 7
cnot bell8 7
T 7
cnot 6 7
H 7
H bell28
cnot bell28 bell29
cnot 4 bell29
measure bell29
cnot bell29 bell28
cnot bell28 8
H bell30
cnot bell30 bell31
cnot 7 bell31
measure bell31
cnot bell31 bell30
cnot bell30 8
T* 8
cnot bell28 8
H bell28
measure bell28
cz bell28 4
T 8
cnot bell30 8
H bell30
measure bell30
cz bell30 7
H 8
T* 6
cnot bell8 6
T 6
T* 7
H bell32
cnot bell32 bell33
cnot 4 bell33
measure bell33
cnot bell33 bell32
cnot bell32 7
T 7
cnot bell32 7
H bell32
measure bell32
cz bell32 4
cnot bell8 6
H bell8
measure bell8
cz bell8 3
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
reset bell32
reset bell33
END
