# Hyperedge cut (ebits): 16

# Actual ebits used (Synthesis): 16
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_10.qc):
#   Qubits: 19
#   H: 34
#   T: 224
#   cnot: 192
#   Depth: 241
#   T depth: 97
# Result (37.867ms):
#   Qubits: 51
#   H: 66
#   T: 100
#   cnot: 192
#   cz: 16
#   measure: 32
#   reset: 32
#   Depth: 278
#   T depth: 81


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell4 bell5 bell6 bell7 bell8 bell9
.i 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
.o 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
BEGIN 
H 19
T 18
cnot 10 18
T* 18
cnot 19 18
T 18
cnot 10 18
T* 18
cnot 19 18
H 18
T 17
cnot 18 17
T* 17
cnot 9 17
T 17
cnot 18 17
T* 17
cnot 9 17
H 17
T 16
H bell0
cnot bell0 bell1
cnot 17 bell1
measure bell1
cnot bell1 bell0
cnot bell0 16
T* 16
cnot 8 16
T 16
cnot bell0 16
H bell0
measure bell0
cz bell0 17
T* 16
cnot 8 16
H 16
T 15
cnot 16 15
T* 15
cnot 7 15
T 15
cnot 16 15
T* 15
cnot 7 15
H 15
T 14
H bell2
cnot bell2 bell3
cnot 15 bell3
measure bell3
cnot bell3 bell2
cnot bell2 14
T* 14
cnot 6 14
T 14
cnot bell2 14
H bell2
measure bell2
cz bell2 15
T* 14
cnot 6 14
H 14
T 13
cnot 14 13
T* 13
cnot 5 13
T 13
cnot 14 13
T* 13
cnot 5 13
H 13
T 12
H bell4
cnot bell4 bell5
cnot 13 bell5
measure bell5
cnot bell5 bell4
cnot bell4 12
T* 12
H bell6
cnot bell6 bell7
cnot 4 bell7
measure bell7
cnot bell7 bell6
cnot bell6 12
T 12
cnot bell4 12
H bell4
measure bell4
cz bell4 13
T* 12
cnot bell6 12
H 12
T 11
cnot 12 11
T* 11
cnot 3 11
T 11
cnot 12 11
T* 11
cnot 3 11
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
cnot 11 12
T 12
cnot 3 12
T* 12
cnot 11 12
cnot 3 12
H 12
H bell8
cnot bell8 bell9
cnot 12 bell9
measure bell9
cnot bell9 bell8
cnot bell8 13
T 13
cnot 4 13
T* 13
cnot bell8 13
H bell8
measure bell8
cz bell8 12
cnot 4 13
H 13
cnot 13 14
T 14
cnot 5 14
T* 14
cnot 13 14
cnot 5 14
H 14
H bell10
cnot bell10 bell11
cnot 14 bell11
measure bell11
cnot bell11 bell10
cnot bell10 15
T 15
H bell12
cnot bell12 bell13
cnot 6 bell13
measure bell13
cnot bell13 bell12
cnot bell12 15
T* 15
cnot bell10 15
H bell10
measure bell10
cz bell10 14
cnot bell12 15
H 15
cnot 15 16
T 16
cnot 7 16
T* 16
cnot 15 16
cnot 7 16
H 16
H bell14
cnot bell14 bell15
cnot 16 bell15
measure bell15
cnot bell15 bell14
cnot bell14 17
T 17
H bell16
cnot bell16 bell17
cnot 8 bell17
measure bell17
cnot bell17 bell16
cnot bell16 17
T* 17
cnot bell14 17
H bell14
measure bell14
cz bell14 16
cnot bell16 17
H 17
cnot 17 18
T 18
cnot 9 18
T* 18
cnot 17 18
cnot 9 18
H 18
cnot 10 19
cnot 18 19
T* 19
cnot 10 19
T 19
cnot 18 19
H 19
T* 18
cnot 10 18
T 18
cnot 10 18
H 18
cnot 18 17
T* 17
cnot 9 17
T 17
cnot 18 17
cnot 9 17
H 17
H bell18
cnot bell18 bell19
cnot 17 bell19
measure bell19
cnot bell19 bell18
cnot bell18 16
T* 16
cnot 8 16
T 16
cnot bell18 16
H bell18
measure bell18
cz bell18 17
cnot 8 16
H 16
cnot 16 15
T* 15
cnot 7 15
T 15
cnot 16 15
cnot 7 15
H 15
H bell20
cnot bell20 bell21
cnot 15 bell21
measure bell21
cnot bell21 bell20
cnot bell20 14
T* 14
cnot 6 14
T 14
cnot bell20 14
H bell20
measure bell20
cz bell20 15
cnot 6 14
H 14
cnot 14 13
T* 13
cnot 5 13
T 13
cnot 14 13
cnot 5 13
H 13
H bell22
cnot bell22 bell23
cnot 13 bell23
measure bell23
cnot bell23 bell22
cnot bell22 12
T* 12
cnot bell6 12
T 12
cnot bell22 12
H bell22
measure bell22
cz bell22 13
cnot bell6 12
H bell6
measure bell6
cz bell6 4
H 12
cnot 12 11
T* 11
cnot 3 11
T 11
cnot 12 11
cnot 3 11
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
cnot 11 12
T 12
cnot 3 12
T* 12
cnot 11 12
cnot 3 12
H 12
H bell24
cnot bell24 bell25
cnot 12 bell25
measure bell25
cnot bell25 bell24
cnot bell24 13
T 13
cnot 4 13
T* 13
cnot bell24 13
H bell24
measure bell24
cz bell24 12
cnot 4 13
H 13
cnot 13 14
T 14
cnot 5 14
T* 14
cnot 13 14
cnot 5 14
H 14
H bell26
cnot bell26 bell27
cnot 14 bell27
measure bell27
cnot bell27 bell26
cnot bell26 15
T 15
cnot bell12 15
T* 15
cnot bell26 15
H bell26
measure bell26
cz bell26 14
cnot bell12 15
H bell12
measure bell12
cz bell12 6
H 15
cnot 15 16
T 16
cnot 7 16
T* 16
cnot 15 16
cnot 7 16
H 16
H bell28
cnot bell28 bell29
cnot 16 bell29
measure bell29
cnot bell29 bell28
cnot bell28 17
T 17
cnot bell16 17
T* 17
cnot bell28 17
H bell28
measure bell28
cz bell28 16
cnot bell16 17
H bell16
measure bell16
cz bell16 8
H 17
cnot 17 18
T 18
cnot 9 18
T* 18
cnot 17 18
cnot 9 18
H 18
T* 11
cnot 11 3
T 3
T* 12
H bell30
cnot bell30 bell31
cnot 12 bell31
measure bell31
cnot bell31 bell30
cnot bell30 4
T 4
T* 13
cnot 13 5
T 5
T* 14
cnot 14 6
T 6
T* 15
cnot 15 7
T 7
T* 16
cnot 16 8
T 8
T* 17
cnot 17 9
T 9
cnot 17 9
cnot 16 8
cnot 15 7
cnot 14 6
cnot 13 5
cnot bell30 4
H bell30
measure bell30
cz bell30 12
cnot 11 3
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
