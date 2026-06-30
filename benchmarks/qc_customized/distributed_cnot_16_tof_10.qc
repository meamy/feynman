# Hyperedge cut (ebits): 15

# Actual ebits used (Synthesis): 15
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_10.qc):
#   Qubits: 19
#   H: 34
#   T: 119
#   cnot: 102
#   Depth: 128
#   T depth: 52
# Result (32.426ms):
#   Qubits: 49
#   H: 64
#   T: 71
#   cnot: 115
#   cz: 15
#   measure: 30
#   reset: 30
#   Depth: 174
#   T depth: 54


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i 1 2 3 4 5 6 7 8 9 10 19
.o 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
BEGIN 
H 11
T 11
H bell0
cnot bell0 bell1
cnot 1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 11
T* 11
cnot 2 11
T 11
cnot bell0 11
T* 11
cnot 2 11
H 11
H 12
T 12
H bell2
cnot bell2 bell3
cnot 11 bell3
measure bell3
cnot bell3 bell2
cnot bell2 12
T* 12
H bell4
cnot bell4 bell5
cnot 3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 12
T 12
cnot bell2 12
T* 12
cnot bell4 12
H 12
H 13
T 13
H bell6
cnot bell6 bell7
cnot 12 bell7
measure bell7
cnot bell7 bell6
cnot bell6 13
T* 13
H bell8
cnot bell8 bell9
cnot 4 bell9
measure bell9
cnot bell9 bell8
cnot bell8 13
T 13
cnot bell6 13
T* 13
cnot bell8 13
H 13
H 14
T 14
H bell10
cnot bell10 bell11
cnot 13 bell11
measure bell11
cnot bell11 bell10
cnot bell10 14
T* 14
H bell12
cnot bell12 bell13
cnot 5 bell13
measure bell13
cnot bell13 bell12
cnot bell12 14
T 14
cnot bell10 14
T* 14
cnot bell12 14
H 14
H 15
T 15
H bell14
cnot bell14 bell15
cnot 14 bell15
measure bell15
cnot bell15 bell14
cnot bell14 15
T* 15
H bell16
cnot bell16 bell17
cnot 6 bell17
measure bell17
cnot bell17 bell16
cnot bell16 15
T 15
cnot bell14 15
T* 15
cnot bell16 15
H 15
H 16
T 16
cnot 15 16
T* 16
H bell18
cnot bell18 bell19
cnot 7 bell19
measure bell19
cnot bell19 bell18
cnot bell18 16
T 16
cnot 15 16
T* 16
cnot bell18 16
H 16
H 17
T 17
H bell20
cnot bell20 bell21
cnot 16 bell21
measure bell21
cnot bell21 bell20
cnot bell20 17
T* 17
H bell22
cnot bell22 bell23
cnot 8 bell23
measure bell23
cnot bell23 bell22
cnot bell22 17
T 17
cnot bell20 17
T* 17
cnot bell22 17
H 17
H 18
T 18
H bell24
cnot bell24 bell25
cnot 17 bell25
measure bell25
cnot bell25 bell24
cnot bell24 18
T* 18
H bell26
cnot bell26 bell27
cnot 9 bell27
measure bell27
cnot bell27 bell26
cnot bell26 18
T 18
cnot bell24 18
T* 18
cnot bell26 18
H 18
H 19
T 19
H bell28
cnot bell28 bell29
cnot 10 bell29
measure bell29
cnot bell29 bell28
cnot bell28 19
T* 19
cnot 18 19
T 19
cnot bell28 19
T* 19
cnot 18 19
H 19
T 18
cnot bell28 18
T* 18
cnot bell28 18
H bell28
measure bell28
cz bell28 10
H 18
T* 18
cnot bell24 18
T 18
cnot bell26 18
T* 18
cnot bell24 18
H bell24
measure bell24
cz bell24 17
T 18
cnot bell26 18
H bell26
measure bell26
cz bell26 9
H 18
H 17
T* 17
cnot bell20 17
T 17
cnot bell22 17
T* 17
cnot bell20 17
H bell20
measure bell20
cz bell20 16
T 17
cnot bell22 17
H bell22
measure bell22
cz bell22 8
H 17
H 16
T* 16
cnot 15 16
T 16
cnot bell18 16
T* 16
cnot 15 16
T 16
cnot bell18 16
H bell18
measure bell18
cz bell18 7
H 16
H 15
T* 15
cnot bell14 15
T 15
cnot bell16 15
T* 15
cnot bell14 15
H bell14
measure bell14
cz bell14 14
T 15
cnot bell16 15
H bell16
measure bell16
cz bell16 6
H 15
H 14
T* 14
cnot bell10 14
T 14
cnot bell12 14
T* 14
cnot bell10 14
H bell10
measure bell10
cz bell10 13
T 14
cnot bell12 14
H bell12
measure bell12
cz bell12 5
H 14
H 13
T* 13
cnot bell6 13
T 13
cnot bell8 13
T* 13
cnot bell6 13
H bell6
measure bell6
cz bell6 12
T 13
cnot bell8 13
H bell8
measure bell8
cz bell8 4
H 13
H 12
T* 12
cnot bell2 12
T 12
cnot bell4 12
T* 12
cnot bell2 12
H bell2
measure bell2
cz bell2 11
T 12
cnot bell4 12
H bell4
measure bell4
cz bell4 3
H 12
H 11
T* 11
cnot bell0 11
T 11
cnot 2 11
T* 11
cnot bell0 11
H bell0
measure bell0
cz bell0 1
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
END
