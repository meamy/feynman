# Hyperedge cut (ebits): 9

# Actual ebits used (Synthesis): 13
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/vbe_adder_3.qc):
#   Qubits: 10
#   H: 10
#   T: 70
#   cnot: 70
#   Depth: 70
#   T depth: 29
# Result (12.367ms):
#   Qubits: 36
#   H: 36
#   S: 6
#   T: 24
#   cnot: 85
#   cz: 13
#   measure: 26
#   reset: 26
#   Depth: 84
#   T depth: 17


# Result Circuit
.v 0 1 2 3 4 5 6 7 8 9 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i 0 1 2 3 4 5 6 7 8 9
.o 0 1 2 3 4 5 6 7 8 9
BEGIN 
H 3
H 6
H 9
H bell0
cnot bell0 bell1
cnot 1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 3
T* 3
cnot 2 3
S 3
cnot bell0 3
T* 3
H bell2
cnot bell2 bell3
cnot 0 bell3
measure bell3
cnot bell3 bell2
cnot bell2 3
cnot bell0 3
T* 3
cnot 2 3
cnot bell0 3
T 3
cnot bell2 3
cnot bell0 2
H 3
H bell4
cnot bell4 bell5
cnot 4 bell5
measure bell5
cnot bell5 bell4
cnot bell4 6
T* 6
H bell6
cnot bell6 bell7
cnot 5 bell7
measure bell7
cnot bell7 bell6
cnot bell6 6
S 6
cnot bell4 6
T* 6
H bell8
cnot bell8 bell9
cnot 3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 6
cnot bell4 6
T* 6
cnot bell6 6
H bell6
measure bell6
cz bell6 5
cnot bell4 6
H bell4
measure bell4
cz bell4 4
T 6
H bell10
cnot bell10 bell11
cnot 4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 5
H bell10
measure bell10
cz bell10 4
cnot bell8 6
H 6
H bell12
cnot bell12 bell13
cnot 7 bell13
measure bell13
cnot bell13 bell12
cnot bell12 9
T* 9
cnot 8 9
S 9
cnot bell12 9
T* 9
H bell14
cnot bell14 bell15
cnot 6 bell15
measure bell15
cnot bell15 bell14
cnot bell14 9
cnot bell12 9
T* 9
cnot 8 9
cnot bell12 9
T 9
cnot bell12 8
H bell12
measure bell12
cz bell12 7
cnot bell14 8
cnot bell14 9
H bell14
measure bell14
cz bell14 6
H 9
T* 6
H bell16
cnot bell16 bell17
cnot 8 bell17
measure bell17
cnot bell17 bell16
cnot bell16 6
S* 6
H bell18
cnot bell18 bell19
cnot 7 bell19
measure bell19
cnot bell19 bell18
cnot bell18 6
T 6
cnot bell16 6
H bell16
measure bell16
cz bell16 8
cnot bell18 6
H bell18
measure bell18
cz bell18 7
H 6
cnot bell8 6
T* 6
H bell20
cnot bell20 bell21
cnot 5 bell21
measure bell21
cnot bell21 bell20
cnot bell20 6
T 6
cnot bell8 6
H bell8
measure bell8
cz bell8 3
S* 6
H bell22
cnot bell22 bell23
cnot 4 bell23
measure bell23
cnot bell23 bell22
cnot bell22 6
T 6
cnot bell20 6
H bell20
measure bell20
cz bell20 5
T 6
cnot bell22 6
H bell22
measure bell22
cz bell22 4
H bell24
cnot bell24 bell25
cnot 3 bell25
measure bell25
cnot bell25 bell24
cnot bell24 5
H bell24
measure bell24
cz bell24 3
H 6
H 3
cnot bell2 3
T* 3
cnot 2 3
T 3
cnot bell2 3
S* 3
cnot bell0 3
T 3
cnot 2 3
T 3
cnot bell0 3
H bell0
measure bell0
cz bell0 1
H 3
T 7
T 8
cnot bell2 2
H bell2
measure bell2
cz bell2 0
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
END
