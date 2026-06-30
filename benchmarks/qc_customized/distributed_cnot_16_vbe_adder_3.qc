# Hyperedge cut (ebits): 14

# Actual ebits used (Synthesis): 21
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/vbe_adder_3.qc):
#   Qubits: 10
#   H: 10
#   T: 70
#   cnot: 70
#   Depth: 70
#   T depth: 29
# Result (12.923ms):
#   Qubits: 52
#   H: 52
#   S: 6
#   T: 24
#   cnot: 111
#   cz: 22
#   measure: 42
#   reset: 43
#   Depth: 96
#   T depth: 17


# Result Circuit
.v 0 1 2 3 4 5 6 7 8 9 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell5 bell6 bell7 bell8 bell9
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
H bell2
cnot bell2 bell3
cnot 2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 3
S 3
cnot bell0 3
T* 3
H bell4
cnot bell4 bell5
cnot 0 bell5
measure bell5
cnot bell5 bell4
cnot bell4 3
cnot bell0 3
T* 3
cnot bell2 3
H bell2
measure bell2
cz bell2 2
cnot bell0 3
H bell0
measure bell0
cz bell0 1
T 3
cnot bell4 3
H bell6
cnot bell6 bell7
cnot 1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 2
H bell6
measure bell6
cz bell6 1
H 3
H bell8
cnot bell8 bell9
cnot 4 bell9
measure bell9
cnot bell9 bell8
cnot bell8 6
T* 6
H bell10
cnot bell10 bell11
cnot 5 bell11
measure bell11
cnot bell11 bell10
cnot bell10 6
S 6
cnot bell8 6
T* 6
H bell12
cnot bell12 bell13
cnot 3 bell13
measure bell13
cnot bell13 bell12
cnot bell12 6
cnot bell8 6
T* 6
cnot bell10 6
H bell10
measure bell10
cz bell10 5
cnot bell8 6
H bell8
measure bell8
cz bell8 4
T 6
H bell14
cnot bell14 bell15
cnot 4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 5
H bell14
measure bell14
cz bell14 4
cnot bell12 6
H 6
H bell16
cnot bell16 bell17
cnot 7 bell17
measure bell17
cnot bell17 bell16
cnot bell16 9
T* 9
H bell18
cnot bell18 bell19
cnot 8 bell19
measure bell19
cnot bell19 bell18
cnot bell18 9
S 9
cnot bell16 9
T* 9
H bell20
cnot bell20 bell21
cnot 6 bell21
measure bell21
cnot bell21 bell20
cnot bell20 9
cnot bell16 9
T* 9
cnot bell18 9
H bell18
measure bell18
cz bell18 8
cnot bell16 9
T 9
H bell22
cnot bell22 bell23
cnot 8 bell23
measure bell23
cnot bell23 bell22
cnot bell16 bell22
H bell16
measure bell16
cz bell16 7
cnot bell20 bell22
H bell24
cnot bell24 bell25
cnot bell22 bell25
measure bell25
cnot bell25 bell24
reset bell25
cnot 8 bell24
cnot bell24 8
H bell24
measure bell24
cz bell24 6
cz bell24 7
H bell22
measure bell22
cz bell22 8
cnot bell20 9
H bell20
measure bell20
cz bell20 6
H 9
T* 6
H bell26
cnot bell26 bell27
cnot 8 bell27
measure bell27
cnot bell27 bell26
cnot bell26 6
S* 6
H bell28
cnot bell28 bell29
cnot 7 bell29
measure bell29
cnot bell29 bell28
cnot bell28 6
T 6
cnot bell26 6
H bell26
measure bell26
cz bell26 8
cnot bell28 6
H bell28
measure bell28
cz bell28 7
H 6
cnot bell12 6
T* 6
H bell30
cnot bell30 bell31
cnot 5 bell31
measure bell31
cnot bell31 bell30
cnot bell30 6
T 6
cnot bell12 6
H bell12
measure bell12
cz bell12 3
S* 6
H bell32
cnot bell32 bell33
cnot 4 bell33
measure bell33
cnot bell33 bell32
cnot bell32 6
T 6
cnot bell30 6
H bell30
measure bell30
cz bell30 5
T 6
cnot bell32 6
H bell32
measure bell32
cz bell32 4
H bell34
cnot bell34 bell35
cnot 3 bell35
measure bell35
cnot bell35 bell34
cnot bell34 5
H bell34
measure bell34
cz bell34 3
H 6
H 3
cnot bell4 3
T* 3
H bell36
cnot bell36 bell37
cnot 2 bell37
measure bell37
cnot bell37 bell36
cnot bell36 3
T 3
cnot bell4 3
H bell4
measure bell4
cz bell4 0
S* 3
H bell38
cnot bell38 bell39
cnot 1 bell39
measure bell39
cnot bell39 bell38
cnot bell38 3
T 3
cnot bell36 3
H bell36
measure bell36
cz bell36 2
T 3
cnot bell38 3
H bell38
measure bell38
cz bell38 1
H 3
T 7
T 8
H bell40
cnot bell40 bell41
cnot 0 bell41
measure bell41
cnot bell41 bell40
cnot bell40 2
H bell40
measure bell40
cz bell40 0
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
reset bell34
reset bell35
reset bell36
reset bell37
reset bell38
reset bell39
reset bell40
reset bell41
END
