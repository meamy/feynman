# Hyperedge cut (ebits): 23

# Actual ebits used (Synthesis): 32
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_10.qc):
#   Qubits: 19
#   H: 34
#   T: 224
#   cnot: 192
#   Depth: 241
#   T depth: 97
# Result (38.013ms):
#   Qubits: 83
#   H: 98
#   T: 100
#   cnot: 240
#   cz: 32
#   measure: 64
#   reset: 64
#   Depth: 291
#   T depth: 81


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell7 bell8 bell9
.i 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
.o 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
BEGIN 
H 19
T 18
H bell0
cnot bell0 bell1
cnot 10 bell1
measure bell1
cnot bell1 bell0
cnot bell0 18
T* 18
H bell2
cnot bell2 bell3
cnot 19 bell3
measure bell3
cnot bell3 bell2
cnot bell2 18
T 18
cnot bell0 18
T* 18
cnot bell2 18
H bell2
measure bell2
cz bell2 19
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
H bell4
cnot bell4 bell5
cnot 17 bell5
measure bell5
cnot bell5 bell4
cnot bell4 16
T* 16
H bell6
cnot bell6 bell7
cnot 8 bell7
measure bell7
cnot bell7 bell6
cnot bell6 16
T 16
cnot bell4 16
H bell4
measure bell4
cz bell4 17
T* 16
cnot bell6 16
H bell6
measure bell6
cz bell6 8
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
H bell8
cnot bell8 bell9
cnot 15 bell9
measure bell9
cnot bell9 bell8
cnot bell8 14
T* 14
H bell10
cnot bell10 bell11
cnot 6 bell11
measure bell11
cnot bell11 bell10
cnot bell10 14
T 14
cnot bell8 14
H bell8
measure bell8
cz bell8 15
T* 14
cnot bell10 14
H bell10
measure bell10
cz bell10 6
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
H bell12
cnot bell12 bell13
cnot 13 bell13
measure bell13
cnot bell13 bell12
cnot bell12 12
T* 12
H bell14
cnot bell14 bell15
cnot 4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 12
T 12
cnot bell12 12
H bell12
measure bell12
cz bell12 13
T* 12
cnot bell14 12
H bell14
measure bell14
cz bell14 4
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
H bell16
cnot bell16 bell17
cnot 1 bell17
measure bell17
cnot bell17 bell16
cnot bell16 11
T* 11
H bell18
cnot bell18 bell19
cnot 2 bell19
measure bell19
cnot bell19 bell18
cnot bell18 11
T 11
cnot bell16 11
T* 11
cnot bell18 11
H 11
cnot 11 12
T 12
cnot 3 12
T* 12
cnot 11 12
cnot 3 12
H 12
H bell20
cnot bell20 bell21
cnot 12 bell21
measure bell21
cnot bell21 bell20
cnot bell20 13
T 13
H bell22
cnot bell22 bell23
cnot 4 bell23
measure bell23
cnot bell23 bell22
cnot bell22 13
T* 13
cnot bell20 13
H bell20
measure bell20
cz bell20 12
cnot bell22 13
H bell22
measure bell22
cz bell22 4
H 13
cnot 13 14
T 14
cnot 5 14
T* 14
cnot 13 14
cnot 5 14
H 14
H bell24
cnot bell24 bell25
cnot 14 bell25
measure bell25
cnot bell25 bell24
cnot bell24 15
T 15
H bell26
cnot bell26 bell27
cnot 6 bell27
measure bell27
cnot bell27 bell26
cnot bell26 15
T* 15
cnot bell24 15
H bell24
measure bell24
cz bell24 14
cnot bell26 15
H bell26
measure bell26
cz bell26 6
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
H bell30
cnot bell30 bell31
cnot 8 bell31
measure bell31
cnot bell31 bell30
cnot bell30 17
T* 17
cnot bell28 17
H bell28
measure bell28
cz bell28 16
cnot bell30 17
H bell30
measure bell30
cz bell30 8
H 17
cnot 17 18
T 18
cnot 9 18
T* 18
cnot 17 18
cnot 9 18
H 18
cnot 10 19
H bell32
cnot bell32 bell33
cnot 18 bell33
measure bell33
cnot bell33 bell32
cnot bell32 19
T* 19
cnot 10 19
T 19
cnot bell32 19
H bell32
measure bell32
cz bell32 18
H 19
T* 18
cnot bell0 18
T 18
cnot bell0 18
H bell0
measure bell0
cz bell0 10
H 18
cnot 18 17
T* 17
cnot 9 17
T 17
cnot 18 17
cnot 9 17
H 17
H bell34
cnot bell34 bell35
cnot 17 bell35
measure bell35
cnot bell35 bell34
cnot bell34 16
T* 16
H bell36
cnot bell36 bell37
cnot 8 bell37
measure bell37
cnot bell37 bell36
cnot bell36 16
T 16
cnot bell34 16
H bell34
measure bell34
cz bell34 17
cnot bell36 16
H bell36
measure bell36
cz bell36 8
H 16
cnot 16 15
T* 15
cnot 7 15
T 15
cnot 16 15
cnot 7 15
H 15
H bell38
cnot bell38 bell39
cnot 15 bell39
measure bell39
cnot bell39 bell38
cnot bell38 14
T* 14
H bell40
cnot bell40 bell41
cnot 6 bell41
measure bell41
cnot bell41 bell40
cnot bell40 14
T 14
cnot bell38 14
H bell38
measure bell38
cz bell38 15
cnot bell40 14
H bell40
measure bell40
cz bell40 6
H 14
cnot 14 13
T* 13
cnot 5 13
T 13
cnot 14 13
cnot 5 13
H 13
H bell42
cnot bell42 bell43
cnot 13 bell43
measure bell43
cnot bell43 bell42
cnot bell42 12
T* 12
H bell44
cnot bell44 bell45
cnot 4 bell45
measure bell45
cnot bell45 bell44
cnot bell44 12
T 12
cnot bell42 12
H bell42
measure bell42
cz bell42 13
cnot bell44 12
H bell44
measure bell44
cz bell44 4
H 12
cnot 12 11
T* 11
cnot 3 11
T 11
cnot 12 11
cnot 3 11
H 11
T* 11
cnot bell16 11
T 11
cnot bell18 11
T* 11
cnot bell16 11
H bell16
measure bell16
cz bell16 1
T 11
cnot bell18 11
H bell18
measure bell18
cz bell18 2
H 11
cnot 11 12
T 12
cnot 3 12
T* 12
cnot 11 12
cnot 3 12
H 12
H bell46
cnot bell46 bell47
cnot 12 bell47
measure bell47
cnot bell47 bell46
cnot bell46 13
T 13
H bell48
cnot bell48 bell49
cnot 4 bell49
measure bell49
cnot bell49 bell48
cnot bell48 13
T* 13
cnot bell46 13
H bell46
measure bell46
cz bell46 12
cnot bell48 13
H bell48
measure bell48
cz bell48 4
H 13
cnot 13 14
T 14
cnot 5 14
T* 14
cnot 13 14
cnot 5 14
H 14
H bell50
cnot bell50 bell51
cnot 14 bell51
measure bell51
cnot bell51 bell50
cnot bell50 15
T 15
H bell52
cnot bell52 bell53
cnot 6 bell53
measure bell53
cnot bell53 bell52
cnot bell52 15
T* 15
cnot bell50 15
H bell50
measure bell50
cz bell50 14
cnot bell52 15
H bell52
measure bell52
cz bell52 6
H 15
cnot 15 16
T 16
cnot 7 16
T* 16
cnot 15 16
cnot 7 16
H 16
H bell54
cnot bell54 bell55
cnot 16 bell55
measure bell55
cnot bell55 bell54
cnot bell54 17
T 17
H bell56
cnot bell56 bell57
cnot 8 bell57
measure bell57
cnot bell57 bell56
cnot bell56 17
T* 17
cnot bell54 17
H bell54
measure bell54
cz bell54 16
cnot bell56 17
H bell56
measure bell56
cz bell56 8
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
H bell58
cnot bell58 bell59
cnot 12 bell59
measure bell59
cnot bell59 bell58
cnot bell58 4
T 4
T* 13
cnot 13 5
T 5
T* 14
H bell60
cnot bell60 bell61
cnot 14 bell61
measure bell61
cnot bell61 bell60
cnot bell60 6
T 6
T* 15
cnot 15 7
T 7
T* 16
H bell62
cnot bell62 bell63
cnot 16 bell63
measure bell63
cnot bell63 bell62
cnot bell62 8
T 8
T* 17
cnot 17 9
T 9
cnot 17 9
cnot bell62 8
H bell62
measure bell62
cz bell62 16
cnot 15 7
cnot bell60 6
H bell60
measure bell60
cz bell60 14
cnot 13 5
cnot bell58 4
H bell58
measure bell58
cz bell58 12
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
reset bell42
reset bell43
reset bell44
reset bell45
reset bell46
reset bell47
reset bell48
reset bell49
reset bell50
reset bell51
reset bell52
reset bell53
reset bell54
reset bell55
reset bell56
reset bell57
reset bell58
reset bell59
reset bell60
reset bell61
reset bell62
reset bell63
END
