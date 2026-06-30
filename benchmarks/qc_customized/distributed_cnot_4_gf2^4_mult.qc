# Hyperedge cut (ebits): 13

# Actual ebits used (Synthesis): 26
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^4_mult.qc):
#   Qubits: 12
#   H: 14
#   T: 112
#   cnot: 99
#   Depth: 85
#   T depth: 41
# Result (17.464ms):
#   Qubits: 64
#   H: 66
#   S: 2
#   T: 68
#   Z: 3
#   cnot: 184
#   cz: 26
#   measure: 52
#   reset: 52
#   Depth: 160
#   T depth: 39


# Result Circuit
.v a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell6 bell7 bell8 bell9
.i a0 a1 a2 a3 b0 b1 b2 b3
.o a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
BEGIN 
H c0
H c1
H c2
T* c0
Z c0
H bell0
cnot bell0 bell1
cnot a3 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
H bell2
cnot bell2 bell3
cnot b1 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
T c0
cnot bell0 c0
T* c0
H bell4
cnot bell4 bell5
cnot a2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
cnot bell2 c0
T* c0
H bell6
cnot bell6 bell7
cnot b2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
T c0
cnot bell4 c0
T* c0
H bell8
cnot bell8 bell9
cnot a1 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
cnot bell6 c0
T* c0
H bell10
cnot bell10 bell11
cnot b3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
T c0
cnot bell8 c0
T* c0
cnot bell10 c0
H c0
S* c1
cnot bell0 c1
T c1
cnot bell6 c1
T* c1
cnot bell0 c1
T c1
cnot bell4 c1
cnot bell6 c1
T c1
cnot bell10 c1
T* c1
cnot bell4 c1
T c1
cnot bell10 c1
H c1
T c2
cnot bell0 c2
T* c2
cnot bell10 c2
T c2
cnot bell0 c2
H bell0
measure bell0
cz bell0 a3
T* c2
cnot bell10 c2
H bell10
measure bell10
cz bell10 b3
H c2
H bell12
cnot bell12 bell13
cnot c2 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c3
H bell12
measure bell12
cz bell12 c2
cnot c1 c2
cnot c0 c1
H c0
H c1
H c2
H c3
T c0
H bell14
cnot bell14 bell15
cnot a0 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
T* c0
H bell16
cnot bell16 bell17
cnot b0 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
T c0
cnot bell14 c0
T* c0
cnot bell16 c0
H c0
S* c1
cnot bell8 c1
T c1
cnot bell16 c1
T* c1
cnot bell8 c1
T c1
cnot bell14 c1
cnot bell16 c1
T c1
cnot bell2 c1
T* c1
cnot bell14 c1
T c1
cnot bell2 c1
H c1
T* c2
Z c2
cnot bell4 c2
T* c2
cnot bell16 c2
T c2
cnot bell4 c2
H bell4
measure bell4
cz bell4 a2
T* c2
cnot bell8 c2
cnot bell16 c2
H bell16
measure bell16
cz bell16 b0
T* c2
cnot bell2 c2
T c2
cnot bell8 c2
H bell8
measure bell8
cz bell8 a1
T* c2
cnot bell14 c2
cnot bell2 c2
H bell2
measure bell2
cz bell2 b1
T* c2
cnot bell6 c2
T c2
cnot bell14 c2
H bell14
measure bell14
cz bell14 a0
T* c2
cnot bell6 c2
H bell6
measure bell6
cz bell6 b2
H c2
Z c3
H bell18
cnot bell18 bell19
cnot a3 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c3
T c3
H bell20
cnot bell20 bell21
cnot b0 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c3
T* c3
cnot bell18 c3
H bell18
measure bell18
cz bell18 a3
T c3
H bell22
cnot bell22 bell23
cnot a2 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c3
cnot bell20 c3
H bell20
measure bell20
cz bell20 b0
T c3
cnot b1 c3
T* c3
cnot bell22 c3
H bell22
measure bell22
cz bell22 a2
T c3
H bell24
cnot bell24 bell25
cnot a1 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c3
cnot b1 c3
T c3
H bell26
cnot bell26 bell27
cnot b2 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c3
T* c3
cnot bell24 c3
T c3
cnot a0 c3
cnot bell26 c3
H bell26
measure bell26
cz bell26 b2
T c3
H bell28
cnot bell28 bell29
cnot b3 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c3
T* c3
cnot a0 c3
T c3
cnot bell28 c3
H bell28
measure bell28
cz bell28 b3
H c3
H bell30
cnot bell30 bell31
cnot a0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 b0
T* b0
cnot a1 b0
cnot bell30 b0
H bell30
measure bell30
cz bell30 a0
T b0
cnot a0 b1
T b1
cnot bell24 b1
H bell24
measure bell24
cz bell24 a1
cnot a0 b1
T* b1
cnot b0 a2
cnot a1 a2
T* a2
H bell32
cnot bell32 bell33
cnot b1 bell33
measure bell33
cnot bell33 bell32
cnot bell32 a2
H bell32
measure bell32
cz bell32 b1
cnot b0 a2
T a2
H bell34
cnot bell34 bell35
cnot a0 bell35
measure bell35
cnot bell35 bell34
cnot bell34 b2
T* b2
H bell36
cnot bell36 bell37
cnot a1 bell37
measure bell37
cnot bell37 bell36
cnot bell36 b2
cnot bell34 b2
T b2
H bell38
cnot bell38 bell39
cnot b1 bell39
measure bell39
cnot bell39 bell38
cnot bell38 b2
H bell40
cnot bell40 bell41
cnot a2 bell41
measure bell41
cnot bell41 bell40
cnot bell40 b2
T* b2
H bell42
cnot bell42 bell43
cnot b0 bell43
measure bell43
cnot bell43 bell42
cnot bell42 a3
cnot bell36 a3
T a3
cnot bell38 a3
cnot bell42 a3
H bell42
measure bell42
cz bell42 b0
T* a3
cnot b2 a3
cnot bell40 a3
T a3
cnot bell34 b3
T b3
cnot bell36 b3
cnot bell34 b3
H bell34
measure bell34
cz bell34 a0
T* b3
cnot bell38 b3
H bell38
measure bell38
cz bell38 b1
cnot bell40 b3
H bell40
measure bell40
cz bell40 a2
T b3
cnot b2 b3
cnot a3 b3
T* b3
H bell44
cnot bell44 bell45
cnot b1 bell45
measure bell45
cnot bell45 bell44
cnot bell44 a2
H bell44
measure bell44
cz bell44 b1
cnot b2 a3
H bell46
cnot bell46 bell47
cnot a2 bell47
measure bell47
cnot bell47 bell46
cnot bell46 a3
cnot a3 b3
cnot bell46 b2
H bell46
measure bell46
cz bell46 a2
cnot bell36 b3
cnot bell36 b2
H bell36
measure bell36
cz bell36 a1
H bell48
cnot bell48 bell49
cnot a1 bell49
measure bell49
cnot bell49 bell48
cnot bell48 b1
H bell48
measure bell48
cz bell48 a1
cnot a1 b0
H bell50
cnot bell50 bell51
cnot a1 bell51
measure bell51
cnot bell51 bell50
cnot bell50 a3
H bell50
measure bell50
cz bell50 a1
cnot a1 a2
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
END
