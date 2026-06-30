# Hyperedge cut (ebits): 25

# Actual ebits used (Synthesis): 41
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^7_mult.qc):
#   Qubits: 21
#   H: 26
#   T: 343
#   cnot: 300
#   Depth: 166
#   T depth: 80
# Result (43.108ms):
#   Qubits: 103
#   H: 108
#   S: 4
#   T: 217
#   Z: 6
#   cnot: 442
#   cz: 41
#   measure: 82
#   reset: 82
#   Depth: 252
#   T depth: 75


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell9
.i a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6
.o a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6
BEGIN 
H c0
H c1
H c2
H c3
H c4
H c5
S* c0
H bell0
cnot bell0 bell1
cnot a6 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
cnot b1 c0
T c0
cnot bell0 c0
H bell0
measure bell0
cz bell0 a6
T* c0
H bell2
cnot bell2 bell3
cnot a5 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
cnot b1 c0
T* c0
H bell4
cnot bell4 bell5
cnot b2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
T c0
cnot bell2 c0
H bell2
measure bell2
cz bell2 a5
T* c0
H bell6
cnot bell6 bell7
cnot a4 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
cnot bell4 c0
H bell4
measure bell4
cz bell4 b2
T* c0
H bell8
cnot bell8 bell9
cnot b3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
T c0
cnot bell6 c0
H bell6
measure bell6
cz bell6 a4
T* c0
H bell10
cnot bell10 bell11
cnot a3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
cnot bell8 c0
H bell8
measure bell8
cz bell8 b3
T* c0
H bell12
cnot bell12 bell13
cnot b4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
T c0
cnot bell10 c0
H bell10
measure bell10
cz bell10 a3
T* c0
H bell14
cnot bell14 bell15
cnot a2 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
cnot bell12 c0
H bell12
measure bell12
cz bell12 b4
T* c0
H bell16
cnot bell16 bell17
cnot b5 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
T c0
cnot bell14 c0
H bell14
measure bell14
cz bell14 a2
T* c0
cnot a1 c0
cnot bell16 c0
H bell16
measure bell16
cz bell16 b5
T* c0
H bell18
cnot bell18 bell19
cnot b6 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c0
T c0
cnot a1 c0
T* c0
cnot bell18 c0
H bell18
measure bell18
cz bell18 b6
H c0
T c1
Z c1
H bell20
cnot bell20 bell21
cnot a6 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c1
T* c1
H bell22
cnot bell22 bell23
cnot b2 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c1
T c1
cnot bell20 c1
T* c1
H bell24
cnot bell24 bell25
cnot a5 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c1
cnot bell22 c1
T* c1
H bell26
cnot bell26 bell27
cnot b3 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c1
T c1
cnot bell24 c1
T* c1
H bell28
cnot bell28 bell29
cnot a4 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c1
cnot bell26 c1
T* c1
H bell30
cnot bell30 bell31
cnot b4 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c1
T c1
cnot bell28 c1
T* c1
H bell32
cnot bell32 bell33
cnot a3 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c1
cnot bell30 c1
T* c1
H bell34
cnot bell34 bell35
cnot b5 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c1
T c1
cnot bell32 c1
T* c1
H bell36
cnot bell36 bell37
cnot a2 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c1
cnot bell34 c1
T* c1
H bell38
cnot bell38 bell39
cnot b6 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c1
T c1
cnot bell36 c1
T* c1
cnot bell38 c1
H c1
Z c2
cnot bell20 c2
T* c2
cnot bell26 c2
T c2
cnot bell20 c2
T* c2
cnot bell24 c2
cnot bell26 c2
T* c2
cnot bell30 c2
T c2
cnot bell24 c2
T* c2
cnot bell28 c2
cnot bell30 c2
T* c2
cnot bell34 c2
T c2
cnot bell28 c2
T* c2
cnot bell32 c2
cnot bell34 c2
T* c2
cnot bell38 c2
T c2
cnot bell32 c2
T* c2
cnot bell38 c2
H c2
T* c3
Z c3
cnot bell20 c3
T* c3
cnot bell30 c3
T c3
cnot bell20 c3
T* c3
cnot bell24 c3
cnot bell30 c3
T* c3
cnot bell34 c3
T c3
cnot bell24 c3
T* c3
cnot bell28 c3
cnot bell34 c3
T* c3
cnot bell38 c3
T c3
cnot bell28 c3
T* c3
cnot bell38 c3
H c3
S c4
cnot bell20 c4
T* c4
cnot bell34 c4
T c4
cnot bell20 c4
T* c4
cnot bell24 c4
cnot bell34 c4
T* c4
cnot bell38 c4
T c4
cnot bell24 c4
T* c4
cnot bell38 c4
H c4
T c5
cnot bell20 c5
T* c5
cnot bell38 c5
T c5
cnot bell20 c5
T* c5
cnot bell38 c5
H c5
cnot c5 c6
cnot c4 c5
cnot c3 c4
cnot c2 c3
cnot c1 c2
H bell40
cnot bell40 bell41
cnot c0 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c1
H bell40
measure bell40
cz bell40 c0
H c0
H c1
H c2
H c3
H c4
H c5
H c6
T c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T* c0
cnot b0 c0
H c0
S c1
H bell42
cnot bell42 bell43
cnot a1 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c1
T* c1
H bell44
cnot bell44 bell45
cnot b0 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c1
T c1
cnot bell42 c1
T* c1
H bell46
cnot bell46 bell47
cnot a0 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c1
cnot bell44 c1
T* c1
H bell48
cnot bell48 bell49
cnot b1 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c1
T c1
cnot bell46 c1
T* c1
cnot bell48 c1
H c1
T* c2
Z c2
cnot bell36 c2
T* c2
cnot bell44 c2
T c2
cnot bell36 c2
T* c2
cnot bell42 c2
cnot bell44 c2
T* c2
cnot bell48 c2
T c2
cnot bell42 c2
T* c2
cnot bell46 c2
cnot bell48 c2
T* c2
cnot bell22 c2
T c2
cnot bell46 c2
T* c2
cnot bell22 c2
H c2
Z c3
cnot bell32 c3
T* c3
cnot bell44 c3
T c3
cnot bell32 c3
T* c3
cnot bell36 c3
cnot bell44 c3
T* c3
cnot bell48 c3
T c3
cnot bell36 c3
T* c3
cnot bell42 c3
cnot bell48 c3
T* c3
cnot bell22 c3
T c3
cnot bell42 c3
T* c3
cnot bell46 c3
cnot bell22 c3
T* c3
cnot bell26 c3
T c3
cnot bell46 c3
T* c3
cnot bell26 c3
H c3
T c4
Z c4
cnot bell28 c4
T* c4
cnot bell44 c4
T c4
cnot bell28 c4
T* c4
cnot bell32 c4
cnot bell44 c4
T* c4
cnot bell48 c4
T c4
cnot bell32 c4
T* c4
cnot bell36 c4
cnot bell48 c4
T* c4
cnot bell22 c4
T c4
cnot bell36 c4
T* c4
cnot bell42 c4
cnot bell22 c4
T* c4
cnot bell26 c4
T c4
cnot bell42 c4
T* c4
cnot bell46 c4
cnot bell26 c4
T* c4
cnot bell30 c4
T c4
cnot bell46 c4
T* c4
cnot bell30 c4
H c4
S* c5
cnot bell24 c5
T* c5
cnot bell44 c5
T c5
cnot bell24 c5
T* c5
cnot bell28 c5
cnot bell44 c5
T* c5
cnot bell48 c5
T c5
cnot bell28 c5
T* c5
cnot bell32 c5
cnot bell48 c5
T* c5
cnot bell22 c5
T c5
cnot bell32 c5
T* c5
cnot bell36 c5
cnot bell22 c5
T* c5
cnot bell26 c5
T c5
cnot bell36 c5
T* c5
cnot bell42 c5
cnot bell26 c5
T* c5
cnot bell30 c5
T c5
cnot bell42 c5
T* c5
cnot bell46 c5
cnot bell30 c5
T* c5
cnot bell34 c5
T c5
cnot bell46 c5
T* c5
cnot bell34 c5
H c5
T* c6
cnot bell20 c6
T* c6
cnot bell44 c6
T c6
cnot bell20 c6
H bell20
measure bell20
cz bell20 a6
T* c6
cnot bell24 c6
cnot bell44 c6
H bell44
measure bell44
cz bell44 b0
T* c6
cnot bell48 c6
T c6
cnot bell24 c6
H bell24
measure bell24
cz bell24 a5
T* c6
cnot bell28 c6
cnot bell48 c6
H bell48
measure bell48
cz bell48 b1
T* c6
cnot bell22 c6
T c6
cnot bell28 c6
H bell28
measure bell28
cz bell28 a4
T* c6
cnot bell32 c6
cnot bell22 c6
H bell22
measure bell22
cz bell22 b2
T* c6
cnot bell26 c6
T c6
cnot bell32 c6
H bell32
measure bell32
cz bell32 a3
T* c6
cnot bell36 c6
cnot bell26 c6
H bell26
measure bell26
cz bell26 b3
T* c6
cnot bell30 c6
T c6
cnot bell36 c6
H bell36
measure bell36
cz bell36 a2
T* c6
cnot bell42 c6
cnot bell30 c6
H bell30
measure bell30
cz bell30 b4
T* c6
cnot bell34 c6
T c6
cnot bell42 c6
H bell42
measure bell42
cz bell42 a1
T* c6
cnot bell46 c6
cnot bell34 c6
H bell34
measure bell34
cz bell34 b5
T* c6
cnot bell38 c6
T c6
cnot bell46 c6
H bell46
measure bell46
cz bell46 a0
T* c6
cnot bell38 c6
H bell38
measure bell38
cz bell38 b6
H c6
T* a0
T* a1
T* b0
cnot a0 b0
T* b0
cnot a1 b0
cnot a0 b0
T* b0
T* b1
cnot a0 b1
T* b1
cnot a1 b1
cnot a0 b1
T* b1
T* a2
H bell50
cnot bell50 bell51
cnot b0 bell51
measure bell51
cnot bell51 bell50
cnot bell50 a2
H bell52
cnot bell52 bell53
cnot a1 bell53
measure bell53
cnot bell53 bell52
cnot bell52 a2
T* a2
H bell54
cnot bell54 bell55
cnot b1 bell55
measure bell55
cnot bell55 bell54
cnot bell54 a2
cnot bell50 a2
T* a2
T* b2
H bell56
cnot bell56 bell57
cnot a0 bell57
measure bell57
cnot bell57 bell56
cnot bell56 b2
T* b2
cnot bell52 b2
cnot bell56 b2
T* b2
cnot bell54 b2
cnot a2 b2
T* b2
T* a3
cnot bell50 a3
cnot bell52 a3
T* a3
cnot bell54 a3
cnot bell50 a3
H bell50
measure bell50
cz bell50 b0
T* a3
cnot b2 a3
cnot a2 a3
T* a3
T* b3
cnot bell56 b3
T* b3
cnot bell52 b3
H bell52
measure bell52
cz bell52 a1
cnot bell56 b3
H bell56
measure bell56
cz bell56 a0
T* b3
cnot bell54 b3
H bell54
measure bell54
cz bell54 b1
cnot a2 b3
T* b3
cnot b2 b3
cnot a3 b3
T* b3
T* a4
H bell58
cnot bell58 bell59
cnot b0 bell59
measure bell59
cnot bell59 bell58
cnot bell58 a4
H bell60
cnot bell60 bell61
cnot a1 bell61
measure bell61
cnot bell61 bell60
cnot bell60 a4
T* a4
H bell62
cnot bell62 bell63
cnot b1 bell63
measure bell63
cnot bell63 bell62
cnot bell62 a4
cnot bell58 a4
T* a4
H bell64
cnot bell64 bell65
cnot b2 bell65
measure bell65
cnot bell65 bell64
cnot bell64 a4
H bell66
cnot bell66 bell67
cnot a2 bell67
measure bell67
cnot bell67 bell66
cnot bell66 a4
T* a4
H bell68
cnot bell68 bell69
cnot b3 bell69
measure bell69
cnot bell69 bell68
cnot bell68 a4
H bell70
cnot bell70 bell71
cnot a3 bell71
measure bell71
cnot bell71 bell70
cnot bell70 a4
T* a4
T* b4
H bell72
cnot bell72 bell73
cnot a0 bell73
measure bell73
cnot bell73 bell72
cnot bell72 b4
T* b4
cnot bell60 b4
cnot bell72 b4
T* b4
cnot bell62 b4
cnot bell66 b4
T* b4
cnot bell64 b4
cnot bell70 b4
T* b4
cnot bell68 b4
cnot a4 b4
T* b4
T* a5
cnot bell58 a5
cnot bell60 a5
T* a5
cnot bell62 a5
cnot bell58 a5
T* a5
cnot bell64 a5
cnot bell66 a5
T* a5
cnot bell68 a5
cnot bell70 a5
T* a5
cnot b4 a5
cnot a4 a5
T* a5
T* b5
cnot bell72 b5
T* b5
cnot bell60 b5
cnot bell72 b5
T* b5
cnot bell62 b5
cnot bell66 b5
T* b5
cnot bell64 b5
cnot bell70 b5
T* b5
cnot bell68 b5
cnot a4 b5
T* b5
cnot b4 b5
cnot a5 b5
T* b5
T* a6
cnot bell58 a6
cnot bell60 a6
T* a6
cnot bell62 a6
cnot bell58 a6
H bell58
measure bell58
cz bell58 b0
T* a6
cnot bell64 a6
cnot bell66 a6
T* a6
cnot bell68 a6
cnot bell70 a6
T* a6
cnot b4 a6
cnot a4 a6
T* a6
cnot b5 a6
cnot a5 a6
T* a6
T* b6
cnot bell72 b6
T* b6
cnot bell60 b6
H bell60
measure bell60
cz bell60 a1
cnot bell72 b6
H bell72
measure bell72
cz bell72 a0
T* b6
cnot bell62 b6
H bell62
measure bell62
cz bell62 b1
cnot bell66 b6
H bell66
measure bell66
cz bell66 a2
T* b6
cnot bell64 b6
H bell64
measure bell64
cz bell64 b2
cnot bell70 b6
H bell70
measure bell70
cz bell70 a3
T* b6
cnot bell68 b6
cnot a4 b6
T* b6
cnot b4 b6
cnot a5 b6
T* b6
cnot b5 b6
cnot a6 b6
T* b6
H bell74
cnot bell74 bell75
cnot b1 bell75
measure bell75
cnot bell75 bell74
cnot bell74 a2
H bell74
measure bell74
cz bell74 b1
cnot b2 a3
cnot bell68 a4
H bell68
measure bell68
cz bell68 b3
cnot b4 a5
cnot b5 a6
cnot a6 b6
cnot a4 a5
H bell76
cnot bell76 bell77
cnot a3 bell77
measure bell77
cnot bell77 bell76
cnot bell76 a5
cnot bell76 a4
H bell76
measure bell76
cz bell76 a3
cnot a5 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a5 a6
H bell78
cnot bell78 bell79
cnot a1 bell79
measure bell79
cnot bell79 bell78
cnot bell78 a2
H bell78
measure bell78
cz bell78 a1
H bell80
cnot bell80 bell81
cnot a2 bell81
measure bell81
cnot bell81 bell80
cnot bell80 b6
cnot bell80 b5
cnot bell80 b4
cnot a2 b3
cnot a2 b2
cnot a1 b1
cnot a1 b0
cnot bell80 a6
cnot bell80 a5
cnot bell80 a4
H bell80
measure bell80
cz bell80 a2
cnot a2 a3
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
reset bell64
reset bell65
reset bell66
reset bell67
reset bell68
reset bell69
reset bell70
reset bell71
reset bell72
reset bell73
reset bell74
reset bell75
reset bell76
reset bell77
reset bell78
reset bell79
reset bell80
reset bell81
END
