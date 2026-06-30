# Hyperedge cut (ebits): 17

# Actual ebits used (Synthesis): 49
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^4_mult.qc):
#   Qubits: 12
#   H: 14
#   T: 112
#   cnot: 99
#   Depth: 85
#   T depth: 41
# Result (18.193ms):
#   Qubits: 110
#   H: 112
#   S: 2
#   T: 68
#   Z: 3
#   cnot: 255
#   cz: 50
#   measure: 98
#   reset: 99
#   Depth: 215
#   T depth: 39


# Result Circuit
.v a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97
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
cnot b1 c0
T c0
cnot bell0 c0
H bell0
measure bell0
cz bell0 a3
T* c0
H bell2
cnot bell2 bell3
cnot a2 bell3
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
cz bell2 a2
T* c0
H bell6
cnot bell6 bell7
cnot a1 bell7
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
cz bell6 a1
T* c0
cnot bell8 c0
H bell8
measure bell8
cz bell8 b3
H c0
S* c1
H bell10
cnot bell10 bell11
cnot a3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c1
T c1
H bell12
cnot bell12 bell13
cnot b2 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c1
T* c1
cnot bell10 c1
T c1
H bell14
cnot bell14 bell15
cnot a2 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c1
cnot bell12 c1
T c1
H bell16
cnot bell16 bell17
cnot b3 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c1
T* c1
cnot bell14 c1
T c1
cnot bell16 c1
H c1
T c2
cnot bell10 c2
T* c2
cnot bell16 c2
T c2
cnot bell10 c2
H bell10
measure bell10
cz bell10 a3
T* c2
cnot bell16 c2
H bell16
measure bell16
cz bell16 b3
H c2
H bell18
cnot bell18 bell19
cnot c2 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c3
H bell18
measure bell18
cz bell18 c2
cnot c1 c2
H bell20
cnot bell20 bell21
cnot c0 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c1
H bell20
measure bell20
cz bell20 c0
H c0
H c1
H c2
H c3
T c0
H bell22
cnot bell22 bell23
cnot a0 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c0
T* c0
H bell24
cnot bell24 bell25
cnot b0 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c0
T c0
cnot bell22 c0
H bell22
measure bell22
cz bell22 a0
T* c0
cnot bell24 c0
H bell24
measure bell24
cz bell24 b0
H c0
S* c1
H bell26
cnot bell26 bell27
cnot a1 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c1
T c1
H bell28
cnot bell28 bell29
cnot b0 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c1
T* c1
cnot bell26 c1
T c1
H bell30
cnot bell30 bell31
cnot a0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c1
cnot bell28 c1
T c1
H bell32
cnot bell32 bell33
cnot b1 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c1
T* c1
cnot bell30 c1
T c1
cnot bell32 c1
H c1
T* c2
Z c2
cnot bell14 c2
T* c2
cnot bell28 c2
T c2
cnot bell14 c2
H bell14
measure bell14
cz bell14 a2
T* c2
cnot bell26 c2
cnot bell28 c2
H bell28
measure bell28
cz bell28 b0
T* c2
cnot bell32 c2
T c2
cnot bell26 c2
H bell26
measure bell26
cz bell26 a1
T* c2
cnot bell30 c2
cnot bell32 c2
H bell32
measure bell32
cz bell32 b1
T* c2
cnot bell12 c2
T c2
cnot bell30 c2
H bell30
measure bell30
cz bell30 a0
T* c2
cnot bell12 c2
H bell12
measure bell12
cz bell12 b2
H c2
Z c3
H bell34
cnot bell34 bell35
cnot a3 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c3
T c3
H bell36
cnot bell36 bell37
cnot b0 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c3
T* c3
cnot bell34 c3
H bell34
measure bell34
cz bell34 a3
T c3
H bell38
cnot bell38 bell39
cnot a2 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c3
cnot bell36 c3
H bell36
measure bell36
cz bell36 b0
T c3
H bell40
cnot bell40 bell41
cnot b1 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c3
T* c3
cnot bell38 c3
H bell38
measure bell38
cz bell38 a2
T c3
H bell42
cnot bell42 bell43
cnot a1 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c3
cnot bell40 c3
H bell40
measure bell40
cz bell40 b1
T c3
H bell44
cnot bell44 bell45
cnot b2 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c3
T* c3
cnot bell42 c3
H bell42
measure bell42
cz bell42 a1
T c3
H bell46
cnot bell46 bell47
cnot a0 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c3
cnot bell44 c3
H bell44
measure bell44
cz bell44 b2
T c3
H bell48
cnot bell48 bell49
cnot b3 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c3
T* c3
cnot bell46 c3
H bell46
measure bell46
cz bell46 a0
T c3
cnot bell48 c3
H bell48
measure bell48
cz bell48 b3
H c3
H bell50
cnot bell50 bell51
cnot a0 bell51
measure bell51
cnot bell51 bell50
cnot bell50 b0
T* b0
H bell52
cnot bell52 bell53
cnot a1 bell53
measure bell53
cnot bell53 bell52
cnot bell52 b0
H bell52
measure bell52
cz bell52 a1
cnot bell50 b0
H bell50
measure bell50
cz bell50 a0
T b0
H bell54
cnot bell54 bell55
cnot a0 bell55
measure bell55
cnot bell55 bell54
cnot bell54 b1
T b1
H bell56
cnot bell56 bell57
cnot a1 bell57
measure bell57
cnot bell57 bell56
cnot bell56 b1
H bell56
measure bell56
cz bell56 a1
cnot bell54 b1
H bell54
measure bell54
cz bell54 a0
T* b1
cnot b0 a2
H bell58
cnot bell58 bell59
cnot a1 bell59
measure bell59
cnot bell59 bell58
cnot bell58 a2
H bell58
measure bell58
cz bell58 a1
T* a2
H bell60
cnot bell60 bell61
cnot b1 bell61
measure bell61
cnot bell61 bell60
cnot bell60 a2
H bell60
measure bell60
cz bell60 b1
cnot b0 a2
T a2
H bell62
cnot bell62 bell63
cnot a0 bell63
measure bell63
cnot bell63 bell62
cnot bell62 b2
T* b2
H bell64
cnot bell64 bell65
cnot a1 bell65
measure bell65
cnot bell65 bell64
cnot bell64 b2
H bell64
measure bell64
cz bell64 a1
cnot bell62 b2
H bell62
measure bell62
cz bell62 a0
T b2
H bell66
cnot bell66 bell67
cnot b2 bell67
measure bell67
cnot bell67 bell66
H bell68
cnot bell68 bell69
cnot b1 bell69
measure bell69
cnot bell69 bell68
cnot bell68 bell66
H bell70
cnot bell70 bell71
cnot a2 bell71
measure bell71
cnot bell71 bell70
cnot bell70 bell66
H bell72
cnot bell72 bell73
cnot bell66 bell73
measure bell73
cnot bell73 bell72
reset bell73
cnot b2 bell72
cnot bell72 b2
H bell72
measure bell72
cz bell72 a2
cz bell72 b1
H bell66
measure bell66
cz bell66 b2
T* b2
H bell74
cnot bell74 bell75
cnot b0 bell75
measure bell75
cnot bell75 bell74
cnot bell74 a3
H bell76
cnot bell76 bell77
cnot a1 bell77
measure bell77
cnot bell77 bell76
cnot bell76 a3
T a3
cnot bell68 a3
cnot bell74 a3
H bell74
measure bell74
cz bell74 b0
T* a3
H bell78
cnot bell78 bell79
cnot b2 bell79
measure bell79
cnot bell79 bell78
cnot bell78 a3
cnot bell70 a3
T a3
H bell80
cnot bell80 bell81
cnot a0 bell81
measure bell81
cnot bell81 bell80
cnot bell80 b3
T b3
cnot bell76 b3
cnot bell80 b3
H bell80
measure bell80
cz bell80 a0
T* b3
cnot bell68 b3
H bell68
measure bell68
cz bell68 b1
cnot bell70 b3
H bell70
measure bell70
cz bell70 a2
T b3
cnot bell78 b3
cnot a3 b3
T* b3
H bell82
cnot bell82 bell83
cnot b1 bell83
measure bell83
cnot bell83 bell82
cnot bell82 a2
H bell82
measure bell82
cz bell82 b1
cnot bell78 a3
H bell78
measure bell78
cz bell78 b2
H bell84
cnot bell84 bell85
cnot a2 bell85
measure bell85
cnot bell85 bell84
cnot bell84 a3
H bell84
measure bell84
cz bell84 a2
cnot a3 b3
H bell86
cnot bell86 bell87
cnot a2 bell87
measure bell87
cnot bell87 bell86
cnot bell86 b2
H bell86
measure bell86
cz bell86 a2
cnot bell76 b3
H bell76
measure bell76
cz bell76 a1
H bell88
cnot bell88 bell89
cnot a1 bell89
measure bell89
cnot bell89 bell88
cnot bell88 b2
H bell88
measure bell88
cz bell88 a1
H bell90
cnot bell90 bell91
cnot a1 bell91
measure bell91
cnot bell91 bell90
cnot bell90 b1
H bell90
measure bell90
cz bell90 a1
H bell92
cnot bell92 bell93
cnot a1 bell93
measure bell93
cnot bell93 bell92
cnot bell92 b0
H bell92
measure bell92
cz bell92 a1
H bell94
cnot bell94 bell95
cnot a1 bell95
measure bell95
cnot bell95 bell94
cnot bell94 a3
H bell94
measure bell94
cz bell94 a1
H bell96
cnot bell96 bell97
cnot a1 bell97
measure bell97
cnot bell97 bell96
cnot bell96 a2
H bell96
measure bell96
cz bell96 a1
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
reset bell82
reset bell83
reset bell84
reset bell85
reset bell86
reset bell87
reset bell88
reset bell89
reset bell90
reset bell91
reset bell92
reset bell93
reset bell94
reset bell95
reset bell96
reset bell97
END
