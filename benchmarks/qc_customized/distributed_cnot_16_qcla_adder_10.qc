# Hyperedge cut (ebits): 48

# Actual ebits used (Synthesis): 66
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/qcla_adder_10.qc):
#   Qubits: 36
#   H: 50
#   T: 238
#   cnot: 233
#   Depth: 64
#   T depth: 30
# Result (106.967ms):
#   Qubits: 168
#   H: 182
#   S: 10
#   T: 162
#   cnot: 426
#   cz: 69
#   measure: 132
#   reset: 135
#   Depth: 134
#   T depth: 28


# Result Circuit
.v a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 d6 a7 b7 c7 a8 b8 c8 d8 a9 b9 c9 e bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9
.o a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 d6 a7 b7 c7 a8 b8 c8 d8 a9 b9 c9 e
BEGIN 
H c0
H c1
H c2
H d2
H c3
H c4
H d4
H c5
H d5
H c6
H d6
H c7
H c8
H d8
H c9
T c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T* c0
cnot b0 c0
cnot a9 b9
cnot a8 b8
cnot a7 b7
H bell0
cnot bell0 bell1
cnot a6 bell1
measure bell1
cnot bell1 bell0
cnot bell0 b6
cnot a5 b5
H bell2
cnot bell2 bell3
cnot a4 bell3
measure bell3
cnot bell3 bell2
cnot bell2 b4
cnot a3 b3
cnot a2 b2
cnot a1 b1
H c0
T c2
H bell4
cnot bell4 bell5
cnot b2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c2
T* c2
H bell6
cnot bell6 bell7
cnot b3 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c2
T c2
cnot bell4 c2
T* c2
cnot bell6 c2
H c2
T d2
H bell8
cnot bell8 bell9
cnot a2 bell9
measure bell9
cnot bell9 bell8
cnot bell8 d2
T* d2
cnot bell4 d2
T* d2
cnot bell8 d2
H bell8
measure bell8
cz bell8 a2
T d2
cnot bell4 d2
H d2
T c4
H bell10
cnot bell10 bell11
cnot b4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c4
T* c4
H bell12
cnot bell12 bell13
cnot b5 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c4
T c4
cnot bell10 c4
T* c4
cnot bell12 c4
H c4
T d4
cnot bell2 d4
T* d4
cnot b4 d4
T* d4
cnot bell2 d4
H bell2
measure bell2
cz bell2 a4
T d4
cnot b4 d4
H d4
T c6
H bell14
cnot bell14 bell15
cnot b6 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c6
T* c6
H bell16
cnot bell16 bell17
cnot b7 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c6
T c6
cnot bell14 c6
T* c6
cnot bell16 c6
H c6
T d6
cnot bell0 d6
T* d6
cnot b6 d6
T* d6
cnot bell0 d6
H bell0
measure bell0
cz bell0 a6
T d6
cnot b6 d6
H d6
T c8
H bell18
cnot bell18 bell19
cnot b8 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c8
T* c8
H bell20
cnot bell20 bell21
cnot b9 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c8
T c8
cnot bell18 c8
T* c8
cnot bell20 c8
H c8
T d8
H bell22
cnot bell22 bell23
cnot a8 bell23
measure bell23
cnot bell23 bell22
cnot bell22 d8
T* d8
cnot bell18 d8
T* d8
cnot bell22 d8
H bell22
measure bell22
cz bell22 a8
T d8
cnot bell18 d8
H d8
H bell24
cnot bell24 bell25
cnot a1 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c1
T* c1
H bell26
cnot bell26 bell27
cnot b1 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c1
T* c1
cnot bell24 c1
H bell24
measure bell24
cz bell24 a1
S c1
H bell28
cnot bell28 bell29
cnot c0 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c1
T* c1
cnot bell26 c1
H bell26
measure bell26
cz bell26 b1
T c1
cnot bell28 c1
H bell28
measure bell28
cz bell28 c0
H c1
T* c5
cnot c4 c5
T c5
H bell30
cnot bell30 bell31
cnot c6 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c5
T* c5
cnot c4 c5
T c5
cnot bell30 c5
H c5
H bell32
cnot bell32 bell33
cnot a5 bell33
measure bell33
cnot bell33 bell32
cnot bell32 d5
T* d5
cnot bell12 d5
T* d5
cnot bell32 d5
H bell32
measure bell32
cz bell32 a5
S d5
H bell34
cnot bell34 bell35
cnot d4 bell35
measure bell35
cnot bell35 bell34
cnot bell34 d5
T* d5
cnot bell12 d5
H bell12
measure bell12
cz bell12 b5
T d5
cnot bell34 d5
H bell34
measure bell34
cz bell34 d4
H d5
T c3
H bell36
cnot bell36 bell37
cnot a3 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c3
T* c3
cnot bell6 c3
T* c3
cnot bell36 c3
H bell36
measure bell36
cz bell36 a3
S c3
H bell38
cnot bell38 bell39
cnot c1 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c3
cnot bell6 c3
T* c3
cnot c2 c3
T c3
cnot bell38 c3
T* c3
cnot d2 c3
cnot c2 c3
T c3
cnot bell6 c3
T* c3
cnot d2 c3
cnot bell6 c3
H c3
T d5
cnot bell30 d5
T* d5
H bell40
cnot bell40 bell41
cnot c7 bell41
measure bell41
cnot bell41 bell40
cnot bell40 d5
T d5
cnot bell30 d5
T* d5
cnot bell40 d5
H bell40
measure bell40
cz bell40 c7
H d5
H bell42
cnot bell42 bell43
cnot a7 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c7
T* c7
cnot bell16 c7
T* c7
cnot bell42 c7
H bell42
measure bell42
cz bell42 a7
S c7
H bell44
cnot bell44 bell45
cnot c3 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c7
cnot bell16 c7
T c7
H bell46
cnot bell46 bell47
cnot c5 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c7
T* c7
cnot bell44 c7
H bell44
measure bell44
cz bell44 c3
T c7
H bell48
cnot bell48 bell49
cnot d6 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c7
cnot bell46 c7
H bell46
measure bell46
cz bell46 c5
T c7
cnot bell16 c7
T* c7
cnot c6 c7
cnot bell48 c7
H bell48
measure bell48
cz bell48 d6
cnot bell16 c7
H bell16
measure bell16
cz bell16 b7
T* c7
cnot c6 c7
H c7
T d5
H bell50
cnot bell50 bell51
cnot c3 bell51
measure bell51
cnot bell51 bell50
cnot bell50 d5
T* d5
cnot c4 d5
T d5
cnot bell50 d5
T* d5
cnot c4 d5
H d5
T* d2
cnot bell6 d2
T d2
cnot bell6 d2
H d2
T* d4
H bell52
cnot bell52 bell53
cnot b5 bell53
measure bell53
cnot bell53 bell52
cnot bell52 d4
T d4
cnot bell52 d4
H bell52
measure bell52
cz bell52 b5
H d4
T* d6
H bell54
cnot bell54 bell55
cnot b7 bell55
measure bell55
cnot bell55 bell54
cnot bell54 d6
T d6
cnot bell54 d6
H bell54
measure bell54
cz bell54 b7
H d6
T* d8
cnot bell20 d8
T d8
cnot c9 d8
T* d8
cnot bell20 d8
T d8
cnot c9 d8
H d8
T* c5
cnot bell50 c5
T c5
cnot bell50 c5
H c5
T c2
cnot bell38 c2
T* c2
cnot bell38 c2
H c2
T c4
cnot c5 c4
T* c4
cnot bell30 c4
T c4
cnot c5 c4
cnot bell50 c4
cnot bell30 c4
H bell30
measure bell30
cz bell30 c6
T* c4
cnot bell50 c4
H bell50
measure bell50
cz bell50 c3
H c4
T c6
H bell56
cnot bell56 bell57
cnot c5 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c6
T* c6
cnot bell56 c6
H bell56
measure bell56
cz bell56 c5
H c6
T c8
H bell58
cnot bell58 bell59
cnot c7 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c8
T* c8
cnot c9 c8
T c8
cnot bell58 c8
T* c8
cnot c9 c8
H c8
T* d2
cnot bell4 d2
T d2
cnot bell38 d2
T* d2
cnot bell4 d2
T d2
cnot bell38 d2
H bell38
measure bell38
cz bell38 c1
H d2
T* d4
cnot b4 d4
T d4
H bell60
cnot bell60 bell61
cnot c3 bell61
measure bell61
cnot bell61 bell60
cnot bell60 d4
T* d4
cnot b4 d4
T d4
cnot bell60 d4
H bell60
measure bell60
cz bell60 c3
H d4
T* d6
cnot b6 d6
T d6
H bell62
cnot bell62 bell63
cnot d5 bell63
measure bell63
cnot bell63 bell62
cnot bell62 d6
T* d6
cnot b6 d6
T d6
cnot bell62 d6
H bell62
measure bell62
cz bell62 d5
H d6
T* d8
cnot bell18 d8
T d8
cnot bell58 d8
T* d8
cnot bell18 d8
T d8
cnot bell58 d8
H d8
T c9
H bell64
cnot bell64 bell65
cnot a9 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c9
T* c9
cnot bell20 c9
T* c9
cnot bell64 c9
H bell64
measure bell64
cz bell64 a9
S c9
cnot bell58 c9
cnot bell20 c9
T* c9
cnot bell58 c9
H bell58
measure bell58
cz bell58 c7
H c9
T c5
H c5
T c2
cnot bell4 c2
T* c2
cnot bell6 c2
T c2
cnot bell4 c2
H bell4
measure bell4
cz bell4 b2
T* c2
cnot bell6 c2
H bell6
measure bell6
cz bell6 b3
H c2
T c4
cnot bell10 c4
T* c4
H bell66
cnot bell66 bell67
cnot b5 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c4
T c4
cnot bell10 c4
H bell10
measure bell10
cz bell10 b4
T* c4
cnot bell66 c4
H bell66
measure bell66
cz bell66 b5
H c4
T c6
cnot bell14 c6
T* c6
H bell68
cnot bell68 bell69
cnot b7 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c6
T c6
cnot bell14 c6
H bell14
measure bell14
cz bell14 b6
T* c6
cnot bell68 c6
H bell68
measure bell68
cz bell68 b7
H c6
T c8
cnot bell18 c8
T* c8
cnot bell20 c8
T c8
cnot bell18 c8
H bell18
measure bell18
cz bell18 b8
T* c8
cnot bell20 c8
H bell20
measure bell20
cz bell20 b9
H c8
T a2
cnot a2 b2
T b2
H bell70
cnot bell70 bell71
cnot b2 bell71
measure bell71
cnot bell71 bell70
cnot bell70 b3
H bell72
cnot bell72 bell73
cnot a2 bell73
measure bell73
cnot bell73 bell72
cnot bell72 b3
S* b3
T a3
cnot b3 a3
cnot bell70 a3
cnot bell72 a3
H bell72
measure bell72
cz bell72 a2
T a3
T a4
H bell74
cnot bell74 bell75
cnot a4 bell75
measure bell75
cnot bell75 bell74
cnot bell74 b4
H bell74
measure bell74
cz bell74 a4
T b4
H bell76
cnot bell76 bell77
cnot b4 bell77
measure bell77
cnot bell77 bell76
cnot bell76 b5
H bell78
cnot bell78 bell79
cnot a4 bell79
measure bell79
cnot bell79 bell78
cnot bell78 b5
S* b5
T a5
cnot b5 a5
cnot bell76 a5
cnot bell78 a5
T a5
T a6
H bell80
cnot bell80 bell81
cnot a6 bell81
measure bell81
cnot bell81 bell80
cnot bell80 b6
H bell80
measure bell80
cz bell80 a6
T b6
H bell82
cnot bell82 bell83
cnot b6 bell83
measure bell83
cnot bell83 bell82
cnot bell82 b7
H bell84
cnot bell84 bell85
cnot a6 bell85
measure bell85
cnot bell85 bell84
cnot bell84 b7
S* b7
T a7
cnot b7 a7
cnot bell82 a7
H bell82
measure bell82
cz bell82 b6
cnot bell84 a7
H bell84
measure bell84
cz bell84 a6
T a7
T a8
cnot a8 b8
T b8
H bell86
cnot bell86 bell87
cnot b8 bell87
measure bell87
cnot bell87 bell86
cnot bell86 b9
H bell88
cnot bell88 bell89
cnot a8 bell89
measure bell89
cnot bell89 bell88
cnot bell88 b9
S* b9
T a9
cnot b9 a9
cnot bell86 a9
cnot bell88 a9
T a9
T a0
T b0
cnot a0 b0
T* b0
T a1
S* b1
cnot a1 b1
T b1
T* c0
H bell90
cnot bell90 bell91
cnot c0 bell91
measure bell91
cnot bell91 bell90
cnot b1 bell90
cnot a1 bell90
H bell92
cnot bell92 bell93
cnot bell90 bell93
measure bell93
cnot bell93 bell92
reset bell93
cnot c0 bell92
cnot bell92 c0
H bell92
measure bell92
cz bell92 a1
cz bell92 b1
H bell90
measure bell90
cz bell90 c0
T c0
cnot b2 c1
cnot a2 c1
T c1
T* c3
H bell94
cnot bell94 bell95
cnot c3 bell95
measure bell95
cnot bell95 bell94
cnot bell76 bell94
cnot bell78 bell94
H bell96
cnot bell96 bell97
cnot bell94 bell97
measure bell97
cnot bell97 bell96
reset bell97
cnot c3 bell96
cnot bell96 c3
H bell96
measure bell96
cz bell96 a4
cz bell96 b4
H bell94
measure bell94
cz bell94 c3
T c3
H bell98
cnot bell98 bell99
cnot c7 bell99
measure bell99
cnot bell99 bell98
cnot bell86 bell98
cnot bell88 bell98
H bell100
cnot bell100 bell101
cnot bell98 bell101
measure bell101
cnot bell101 bell100
reset bell101
cnot c7 bell100
cnot bell100 c7
H bell100
measure bell100
cz bell100 a8
cz bell100 b8
H bell98
measure bell98
cz bell98 c7
H bell88
measure bell88
cz bell88 a8
T c7
T* d5
H bell102
cnot bell102 bell103
cnot b6 bell103
measure bell103
cnot bell103 bell102
cnot bell102 d5
H bell102
measure bell102
cz bell102 b6
H bell104
cnot bell104 bell105
cnot a6 bell105
measure bell105
cnot bell105 bell104
cnot bell104 d5
H bell104
measure bell104
cz bell104 a6
T d5
cnot bell86 b9
H bell86
measure bell86
cz bell86 b8
H bell106
cnot bell106 bell107
cnot b9 bell107
measure bell107
cnot bell107 bell106
cnot bell106 c8
H bell106
measure bell106
cz bell106 b9
H bell108
cnot bell108 bell109
cnot b6 bell109
measure bell109
cnot bell109 bell108
cnot bell108 b7
H bell108
measure bell108
cz bell108 b6
H bell110
cnot bell110 bell111
cnot b7 bell111
measure bell111
cnot bell111 bell110
cnot bell110 d6
H bell110
measure bell110
cz bell110 b7
H bell112
cnot bell112 bell113
cnot b5 bell113
measure bell113
cnot bell113 bell112
cnot bell112 d4
H bell112
measure bell112
cz bell112 b5
cnot bell70 b3
H bell70
measure bell70
cz bell70 b2
cnot b4 d4
H bell114
cnot bell114 bell115
cnot b3 bell115
measure bell115
cnot bell115 bell114
cnot bell114 d2
H bell114
measure bell114
cz bell114 b3
cnot bell76 b5
H bell76
measure bell76
cz bell76 b4
cnot b9 a9
H bell116
cnot bell116 bell117
cnot b0 bell117
measure bell117
cnot bell117 bell116
cnot bell116 e
H bell116
measure bell116
cz bell116 b0
cnot a9 b9
cnot b7 a7
cnot a7 b7
H bell118
cnot bell118 bell119
cnot a6 bell119
measure bell119
cnot bell119 bell118
cnot bell118 a7
H bell118
measure bell118
cz bell118 a6
H bell120
cnot bell120 bell121
cnot a6 bell121
measure bell121
cnot bell121 bell120
cnot bell120 d6
H bell120
measure bell120
cz bell120 a6
H bell122
cnot bell122 bell123
cnot a8 bell123
measure bell123
cnot bell123 bell122
cnot bell122 c8
H bell122
measure bell122
cz bell122 a8
H bell124
cnot bell124 bell125
cnot a8 bell125
measure bell125
cnot bell125 bell124
cnot bell124 a9
H bell124
measure bell124
cz bell124 a8
cnot b5 a5
cnot a5 b5
cnot bell78 a5
H bell78
measure bell78
cz bell78 a4
cnot b3 a3
H bell126
cnot bell126 bell127
cnot a4 bell127
measure bell127
cnot bell127 bell126
cnot bell126 d4
H bell126
measure bell126
cz bell126 a4
cnot a3 b3
H bell128
cnot bell128 bell129
cnot a2 bell129
measure bell129
cnot bell129 bell128
cnot bell128 d2
H bell128
measure bell128
cz bell128 a2
cnot a0 b0
H bell130
cnot bell130 bell131
cnot a2 bell131
measure bell131
cnot bell131 bell130
cnot bell130 a3
H bell130
measure bell130
cz bell130 a2
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
reset bell98
reset bell99
reset bell100
reset bell101
reset bell102
reset bell103
reset bell104
reset bell105
reset bell106
reset bell107
reset bell108
reset bell109
reset bell110
reset bell111
reset bell112
reset bell113
reset bell114
reset bell115
reset bell116
reset bell117
reset bell118
reset bell119
reset bell120
reset bell121
reset bell122
reset bell123
reset bell124
reset bell125
reset bell126
reset bell127
reset bell128
reset bell129
reset bell130
reset bell131
END
