# Hyperedge cut (ebits): 45

# Actual ebits used (Synthesis): 76
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/qcla_mod_7.qc):
#   Qubits: 26
#   H: 82
#   T: 413
#   X: 7
#   cnot: 382
#   Depth: 172
#   T depth: 77
# Result (130.883ms):
#   Qubits: 178
#   H: 234
#   S: 24
#   T: 237
#   X: 7
#   cnot: 606
#   cz: 76
#   measure: 152
#   reset: 152
#   Depth: 242
#   T depth: 65


# Result Circuit
.v e a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6
.o e a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6
BEGIN 
H e
H c0
H d0
H c1
H d1
H c2
H d2
H c3
H c4
H d4
H c5
H d5
T c0
H bell0
cnot bell0 bell1
cnot b0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
H bell2
cnot bell2 bell3
cnot a0 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
T* c0
cnot b1 c0
H bell4
cnot bell4 bell5
cnot a1 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
T c0
cnot bell0 c0
H bell0
measure bell0
cz bell0 b0
cnot bell2 c0
T* c0
cnot b1 c0
cnot a6 b6
H bell6
cnot bell6 bell7
cnot a5 bell7
measure bell7
cnot bell7 bell6
cnot bell6 b5
cnot a4 b4
H bell8
cnot bell8 bell9
cnot a3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 b3
H bell8
measure bell8
cz bell8 a3
cnot bell4 c0
H bell10
cnot bell10 bell11
cnot a2 bell11
measure bell11
cnot bell11 bell10
cnot bell10 b2
cnot bell4 b1
cnot a0 b0
H c0
T d0
cnot a0 d0
T* d0
cnot b0 d0
T* d0
cnot a0 d0
T d0
cnot b0 d0
H d0
T c2
cnot b2 c2
T* c2
cnot b3 c2
T c2
cnot b2 c2
T* c2
cnot b3 c2
H c2
T d2
cnot bell10 d2
T* d2
cnot b2 d2
T* d2
cnot bell10 d2
T d2
cnot b2 d2
H d2
T c4
H bell12
cnot bell12 bell13
cnot b4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c4
T* c4
cnot b5 c4
T c4
cnot bell12 c4
T* c4
cnot b5 c4
H c4
T d4
H bell14
cnot bell14 bell15
cnot a4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 d4
T* d4
cnot bell12 d4
T* d4
cnot bell14 d4
T d4
cnot bell12 d4
H d4
T c1
cnot c0 c1
T* c1
H bell16
cnot bell16 bell17
cnot c2 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c1
T c1
cnot c0 c1
T* c1
cnot bell16 c1
H bell16
measure bell16
cz bell16 c2
H c1
S d1
cnot bell4 d1
T* d1
cnot b1 d1
T* d1
cnot bell4 d1
H bell18
cnot bell18 bell19
cnot d0 bell19
measure bell19
cnot bell19 bell18
cnot bell18 d1
T d1
cnot b1 d1
T* d1
cnot bell18 d1
H bell18
measure bell18
cz bell18 d0
H d1
T c5
H bell20
cnot bell20 bell21
cnot b6 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c5
T* c5
H bell22
cnot bell22 bell23
cnot c4 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c5
T c5
cnot bell20 c5
T* c5
cnot bell22 c5
H bell22
measure bell22
cz bell22 c4
H c5
S d5
cnot bell6 d5
T* d5
cnot b5 d5
T* d5
cnot bell6 d5
cnot d4 d5
T d5
cnot b5 d5
T* d5
cnot d4 d5
H d5
T c3
H bell24
cnot bell24 bell25
cnot a3 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c3
T* c3
H bell26
cnot bell26 bell27
cnot b3 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c3
T* c3
cnot bell24 c3
H bell24
measure bell24
cz bell24 a3
H bell28
cnot bell28 bell29
cnot c2 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c3
cnot bell26 c3
T c3
H bell30
cnot bell30 bell31
cnot d1 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c3
T* c3
cnot bell28 c3
H bell28
measure bell28
cz bell28 c2
T c3
H bell32
cnot bell32 bell33
cnot d2 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c3
cnot bell30 c3
H bell30
measure bell30
cz bell30 d1
T* c3
cnot bell26 c3
T c3
cnot bell32 c3
H bell32
measure bell32
cz bell32 d2
cnot bell26 c3
H bell26
measure bell26
cz bell26 b3
H c3
S* e
H bell34
cnot bell34 bell35
cnot a6 bell35
measure bell35
cnot bell35 bell34
cnot bell34 e
T* e
cnot bell20 e
T* e
cnot bell34 e
H bell34
measure bell34
cz bell34 a6
S e
H bell36
cnot bell36 bell37
cnot c1 bell37
measure bell37
cnot bell37 bell36
cnot bell36 e
cnot bell20 e
T e
cnot c5 e
T* e
cnot bell36 e
S e
cnot c3 e
T* e
cnot c5 e
T e
H bell38
cnot bell38 bell39
cnot d5 bell39
measure bell39
cnot bell39 bell38
cnot bell38 e
cnot c3 e
T e
cnot bell20 e
T* e
cnot bell38 e
H bell38
measure bell38
cz bell38 d5
cnot bell20 e
H bell20
measure bell20
cz bell20 b6
H e
T* c3
cnot c5 c3
T c3
cnot c5 c3
H c3
T* c3
cnot bell36 c3
T c3
cnot e c3
T* c3
cnot bell36 c3
H bell36
measure bell36
cz bell36 c1
T c3
cnot e c3
H c3
T* d1
H bell40
cnot bell40 bell41
cnot c2 bell41
measure bell41
cnot bell41 bell40
cnot bell40 d1
T d1
cnot bell40 d1
H d1
S* c1
H bell42
cnot bell42 bell43
cnot c5 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c1
T c1
H bell44
cnot bell44 bell45
cnot e bell45
measure bell45
cnot bell45 bell44
cnot bell44 c1
cnot bell42 c1
H bell42
measure bell42
cz bell42 c5
T c1
cnot bell44 c1
H bell44
measure bell44
cz bell44 e
H c1
T d0
H bell46
cnot bell46 bell47
cnot b1 bell47
measure bell47
cnot bell47 bell46
cnot bell46 d0
T* d0
cnot bell46 d0
H bell46
measure bell46
cz bell46 b1
H d0
T d4
cnot b5 d4
T* d4
cnot b5 d4
H d4
S* c5
H c5
T* d5
H bell48
cnot bell48 bell49
cnot b6 bell49
measure bell49
cnot bell49 bell48
cnot bell48 d5
T d5
cnot bell48 d5
H d5
T* d0
cnot b0 d0
T d0
H bell50
cnot bell50 bell51
cnot e bell51
measure bell51
cnot bell51 bell50
cnot bell50 d0
T* d0
cnot b0 d0
T d0
cnot bell50 d0
H bell50
measure bell50
cz bell50 e
H d0
T* d1
cnot c0 d1
T d1
H bell52
cnot bell52 bell53
cnot e bell53
measure bell53
cnot bell53 bell52
cnot bell52 d1
T* d1
cnot c0 d1
T d1
cnot bell52 d1
H d1
T* d4
cnot bell12 d4
T d4
H bell54
cnot bell54 bell55
cnot c3 bell55
measure bell55
cnot bell55 bell54
cnot bell54 d4
T* d4
cnot bell12 d4
H bell12
measure bell12
cz bell12 b4
T d4
cnot bell54 d4
H d4
T* d5
cnot bell54 d5
T d5
cnot c4 d5
T* d5
cnot bell54 d5
T d5
cnot c4 d5
H d5
T* c0
cnot c1 c0
T c0
cnot bell40 c0
T* c0
cnot c1 c0
cnot bell52 c0
cnot bell40 c0
H bell40
measure bell40
cz bell40 c2
T c0
cnot bell52 c0
H bell52
measure bell52
cz bell52 e
H c0
T* c2
H bell56
cnot bell56 bell57
cnot c1 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c2
T c2
cnot bell56 c2
H bell56
measure bell56
cz bell56 c1
H c2
T d2
cnot b3 d2
T* d2
cnot b3 d2
H d2
T* c4
cnot bell48 c4
H bell58
cnot bell58 bell59
cnot c5 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c4
T* c4
cnot bell48 c4
H bell48
measure bell48
cz bell48 b6
T c4
cnot bell54 c4
cnot bell58 c4
T c4
cnot bell54 c4
H bell54
measure bell54
cz bell54 c3
H c4
T* d2
cnot b2 d2
T d2
H bell60
cnot bell60 bell61
cnot d1 bell61
measure bell61
cnot bell61 bell60
cnot bell60 d2
T* d2
cnot b2 d2
T d2
cnot bell60 d2
H d2
cnot b2 b3
cnot c2 b3
T* b3
cnot b2 b3
T b3
H bell62
cnot bell62 bell63
cnot a3 bell63
measure bell63
cnot bell63 bell62
cnot bell62 b3
cnot c2 b3
T b3
H bell64
cnot bell64 bell65
cnot d0 bell65
measure bell65
cnot bell65 bell64
cnot bell64 b1
H bell66
cnot bell66 bell67
cnot e bell67
measure bell67
cnot bell67 bell66
cnot bell66 b0
H bell66
measure bell66
cz bell66 e
H bell68
cnot bell68 bell69
cnot c3 bell69
measure bell69
cnot bell69 bell68
cnot bell68 b4
H bell68
measure bell68
cz bell68 c3
cnot bell60 b2
cnot d2 b3
cnot d4 b5
H bell70
cnot bell70 bell71
cnot d5 bell71
measure bell71
cnot bell71 bell70
cnot bell70 b6
H bell70
measure bell70
cz bell70 d5
cnot a6 b6
cnot bell6 b5
cnot a4 b4
cnot bell10 b2
cnot bell4 b1
cnot a0 b0
H d2
H bell72
cnot bell72 bell73
cnot b0 bell73
measure bell73
cnot bell73 bell72
cnot bell72 c0
T c0
cnot b1 c0
T c0
cnot bell72 c0
T c0
cnot bell64 c0
cnot bell4 c0
T c0
H bell74
cnot bell74 bell75
cnot e bell75
measure bell75
cnot bell75 bell74
cnot bell74 c0
cnot bell72 c0
cnot bell2 c0
T* c0
cnot bell64 c0
H bell64
measure bell64
cz bell64 d0
cnot b1 c0
cnot bell4 c0
H bell4
measure bell4
cz bell4 a1
T c0
cnot bell74 c0
H bell74
measure bell74
cz bell74 e
cnot bell72 c0
H bell72
measure bell72
cz bell72 b0
cnot bell2 c0
H bell2
measure bell2
cz bell2 a0
H c0
cnot b2 c2
T c2
cnot b3 c2
T c2
cnot b2 c2
T c2
cnot bell60 c2
cnot b3 c2
cnot b2 c2
cnot bell10 c2
T c2
cnot bell60 c2
cnot b2 c2
cnot bell10 c2
H bell10
measure bell10
cz bell10 a2
H c2
T d2
cnot b2 d2
T d2
cnot bell60 d2
T* d2
cnot b2 d2
T* d2
cnot bell60 d2
H bell60
measure bell60
cz bell60 d1
H d2
H bell76
cnot bell76 bell77
cnot b4 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c4
T c4
cnot b5 c4
T c4
cnot bell76 c4
T c4
H bell78
cnot bell78 bell79
cnot c3 bell79
measure bell79
cnot bell79 bell78
cnot bell78 c4
cnot b5 c4
cnot bell76 c4
cnot bell14 c4
T c4
cnot d4 c4
cnot b5 c4
cnot bell6 c4
T* c4
cnot bell78 c4
cnot bell76 c4
cnot bell14 c4
T c4
cnot d4 c4
cnot b5 c4
cnot bell6 c4
H c4
H bell80
cnot bell80 bell81
cnot b1 bell81
measure bell81
cnot bell81 bell80
cnot bell80 d0
T d0
H bell82
cnot bell82 bell83
cnot a1 bell83
measure bell83
cnot bell83 bell82
cnot bell82 d0
H bell84
cnot bell84 bell85
cnot e bell85
measure bell85
cnot bell85 bell84
cnot bell84 d0
cnot b0 d0
cnot a0 d0
cnot bell84 d0
H bell84
measure bell84
cz bell84 e
cnot bell80 d0
cnot b0 d0
cnot bell82 d0
H bell82
measure bell82
cz bell82 a1
cnot a0 d0
H d0
H bell86
cnot bell86 bell87
cnot b2 bell87
measure bell87
cnot bell87 bell86
cnot bell86 d1
S d1
H bell88
cnot bell88 bell89
cnot a2 bell89
measure bell89
cnot bell89 bell88
cnot bell88 d1
S* d1
cnot bell86 d1
H bell86
measure bell86
cz bell86 b2
cnot bell88 d1
H bell88
measure bell88
cz bell88 a2
H d1
cnot b5 d4
T d4
cnot bell6 d4
cnot bell78 d4
cnot bell76 d4
cnot bell14 d4
cnot bell78 d4
cnot b5 d4
cnot bell76 d4
cnot bell6 d4
cnot bell14 d4
H bell14
measure bell14
cz bell14 a4
H d4
H bell90
cnot bell90 bell91
cnot b6 bell91
measure bell91
cnot bell91 bell90
cnot bell90 d5
T d5
H bell92
cnot bell92 bell93
cnot a6 bell93
measure bell93
cnot bell93 bell92
cnot bell92 d5
S* d5
cnot bell58 d5
T d5
cnot bell58 d5
H bell58
measure bell58
cz bell58 c5
cnot bell90 d5
H bell90
measure bell90
cz bell90 b6
cnot bell92 d5
H bell92
measure bell92
cz bell92 a6
H d5
T d1
cnot c0 d1
T* d1
H bell94
cnot bell94 bell95
cnot e bell95
measure bell95
cnot bell95 bell94
cnot bell94 d1
T d1
cnot c0 d1
T* d1
cnot bell94 d1
H bell94
measure bell94
cz bell94 e
H d1
cnot c0 c1
T* c1
H bell96
cnot bell96 bell97
cnot c2 bell97
measure bell97
cnot bell97 bell96
cnot bell96 c1
T c1
cnot c0 c1
T* c1
cnot bell96 c1
H c1
T d0
cnot b0 d0
T d0
H bell98
cnot bell98 bell99
cnot e bell99
measure bell99
cnot bell99 bell98
cnot bell98 d0
T* d0
cnot b0 d0
T* d0
cnot bell98 d0
H bell98
measure bell98
cz bell98 e
H d0
T d4
cnot bell76 d4
T d4
cnot bell78 d4
T* d4
cnot bell76 d4
H bell76
measure bell76
cz bell76 b4
T* d4
cnot bell78 d4
H d4
H bell100
cnot bell100 bell101
cnot b6 bell101
measure bell101
cnot bell101 bell100
cnot bell100 c5
T c5
H bell102
cnot bell102 bell103
cnot c4 bell103
measure bell103
cnot bell103 bell102
cnot bell102 c5
T* c5
cnot bell100 c5
H bell100
measure bell100
cz bell100 b6
T* c5
cnot bell102 c5
H c5
T d5
cnot bell78 d5
T* d5
cnot c4 d5
T d5
cnot bell78 d5
H bell78
measure bell78
cz bell78 c3
T* d5
cnot c4 d5
H d5
H bell104
cnot bell104 bell105
cnot b4 bell105
measure bell105
cnot bell105 bell104
cnot bell104 c3
S c3
H bell106
cnot bell106 bell107
cnot a4 bell107
measure bell107
cnot bell107 bell106
cnot bell106 c3
S* c3
cnot bell102 c3
cnot bell104 c3
H bell104
measure bell104
cz bell104 b4
cnot bell106 c3
H bell106
measure bell106
cz bell106 a4
T* c3
cnot bell102 c3
H bell102
measure bell102
cz bell102 c4
H c3
H bell108
cnot bell108 bell109
cnot c1 bell109
measure bell109
cnot bell109 bell108
cnot bell108 e
T* e
cnot c3 e
T e
cnot bell108 e
T* e
H bell110
cnot bell110 bell111
cnot b0 bell111
measure bell111
cnot bell111 bell110
cnot bell110 e
cnot c3 e
S e
H bell112
cnot bell112 bell113
cnot a0 bell113
measure bell113
cnot bell113 bell112
cnot bell112 e
S* e
H bell114
cnot bell114 bell115
cnot c0 bell115
measure bell115
cnot bell115 bell114
cnot bell114 e
cnot bell110 e
H bell110
measure bell110
cz bell110 b0
cnot bell112 e
H bell112
measure bell112
cz bell112 a0
T* e
cnot bell114 e
H bell114
measure bell114
cz bell114 c0
H e
T c3
cnot bell108 c3
T* c3
cnot bell108 c3
H bell108
measure bell108
cz bell108 c1
H c3
T c3
cnot c5 c3
T* c3
cnot e c3
T c3
cnot c5 c3
T* c3
cnot e c3
H c3
T c1
H c1
T d1
cnot bell96 d1
T* d1
H bell116
cnot bell116 bell117
cnot c3 bell117
measure bell117
cnot bell117 bell116
cnot bell116 d1
T d1
cnot bell96 d1
T* d1
cnot bell116 d1
H bell116
measure bell116
cz bell116 c3
H d1
T c5
cnot e c5
T* c5
cnot e c5
H c5
T d5
H bell118
cnot bell118 bell119
cnot b6 bell119
measure bell119
cnot bell119 bell118
cnot bell118 d5
T d5
H bell120
cnot bell120 bell121
cnot e bell121
measure bell121
cnot bell121 bell120
cnot bell120 d5
T* d5
cnot bell118 d5
T* d5
cnot bell120 d5
H bell120
measure bell120
cz bell120 e
H d5
T c0
cnot c1 c0
T c0
cnot bell96 c0
T* c0
cnot c1 c0
cnot bell96 c0
H bell96
measure bell96
cz bell96 c2
H c0
T* d0
cnot bell80 d0
T* d0
H bell122
cnot bell122 bell123
cnot d1 bell123
measure bell123
cnot bell123 bell122
cnot bell122 d0
T d0
cnot bell80 d0
H bell80
measure bell80
cz bell80 b1
T d0
cnot bell122 d0
H bell122
measure bell122
cz bell122 d1
H d0
T c2
H bell124
cnot bell124 bell125
cnot c1 bell125
measure bell125
cnot bell125 bell124
cnot bell124 c2
T c2
H bell126
cnot bell126 bell127
cnot c3 bell127
measure bell127
cnot bell127 bell126
cnot bell126 c2
cnot bell124 c2
H bell124
measure bell124
cz bell124 c1
T* c2
cnot bell126 c2
H c2
T* d2
cnot b3 d2
T* d2
cnot bell126 d2
T d2
cnot b3 d2
T d2
cnot bell126 d2
H bell126
measure bell126
cz bell126 c3
H d2
T c4
cnot bell118 c4
H bell128
cnot bell128 bell129
cnot c5 bell129
measure bell129
cnot bell129 bell128
cnot bell128 c4
T c4
cnot bell118 c4
H bell118
measure bell118
cz bell118 b6
T c4
cnot bell128 c4
H bell128
measure bell128
cz bell128 c5
H c4
T* d4
cnot b5 d4
T* d4
cnot d5 d4
T d4
cnot b5 d4
T d4
cnot d5 d4
H d4
T e
H bell130
cnot bell130 bell131
cnot a6 bell131
measure bell131
cnot bell131 bell130
cnot bell130 e
T e
H bell132
cnot bell132 bell133
cnot b6 bell133
measure bell133
cnot bell133 bell132
cnot bell132 e
T* e
cnot bell130 e
S e
cnot bell132 e
H bell132
measure bell132
cz bell132 b6
cnot a6 b6
cnot bell6 b5
cnot a4 b4
cnot bell62 b3
H bell134
cnot bell134 bell135
cnot a2 bell135
measure bell135
cnot bell135 bell134
cnot bell134 b2
H bell136
cnot bell136 bell137
cnot a1 bell137
measure bell137
cnot bell137 bell136
cnot bell136 b1
cnot a0 b0
H e
T* c0
H bell138
cnot bell138 bell139
cnot b0 bell139
measure bell139
cnot bell139 bell138
cnot bell138 c0
H bell140
cnot bell140 bell141
cnot a0 bell141
measure bell141
cnot bell141 bell140
cnot bell140 c0
T* c0
cnot b1 c0
cnot bell136 c0
T* c0
cnot bell138 c0
H bell138
measure bell138
cz bell138 b0
cnot bell140 c0
H bell140
measure bell140
cz bell140 a0
T* c0
cnot b1 c0
cnot bell136 c0
H c0
T* d0
cnot a0 d0
T d0
cnot b0 d0
T d0
cnot a0 d0
T* d0
cnot b0 d0
H d0
T* c1
H c1
S* d1
cnot bell136 d1
T d1
cnot b1 d1
cnot bell136 d1
H bell136
measure bell136
cz bell136 a1
T* d1
cnot b1 d1
H d1
T* c2
cnot b2 c2
cnot bell134 c2
T* c2
cnot b3 c2
cnot bell62 c2
T* c2
cnot b2 c2
cnot bell134 c2
T* c2
cnot b3 c2
cnot bell62 c2
H bell62
measure bell62
cz bell62 a3
H c2
T* d2
cnot bell134 d2
T d2
cnot b2 d2
T d2
cnot bell134 d2
T* d2
cnot b2 d2
H d2
T* c3
H bell142
cnot bell142 bell143
cnot a3 bell143
measure bell143
cnot bell143 bell142
cnot bell142 c3
T c3
H bell144
cnot bell144 bell145
cnot b3 bell145
measure bell145
cnot bell145 bell144
cnot bell144 c3
cnot bell142 c3
H bell142
measure bell142
cz bell142 a3
T* c3
cnot bell144 c3
H bell144
measure bell144
cz bell144 b3
H c3
T* c4
H bell146
cnot bell146 bell147
cnot b4 bell147
measure bell147
cnot bell147 bell146
cnot bell146 c4
H bell148
cnot bell148 bell149
cnot a4 bell149
measure bell149
cnot bell149 bell148
cnot bell148 c4
T* c4
cnot b5 c4
cnot bell6 c4
T* c4
cnot bell146 c4
cnot bell148 c4
T* c4
cnot b5 c4
cnot bell6 c4
H c4
T* d4
cnot bell148 d4
T d4
cnot bell146 d4
T d4
cnot bell148 d4
H bell148
measure bell148
cz bell148 a4
T* d4
cnot bell146 d4
H bell146
measure bell146
cz bell146 b4
H d4
T* c5
H bell150
cnot bell150 bell151
cnot b6 bell151
measure bell151
cnot bell151 bell150
cnot bell150 c5
cnot bell130 c5
T* c5
cnot bell150 c5
H bell150
measure bell150
cz bell150 b6
cnot bell130 c5
H bell130
measure bell130
cz bell130 a6
H c5
S* d5
cnot bell6 d5
T d5
cnot b5 d5
cnot bell6 d5
H bell6
measure bell6
cz bell6 a5
T* d5
cnot b5 d5
H d5
S b0
cnot a0 b0
S* b0
T b1
S b2
cnot bell134 b2
S* b2
T b3
S b4
cnot a4 b4
S* b4
T b5
T b6
cnot a6 b6
S* b6
cnot a6 b6
cnot a4 b4
cnot bell134 b2
H bell134
measure bell134
cz bell134 a2
cnot a0 b0
X b0
X b1
X b2
X b3
X b4
X b5
X b6
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
reset bell132
reset bell133
reset bell134
reset bell135
reset bell136
reset bell137
reset bell138
reset bell139
reset bell140
reset bell141
reset bell142
reset bell143
reset bell144
reset bell145
reset bell146
reset bell147
reset bell148
reset bell149
reset bell150
reset bell151
END
