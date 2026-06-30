# Hyperedge cut (ebits): 43

# Actual ebits used (Synthesis): 89
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/csla_mux_3.qc):
#   Qubits: 15
#   H: 20
#   T: 70
#   cnot: 80
#   Depth: 58
#   T depth: 26
# Result (20.249ms):
#   Qubits: 193
#   H: 198
#   T: 62
#   cnot: 389
#   cz: 95
#   measure: 178
#   reset: 181
#   swap: 7
#   Depth: 272
#   T depth: 29


# Result Circuit
.v cin a0 b0 c0 d0 a1 b1 c1 d1 e1 a2 b2 c2 d2 e2 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i cin a0 b0 a1 b1 a2 b2
.o cin a0 b0 c0 d0 a1 b1 c1 d1 e1 a2 b2 c2 d2 e2
BEGIN 
H c0
H c1
H c2
T c0
H bell0
cnot bell0 bell1
cnot a0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
H bell2
cnot bell2 bell3
cnot b0 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
T c0
cnot bell0 c0
H bell0
measure bell0
cz bell0 a0
T* c0
cnot bell2 c0
H bell2
measure bell2
cz bell2 b0
H c0
T c1
H bell4
cnot bell4 bell5
cnot a1 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c1
T* c1
H bell6
cnot bell6 bell7
cnot b1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c1
T c1
cnot bell4 c1
H bell4
measure bell4
cz bell4 a1
T* c1
cnot bell6 c1
H bell6
measure bell6
cz bell6 b1
H c1
T c2
H bell8
cnot bell8 bell9
cnot a2 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c2
T* c2
H bell10
cnot bell10 bell11
cnot b2 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c2
T c2
cnot bell8 c2
H bell8
measure bell8
cz bell8 a2
T* c2
cnot bell10 c2
H bell10
measure bell10
cz bell10 b2
H c2
H bell12
cnot bell12 bell13
cnot c2 bell13
measure bell13
cnot bell13 bell12
cnot bell12 e2
H bell12
measure bell12
cz bell12 c2
H bell14
cnot bell14 bell15
cnot c1 bell15
measure bell15
cnot bell15 bell14
cnot bell14 e1
H bell14
measure bell14
cz bell14 c1
H bell16
cnot bell16 bell17
cnot c0 bell17
measure bell17
cnot bell17 bell16
cnot bell16 d0
H bell16
measure bell16
cz bell16 c0
H bell18
cnot bell18 bell19
cnot a2 bell19
measure bell19
cnot bell19 bell18
cnot bell18 b2
H bell18
measure bell18
cz bell18 a2
H bell20
cnot bell20 bell21
cnot a1 bell21
measure bell21
cnot bell21 bell20
cnot bell20 b1
H bell20
measure bell20
cz bell20 a1
H bell22
cnot bell22 bell23
cnot a0 bell23
measure bell23
cnot bell23 bell22
cnot bell22 b0
H bell22
measure bell22
cz bell22 a0
H c1
H e1
H c2
H e2
T e1
H bell24
cnot bell24 bell25
cnot b1 bell25
measure bell25
cnot bell25 bell24
cnot bell24 e1
T* e1
H bell26
cnot bell26 bell27
cnot c0 bell27
measure bell27
cnot bell27 bell26
cnot bell26 e1
T e1
cnot bell24 e1
H bell24
measure bell24
cz bell24 b1
T* e1
swap d0 d2
cnot bell26 e1
H bell26
measure bell26
cz bell26 c0
H bell28
cnot bell28 bell29
cnot c0 bell29
measure bell29
cnot bell29 bell28
cnot bell28 d2
H bell28
measure bell28
cz bell28 c0
H bell30
cnot bell30 bell31
cnot c0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 d0
H bell30
measure bell30
cz bell30 c0
H bell32
cnot bell32 bell33
cnot d2 bell33
measure bell33
cnot bell33 bell32
cnot bell32 b2
H bell32
measure bell32
cz bell32 d2
H bell34
cnot bell34 bell35
cnot b2 bell35
measure bell35
cnot bell35 bell34
cnot bell34 d2
H bell34
measure bell34
cz bell34 b2
H bell36
cnot bell36 bell37
cnot b0 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c0
H bell36
measure bell36
cz bell36 b0
H e1
T* c1
H bell38
cnot bell38 bell39
cnot b1 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c1
T c1
H bell40
cnot bell40 bell41
cnot c0 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c1
T* c1
cnot bell38 c1
H bell38
measure bell38
cz bell38 b1
T c1
cnot bell40 c1
H bell40
measure bell40
cz bell40 c0
H c1
T c2
H bell42
cnot bell42 bell43
cnot b2 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c2
T* c2
H bell44
cnot bell44 bell45
cnot c1 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c2
H bell44
measure bell44
cz bell44 c1
T c2
cnot bell42 c2
H bell42
measure bell42
cz bell42 b2
T* c2
H bell46
cnot bell46 bell47
cnot c0 bell47
measure bell47
cnot bell47 bell46
cnot bell46 b1
H bell46
measure bell46
cz bell46 c0
H bell48
cnot bell48 bell49
cnot d2 bell49
measure bell49
cnot bell49 bell48
cnot bell48 b2
H bell48
measure bell48
cz bell48 d2
H bell50
cnot bell50 bell51
cnot d1 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c1
H bell50
measure bell50
cz bell50 d1
H bell52
cnot bell52 bell53
cnot d1 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c2
H bell52
measure bell52
cz bell52 d1
H bell54
cnot bell54 bell55
cnot d2 bell55
measure bell55
cnot bell55 bell54
cnot bell54 d1
H bell54
measure bell54
cz bell54 d2
H bell56
cnot bell56 bell57
cnot e1 bell57
measure bell57
cnot bell57 bell56
cnot bell56 d2
H bell56
measure bell56
cz bell56 e1
H bell58
cnot bell58 bell59
cnot c1 bell59
measure bell59
cnot bell59 bell58
cnot bell58 d1
H bell58
measure bell58
cz bell58 c1
H bell60
cnot bell60 bell61
cnot c1 bell61
measure bell61
cnot bell61 bell60
cnot bell60 c2
H bell60
measure bell60
cz bell60 c1
swap b2 d1
H bell62
cnot bell62 bell63
cnot b1 bell63
measure bell63
cnot bell63 bell62
cnot bell62 d1
H bell62
measure bell62
cz bell62 b1
H bell64
cnot bell64 bell65
cnot b0 bell65
measure bell65
cnot bell65 bell64
cnot bell64 d1
H bell64
measure bell64
cz bell64 b0
H c2
T* e2
H bell66
cnot bell66 bell67
cnot c1 bell67
measure bell67
cnot bell67 bell66
cnot bell66 e2
H bell68
cnot bell68 bell69
cnot b2 bell69
measure bell69
cnot bell69 bell68
cnot bell68 e2
T e2
H bell70
cnot bell70 bell71
cnot d2 bell71
measure bell71
cnot bell71 bell70
cnot bell70 e2
T e2
cnot bell66 e2
H bell66
measure bell66
cz bell66 c1
cnot bell68 e2
H bell68
measure bell68
cz bell68 b2
T* e2
cnot bell70 e2
H bell70
measure bell70
cz bell70 d2
H e2
H bell72
cnot bell72 bell73
cnot d2 bell73
measure bell73
cnot bell73 bell72
cnot bell72 b2
H bell72
measure bell72
cz bell72 d2
H bell74
cnot bell74 bell75
cnot e1 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c1
H bell74
measure bell74
cz bell74 e1
H bell76
cnot bell76 bell77
cnot e2 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c2
H bell76
measure bell76
cz bell76 e2
H bell78
cnot bell78 bell79
cnot e1 bell79
measure bell79
cnot bell79 bell78
cnot bell78 d1
H bell78
measure bell78
cz bell78 e1
swap d1 e1
swap c1 d1
H bell80
cnot bell80 bell81
cnot b2 bell81
measure bell81
cnot bell81 bell80
cnot bell80 d1
H bell80
measure bell80
cz bell80 b2
H bell82
cnot bell82 bell83
cnot b2 bell83
measure bell83
cnot bell83 bell82
cnot bell82 c1
H bell82
measure bell82
cz bell82 b2
H bell84
cnot bell84 bell85
cnot b1 bell85
measure bell85
cnot bell85 bell84
cnot bell84 e1
H bell84
measure bell84
cz bell84 b1
swap b1 d1
H bell86
cnot bell86 bell87
cnot b0 bell87
measure bell87
cnot bell87 bell86
cnot bell86 e1
H bell86
measure bell86
cz bell86 b0
H bell88
cnot bell88 bell89
cnot b0 bell89
measure bell89
cnot bell89 bell88
cnot bell88 d1
H bell88
measure bell88
cz bell88 b0
H bell90
cnot bell90 bell91
cnot b0 bell91
measure bell91
cnot bell91 bell90
cnot bell90 b1
H bell90
measure bell90
cz bell90 b0
H e2
T d2
H bell92
cnot bell92 bell93
cnot b2 bell93
measure bell93
cnot bell93 bell92
cnot bell92 d2
T* d2
H bell94
cnot bell94 bell95
cnot c1 bell95
measure bell95
cnot bell95 bell94
cnot bell94 d2
T* d2
H bell96
cnot bell96 bell97
cnot a2 bell97
measure bell97
cnot bell97 bell96
cnot bell96 d2
T d2
cnot bell94 d2
H bell94
measure bell94
cz bell94 c1
cnot bell92 d2
cnot bell96 d2
H bell96
measure bell96
cz bell96 a2
H d2
T* d1
H bell98
cnot bell98 bell99
cnot b0 bell99
measure bell99
cnot bell99 bell98
cnot bell98 d1
T d1
H bell100
cnot bell100 bell101
cnot c0 bell101
measure bell101
cnot bell101 bell100
cnot bell100 d1
T* d1
H bell102
cnot bell102 bell103
cnot a1 bell103
measure bell103
cnot bell103 bell102
cnot bell102 d1
T d1
cnot bell100 d1
H bell100
measure bell100
cz bell100 c0
cnot bell98 d1
cnot bell102 d1
H bell102
measure bell102
cz bell102 a1
H d1
T e2
H bell104
cnot bell104 bell105
cnot c2 bell105
measure bell105
cnot bell105 bell104
cnot bell104 e2
T* e2
H bell106
cnot bell106 bell107
cnot cin bell107
measure bell107
cnot bell107 bell106
cnot bell106 e2
T e2
cnot bell104 e2
H bell104
measure bell104
cz bell104 c2
T* e2
cnot bell106 e2
H bell106
measure bell106
cz bell106 cin
H e2
T* d2
cnot bell92 d2
T d2
H bell108
cnot bell108 bell109
cnot cin bell109
measure bell109
cnot bell109 bell108
cnot bell108 d2
T* d2
cnot bell92 d2
H bell92
measure bell92
cz bell92 b2
T d2
cnot bell108 d2
H bell108
measure bell108
cz bell108 cin
H d2
T d1
cnot bell98 d1
T* d1
H bell110
cnot bell110 bell111
cnot cin bell111
measure bell111
cnot bell111 bell110
cnot bell110 d1
T d1
cnot bell98 d1
H bell98
measure bell98
cz bell98 b0
T* d1
cnot bell110 d1
H bell110
measure bell110
cz bell110 cin
H d1
T a0
H bell112
cnot bell112 bell113
cnot a0 bell113
measure bell113
cnot bell113 bell112
cnot bell112 b0
H bell112
measure bell112
cz bell112 a0
T b0
T cin
H bell114
cnot bell114 bell115
cnot b0 bell115
measure bell115
cnot bell115 bell114
cnot bell114 cin
H bell114
measure bell114
cz bell114 b0
H bell116
cnot bell116 bell117
cnot a0 bell117
measure bell117
cnot bell117 bell116
cnot bell116 cin
H bell116
measure bell116
cz bell116 a0
T* cin
T* b2
H bell118
cnot bell118 bell119
cnot cin bell119
measure bell119
cnot bell119 bell118
cnot bell118 b2
H bell120
cnot bell120 bell121
cnot b0 bell121
measure bell121
cnot bell121 bell120
cnot bell120 b2
H bell120
measure bell120
cz bell120 b0
H bell122
cnot bell122 bell123
cnot a0 bell123
measure bell123
cnot bell123 bell122
cnot bell122 b2
H bell122
measure bell122
cz bell122 a0
T b2
T* c0
H bell124
cnot bell124 bell125
cnot b0 bell125
measure bell125
cnot bell125 bell124
cnot bell124 c0
H bell124
measure bell124
cz bell124 b0
H bell126
cnot bell126 bell127
cnot a0 bell127
measure bell127
cnot bell127 bell126
cnot bell126 c0
H bell126
measure bell126
cz bell126 a0
T c0
T c1
H bell128
cnot bell128 bell129
cnot c1 bell129
measure bell129
cnot bell129 bell128
cnot bell118 bell128
H bell118
measure bell118
cz bell118 cin
cnot b2 bell128
H bell130
cnot bell130 bell131
cnot b0 bell131
measure bell131
cnot bell131 bell130
cnot bell130 bell128
H bell130
measure bell130
cz bell130 b0
H bell132
cnot bell132 bell133
cnot a0 bell133
measure bell133
cnot bell133 bell132
cnot bell132 bell128
H bell134
cnot bell134 bell135
cnot bell128 bell135
measure bell135
cnot bell135 bell134
reset bell135
cnot c1 bell134
cnot bell134 c1
H bell134
measure bell134
cz bell134 a0
cz bell134 b0
cz bell134 b2
cz bell134 cin
H bell128
measure bell128
cz bell128 c1
H bell132
measure bell132
cz bell132 a0
T* c1
T c2
H bell136
cnot bell136 bell137
cnot c2 bell137
measure bell137
cnot bell137 bell136
cnot cin bell136
H bell138
cnot bell138 bell139
cnot b0 bell139
measure bell139
cnot bell139 bell138
cnot bell138 bell136
H bell138
measure bell138
cz bell138 b0
H bell140
cnot bell140 bell141
cnot a0 bell141
measure bell141
cnot bell141 bell140
cnot bell140 bell136
H bell142
cnot bell142 bell143
cnot bell136 bell143
measure bell143
cnot bell143 bell142
reset bell143
cnot c2 bell142
cnot bell142 c2
H bell142
measure bell142
cz bell142 a0
cz bell142 b0
cz bell142 cin
H bell136
measure bell136
cz bell136 c2
H bell140
measure bell140
cz bell140 a0
T* c2
T a1
T a2
H bell144
cnot bell144 bell145
cnot d1 bell145
measure bell145
cnot bell145 bell144
cnot bell144 a0
H bell144
measure bell144
cz bell144 d1
H bell146
cnot bell146 bell147
cnot b1 bell147
measure bell147
cnot bell147 bell146
cnot bell146 b0
H bell146
measure bell146
cz bell146 b1
H bell148
cnot bell148 bell149
cnot d1 bell149
measure bell149
cnot bell149 bell148
cnot bell148 b1
H bell148
measure bell148
cz bell148 d1
H bell150
cnot bell150 bell151
cnot d2 bell151
measure bell151
cnot bell151 bell150
cnot bell150 b2
H bell152
cnot bell152 bell153
cnot d1 bell153
measure bell153
cnot bell153 bell152
cnot bell152 c0
H bell152
measure bell152
cz bell152 d1
H bell154
cnot bell154 bell155
cnot c1 bell155
measure bell155
cnot bell155 bell154
cnot bell150 bell154
H bell150
measure bell150
cz bell150 d2
H bell156
cnot bell156 bell157
cnot d1 bell157
measure bell157
cnot bell157 bell156
cnot bell156 cin
H bell156
measure bell156
cz bell156 d1
H bell158
cnot bell158 bell159
cnot e2 bell159
measure bell159
cnot bell159 bell158
cnot bell158 c2
H bell158
measure bell158
cz bell158 e2
H bell160
cnot bell160 bell161
cnot cin bell161
measure bell161
cnot bell161 bell160
cnot bell160 c2
H bell160
measure bell160
cz bell160 cin
H bell162
cnot bell162 bell163
cnot cin bell163
measure bell163
cnot bell163 bell162
cnot bell162 d1
H bell162
measure bell162
cz bell162 cin
H bell164
cnot bell164 bell165
cnot cin bell165
measure bell165
cnot bell165 bell164
cnot bell164 b2
H bell164
measure bell164
cz bell164 cin
H bell166
cnot bell166 bell167
cnot b1 bell167
measure bell167
cnot bell167 bell166
cnot bell166 b2
H bell166
measure bell166
cz bell166 b1
H bell168
cnot bell168 bell169
cnot b1 bell169
measure bell169
cnot bell169 bell168
cnot bell168 cin
H bell168
measure bell168
cz bell168 b1
H bell170
cnot bell170 bell171
cnot b1 bell171
measure bell171
cnot bell171 bell170
cnot bell170 c2
H bell170
measure bell170
cz bell170 b1
cnot b2 bell154
H bell172
cnot bell172 bell173
cnot bell154 bell173
measure bell173
cnot bell173 bell172
reset bell173
cnot c1 bell172
cnot bell172 c1
H bell172
measure bell172
cz bell172 b2
cz bell172 d2
H bell154
measure bell154
cz bell154 c1
H bell174
cnot bell174 bell175
cnot b1 bell175
measure bell175
cnot bell175 bell174
cnot bell174 c0
H bell174
measure bell174
cz bell174 b1
swap b0 d1
H bell176
cnot bell176 bell177
cnot d1 bell177
measure bell177
cnot bell177 bell176
cnot bell176 a0
H bell176
measure bell176
cz bell176 d1
swap a0 d1
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
reset bell152
reset bell153
reset bell154
reset bell155
reset bell156
reset bell157
reset bell158
reset bell159
reset bell160
reset bell161
reset bell162
reset bell163
reset bell164
reset bell165
reset bell166
reset bell167
reset bell168
reset bell169
reset bell170
reset bell171
reset bell172
reset bell173
reset bell174
reset bell175
reset bell176
reset bell177
END
