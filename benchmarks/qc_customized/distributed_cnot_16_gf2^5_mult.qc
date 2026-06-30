# Hyperedge cut (ebits): 28

# Actual ebits used (Synthesis): 107
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^5_mult.qc):
#   Qubits: 15
#   H: 18
#   T: 175
#   cnot: 154
#   Depth: 111
#   T depth: 54
# Result (20.888ms):
#   Qubits: 229
#   H: 232
#   T: 115
#   Z: 3
#   cnot: 489
#   cz: 108
#   measure: 214
#   reset: 215
#   Depth: 315
#   T depth: 51


# Result Circuit
.v a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
.o a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
BEGIN 
H c0
H c1
H c2
H c3
H bell0
cnot bell0 bell1
cnot a4 bell1
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
H bell0
measure bell0
cz bell0 a4
T* c0
H bell4
cnot bell4 bell5
cnot a3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
cnot bell2 c0
H bell2
measure bell2
cz bell2 b1
T* c0
H bell6
cnot bell6 bell7
cnot b2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
T c0
cnot bell4 c0
H bell4
measure bell4
cz bell4 a3
T* c0
H bell8
cnot bell8 bell9
cnot a2 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
cnot bell6 c0
H bell6
measure bell6
cz bell6 b2
T c0
H bell10
cnot bell10 bell11
cnot b3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
T* c0
cnot bell8 c0
H bell8
measure bell8
cz bell8 a2
T c0
H bell12
cnot bell12 bell13
cnot a1 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
cnot bell10 c0
H bell10
measure bell10
cz bell10 b3
T c0
H bell14
cnot bell14 bell15
cnot b4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
T* c0
cnot bell12 c0
H bell12
measure bell12
cz bell12 a1
T c0
cnot bell14 c0
H bell14
measure bell14
cz bell14 b4
H c0
T c1
H bell16
cnot bell16 bell17
cnot a4 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c1
T* c1
H bell18
cnot bell18 bell19
cnot b2 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c1
T c1
cnot bell16 c1
H bell16
measure bell16
cz bell16 a4
T* c1
H bell20
cnot bell20 bell21
cnot a3 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c1
cnot bell18 c1
H bell18
measure bell18
cz bell18 b2
T c1
H bell22
cnot bell22 bell23
cnot b3 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c1
T* c1
cnot bell20 c1
H bell20
measure bell20
cz bell20 a3
T c1
H bell24
cnot bell24 bell25
cnot a2 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c1
cnot bell22 c1
H bell22
measure bell22
cz bell22 b3
T* c1
H bell26
cnot bell26 bell27
cnot b4 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c1
T c1
cnot bell24 c1
H bell24
measure bell24
cz bell24 a2
T* c1
cnot bell26 c1
H bell26
measure bell26
cz bell26 b4
H c1
H bell28
cnot bell28 bell29
cnot a4 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c2
T* c2
H bell30
cnot bell30 bell31
cnot b3 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c2
T c2
cnot bell28 c2
H bell28
measure bell28
cz bell28 a4
T* c2
H bell32
cnot bell32 bell33
cnot a3 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c2
cnot bell30 c2
H bell30
measure bell30
cz bell30 b3
T c2
H bell34
cnot bell34 bell35
cnot b4 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c2
T* c2
cnot bell32 c2
H bell32
measure bell32
cz bell32 a3
T c2
cnot bell34 c2
H bell34
measure bell34
cz bell34 b4
H c2
T* c3
H bell36
cnot bell36 bell37
cnot a4 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c3
T c3
H bell38
cnot bell38 bell39
cnot b4 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c3
T* c3
cnot bell36 c3
H bell36
measure bell36
cz bell36 a4
T c3
cnot bell38 c3
H bell38
measure bell38
cz bell38 b4
H c3
H bell40
cnot bell40 bell41
cnot c3 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c0
H bell40
measure bell40
cz bell40 c3
H bell42
cnot bell42 bell43
cnot c2 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c4
H bell42
measure bell42
cz bell42 c2
H bell44
cnot bell44 bell45
cnot c1 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c3
H bell44
measure bell44
cz bell44 c1
H bell46
cnot bell46 bell47
cnot c0 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c2
H bell46
measure bell46
cz bell46 c0
H c0
H c1
H c2
H c3
H c4
T c0
H bell48
cnot bell48 bell49
cnot a0 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c0
T* c0
H bell50
cnot bell50 bell51
cnot b0 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c0
T c0
cnot bell48 c0
H bell48
measure bell48
cz bell48 a0
T* c0
cnot bell50 c0
H bell50
measure bell50
cz bell50 b0
H c0
H bell52
cnot bell52 bell53
cnot a1 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c1
T* c1
H bell54
cnot bell54 bell55
cnot b0 bell55
measure bell55
cnot bell55 bell54
cnot bell54 c1
T c1
cnot bell52 c1
H bell52
measure bell52
cz bell52 a1
T* c1
H bell56
cnot bell56 bell57
cnot a0 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c1
cnot bell54 c1
H bell54
measure bell54
cz bell54 b0
T c1
H bell58
cnot bell58 bell59
cnot b1 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c1
T* c1
cnot bell56 c1
H bell56
measure bell56
cz bell56 a0
T c1
cnot bell58 c1
H bell58
measure bell58
cz bell58 b1
H c1
T c2
H bell60
cnot bell60 bell61
cnot a2 bell61
measure bell61
cnot bell61 bell60
cnot bell60 c2
T* c2
H bell62
cnot bell62 bell63
cnot b0 bell63
measure bell63
cnot bell63 bell62
cnot bell62 c2
T c2
cnot bell60 c2
H bell60
measure bell60
cz bell60 a2
T* c2
H bell64
cnot bell64 bell65
cnot a1 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c2
cnot bell62 c2
H bell62
measure bell62
cz bell62 b0
T c2
H bell66
cnot bell66 bell67
cnot b1 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c2
T* c2
cnot bell64 c2
H bell64
measure bell64
cz bell64 a1
T c2
H bell68
cnot bell68 bell69
cnot a0 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c2
cnot bell66 c2
H bell66
measure bell66
cz bell66 b1
T* c2
H bell70
cnot bell70 bell71
cnot b2 bell71
measure bell71
cnot bell71 bell70
cnot bell70 c2
T c2
cnot bell68 c2
H bell68
measure bell68
cz bell68 a0
T* c2
cnot bell70 c2
H bell70
measure bell70
cz bell70 b2
H c2
H bell72
cnot bell72 bell73
cnot a3 bell73
measure bell73
cnot bell73 bell72
cnot bell72 c3
T* c3
H bell74
cnot bell74 bell75
cnot b0 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c3
T c3
cnot bell72 c3
H bell72
measure bell72
cz bell72 a3
T* c3
H bell76
cnot bell76 bell77
cnot a2 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c3
cnot bell74 c3
H bell74
measure bell74
cz bell74 b0
T* c3
H bell78
cnot bell78 bell79
cnot b1 bell79
measure bell79
cnot bell79 bell78
cnot bell78 c3
T c3
cnot bell76 c3
H bell76
measure bell76
cz bell76 a2
T* c3
H bell80
cnot bell80 bell81
cnot a1 bell81
measure bell81
cnot bell81 bell80
cnot bell80 c3
cnot bell78 c3
H bell78
measure bell78
cz bell78 b1
T c3
H bell82
cnot bell82 bell83
cnot b2 bell83
measure bell83
cnot bell83 bell82
cnot bell82 c3
T* c3
cnot bell80 c3
H bell80
measure bell80
cz bell80 a1
T c3
H bell84
cnot bell84 bell85
cnot a0 bell85
measure bell85
cnot bell85 bell84
cnot bell84 c3
cnot bell82 c3
H bell82
measure bell82
cz bell82 b2
T c3
H bell86
cnot bell86 bell87
cnot b3 bell87
measure bell87
cnot bell87 bell86
cnot bell86 c3
T* c3
cnot bell84 c3
H bell84
measure bell84
cz bell84 a0
T c3
cnot bell86 c3
H bell86
measure bell86
cz bell86 b3
H c3
T* c4
Z c4
H bell88
cnot bell88 bell89
cnot a4 bell89
measure bell89
cnot bell89 bell88
cnot bell88 c4
T* c4
H bell90
cnot bell90 bell91
cnot b0 bell91
measure bell91
cnot bell91 bell90
cnot bell90 c4
T c4
cnot bell88 c4
H bell88
measure bell88
cz bell88 a4
T* c4
H bell92
cnot bell92 bell93
cnot a3 bell93
measure bell93
cnot bell93 bell92
cnot bell92 c4
cnot bell90 c4
H bell90
measure bell90
cz bell90 b0
T* c4
H bell94
cnot bell94 bell95
cnot b1 bell95
measure bell95
cnot bell95 bell94
cnot bell94 c4
T c4
cnot bell92 c4
H bell92
measure bell92
cz bell92 a3
T* c4
H bell96
cnot bell96 bell97
cnot a2 bell97
measure bell97
cnot bell97 bell96
cnot bell96 c4
cnot bell94 c4
H bell94
measure bell94
cz bell94 b1
T c4
H bell98
cnot bell98 bell99
cnot b2 bell99
measure bell99
cnot bell99 bell98
cnot bell98 c4
T* c4
cnot bell96 c4
H bell96
measure bell96
cz bell96 a2
T c4
H bell100
cnot bell100 bell101
cnot a1 bell101
measure bell101
cnot bell101 bell100
cnot bell100 c4
cnot bell98 c4
H bell98
measure bell98
cz bell98 b2
T* c4
H bell102
cnot bell102 bell103
cnot b3 bell103
measure bell103
cnot bell103 bell102
cnot bell102 c4
T c4
cnot bell100 c4
H bell100
measure bell100
cz bell100 a1
T* c4
H bell104
cnot bell104 bell105
cnot a0 bell105
measure bell105
cnot bell105 bell104
cnot bell104 c4
cnot bell102 c4
H bell102
measure bell102
cz bell102 b3
T* c4
H bell106
cnot bell106 bell107
cnot b4 bell107
measure bell107
cnot bell107 bell106
cnot bell106 c4
T c4
cnot bell104 c4
H bell104
measure bell104
cz bell104 a0
T* c4
cnot bell106 c4
H bell106
measure bell106
cz bell106 b4
H c4
T a0
T* a1
T b0
Z b0
H bell108
cnot bell108 bell109
cnot a0 bell109
measure bell109
cnot bell109 bell108
cnot bell108 b0
T* b0
H bell110
cnot bell110 bell111
cnot a1 bell111
measure bell111
cnot bell111 bell110
cnot bell110 b0
H bell110
measure bell110
cz bell110 a1
cnot bell108 b0
H bell108
measure bell108
cz bell108 a0
T* b0
T b1
H bell112
cnot bell112 bell113
cnot a0 bell113
measure bell113
cnot bell113 bell112
cnot bell112 b1
T b1
H bell114
cnot bell114 bell115
cnot a1 bell115
measure bell115
cnot bell115 bell114
cnot bell114 b1
H bell114
measure bell114
cz bell114 a1
cnot bell112 b1
H bell112
measure bell112
cz bell112 a0
T b1
T a2
H bell116
cnot bell116 bell117
cnot b0 bell117
measure bell117
cnot bell117 bell116
cnot bell116 a2
H bell118
cnot bell118 bell119
cnot a1 bell119
measure bell119
cnot bell119 bell118
cnot bell118 a2
H bell118
measure bell118
cz bell118 a1
T* a2
H bell120
cnot bell120 bell121
cnot b1 bell121
measure bell121
cnot bell121 bell120
cnot bell120 a2
cnot bell116 a2
H bell116
measure bell116
cz bell116 b0
T* a2
T b2
H bell122
cnot bell122 bell123
cnot a0 bell123
measure bell123
cnot bell123 bell122
cnot bell122 b2
T* b2
H bell124
cnot bell124 bell125
cnot a1 bell125
measure bell125
cnot bell125 bell124
cnot bell124 b2
H bell124
measure bell124
cz bell124 a1
cnot bell122 b2
H bell122
measure bell122
cz bell122 a0
T b2
H bell126
cnot bell126 bell127
cnot b2 bell127
measure bell127
cnot bell127 bell126
cnot bell120 bell126
H bell120
measure bell120
cz bell120 b1
cnot a2 bell126
H bell128
cnot bell128 bell129
cnot bell126 bell129
measure bell129
cnot bell129 bell128
reset bell129
cnot b2 bell128
cnot bell128 b2
H bell128
measure bell128
cz bell128 a2
cz bell128 b1
H bell126
measure bell126
cz bell126 b2
T b2
T a3
H bell130
cnot bell130 bell131
cnot b0 bell131
measure bell131
cnot bell131 bell130
cnot bell130 a3
H bell132
cnot bell132 bell133
cnot a1 bell133
measure bell133
cnot bell133 bell132
cnot bell132 a3
H bell132
measure bell132
cz bell132 a1
T* a3
H bell134
cnot bell134 bell135
cnot b1 bell135
measure bell135
cnot bell135 bell134
cnot bell134 a3
H bell134
measure bell134
cz bell134 b1
cnot bell130 a3
H bell130
measure bell130
cz bell130 b0
T* a3
H bell136
cnot bell136 bell137
cnot b2 bell137
measure bell137
cnot bell137 bell136
cnot bell136 a3
H bell136
measure bell136
cz bell136 b2
H bell138
cnot bell138 bell139
cnot a2 bell139
measure bell139
cnot bell139 bell138
cnot bell138 a3
H bell138
measure bell138
cz bell138 a2
T* a3
T* b3
H bell140
cnot bell140 bell141
cnot a0 bell141
measure bell141
cnot bell141 bell140
cnot bell140 b3
T b3
H bell142
cnot bell142 bell143
cnot a1 bell143
measure bell143
cnot bell143 bell142
cnot bell142 b3
H bell142
measure bell142
cz bell142 a1
cnot bell140 b3
H bell140
measure bell140
cz bell140 a0
T* b3
H bell144
cnot bell144 bell145
cnot b1 bell145
measure bell145
cnot bell145 bell144
cnot bell144 b3
H bell144
measure bell144
cz bell144 b1
H bell146
cnot bell146 bell147
cnot a2 bell147
measure bell147
cnot bell147 bell146
cnot bell146 b3
H bell146
measure bell146
cz bell146 a2
T b3
H bell148
cnot bell148 bell149
cnot b2 bell149
measure bell149
cnot bell149 bell148
cnot bell148 b3
H bell148
measure bell148
cz bell148 b2
H bell150
cnot bell150 bell151
cnot a3 bell151
measure bell151
cnot bell151 bell150
cnot bell150 b3
H bell150
measure bell150
cz bell150 a3
T b3
T* a4
Z a4
H bell152
cnot bell152 bell153
cnot b0 bell153
measure bell153
cnot bell153 bell152
cnot bell152 a4
H bell154
cnot bell154 bell155
cnot a1 bell155
measure bell155
cnot bell155 bell154
cnot bell154 a4
H bell154
measure bell154
cz bell154 a1
T* a4
H bell156
cnot bell156 bell157
cnot b1 bell157
measure bell157
cnot bell157 bell156
cnot bell156 a4
H bell156
measure bell156
cz bell156 b1
cnot bell152 a4
H bell152
measure bell152
cz bell152 b0
T* a4
H bell158
cnot bell158 bell159
cnot b2 bell159
measure bell159
cnot bell159 bell158
cnot bell158 a4
H bell158
measure bell158
cz bell158 b2
H bell160
cnot bell160 bell161
cnot a2 bell161
measure bell161
cnot bell161 bell160
cnot bell160 a4
H bell160
measure bell160
cz bell160 a2
T* a4
H bell162
cnot bell162 bell163
cnot b3 bell163
measure bell163
cnot bell163 bell162
cnot bell162 a4
H bell162
measure bell162
cz bell162 b3
H bell164
cnot bell164 bell165
cnot a3 bell165
measure bell165
cnot bell165 bell164
cnot bell164 a4
H bell164
measure bell164
cz bell164 a3
T* a4
T* b4
H bell166
cnot bell166 bell167
cnot a0 bell167
measure bell167
cnot bell167 bell166
cnot bell166 b4
T* b4
H bell168
cnot bell168 bell169
cnot a1 bell169
measure bell169
cnot bell169 bell168
cnot bell168 b4
cnot bell166 b4
H bell166
measure bell166
cz bell166 a0
T b4
H bell170
cnot bell170 bell171
cnot b1 bell171
measure bell171
cnot bell171 bell170
cnot bell170 b4
H bell170
measure bell170
cz bell170 b1
H bell172
cnot bell172 bell173
cnot a2 bell173
measure bell173
cnot bell173 bell172
cnot bell172 b4
H bell172
measure bell172
cz bell172 a2
T* b4
H bell174
cnot bell174 bell175
cnot b2 bell175
measure bell175
cnot bell175 bell174
cnot bell174 b4
H bell174
measure bell174
cz bell174 b2
H bell176
cnot bell176 bell177
cnot a3 bell177
measure bell177
cnot bell177 bell176
cnot bell176 b4
H bell176
measure bell176
cz bell176 a3
T b4
H bell178
cnot bell178 bell179
cnot b3 bell179
measure bell179
cnot bell179 bell178
cnot bell178 b4
H bell178
measure bell178
cz bell178 b3
H bell180
cnot bell180 bell181
cnot a4 bell181
measure bell181
cnot bell181 bell180
cnot bell180 b4
H bell180
measure bell180
cz bell180 a4
T b4
H bell182
cnot bell182 bell183
cnot b1 bell183
measure bell183
cnot bell183 bell182
cnot bell182 a2
H bell182
measure bell182
cz bell182 b1
H bell184
cnot bell184 bell185
cnot b2 bell185
measure bell185
cnot bell185 bell184
cnot bell184 a3
H bell184
measure bell184
cz bell184 b2
H bell186
cnot bell186 bell187
cnot b3 bell187
measure bell187
cnot bell187 bell186
cnot bell186 a4
H bell186
measure bell186
cz bell186 b3
H bell188
cnot bell188 bell189
cnot a4 bell189
measure bell189
cnot bell189 bell188
cnot bell188 b4
H bell188
measure bell188
cz bell188 a4
H bell190
cnot bell190 bell191
cnot a2 bell191
measure bell191
cnot bell191 bell190
cnot bell190 a3
H bell190
measure bell190
cz bell190 a2
H bell192
cnot bell192 bell193
cnot a3 bell193
measure bell193
cnot bell193 bell192
cnot bell192 b4
H bell192
measure bell192
cz bell192 a3
H bell194
cnot bell194 bell195
cnot a3 bell195
measure bell195
cnot bell195 bell194
cnot bell194 b3
H bell194
measure bell194
cz bell194 a3
H bell196
cnot bell196 bell197
cnot a2 bell197
measure bell197
cnot bell197 bell196
cnot bell196 b2
H bell196
measure bell196
cz bell196 a2
H bell198
cnot bell198 bell199
cnot a3 bell199
measure bell199
cnot bell199 bell198
cnot bell198 a4
H bell198
measure bell198
cz bell198 a3
cnot bell168 b4
H bell168
measure bell168
cz bell168 a1
H bell200
cnot bell200 bell201
cnot a1 bell201
measure bell201
cnot bell201 bell200
cnot bell200 b3
H bell200
measure bell200
cz bell200 a1
H bell202
cnot bell202 bell203
cnot a1 bell203
measure bell203
cnot bell203 bell202
cnot bell202 b2
H bell202
measure bell202
cz bell202 a1
H bell204
cnot bell204 bell205
cnot a1 bell205
measure bell205
cnot bell205 bell204
cnot bell204 b1
H bell204
measure bell204
cz bell204 a1
H bell206
cnot bell206 bell207
cnot a1 bell207
measure bell207
cnot bell207 bell206
cnot bell206 b0
H bell206
measure bell206
cz bell206 a1
H bell208
cnot bell208 bell209
cnot a1 bell209
measure bell209
cnot bell209 bell208
cnot bell208 a4
H bell208
measure bell208
cz bell208 a1
H bell210
cnot bell210 bell211
cnot a1 bell211
measure bell211
cnot bell211 bell210
cnot bell210 a3
H bell210
measure bell210
cz bell210 a1
H bell212
cnot bell212 bell213
cnot a1 bell213
measure bell213
cnot bell213 bell212
cnot bell212 a2
H bell212
measure bell212
cz bell212 a1
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
reset bell178
reset bell179
reset bell180
reset bell181
reset bell182
reset bell183
reset bell184
reset bell185
reset bell186
reset bell187
reset bell188
reset bell189
reset bell190
reset bell191
reset bell192
reset bell193
reset bell194
reset bell195
reset bell196
reset bell197
reset bell198
reset bell199
reset bell200
reset bell201
reset bell202
reset bell203
reset bell204
reset bell205
reset bell206
reset bell207
reset bell208
reset bell209
reset bell210
reset bell211
reset bell212
reset bell213
END
