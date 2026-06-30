# Hyperedge cut (ebits): 46

# Actual ebits used (Synthesis): 167
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^7_mult.qc):
#   Qubits: 21
#   H: 26
#   T: 343
#   cnot: 300
#   Depth: 166
#   T depth: 80
# Result (39.298ms):
#   Qubits: 355
#   H: 360
#   S: 4
#   T: 217
#   Z: 6
#   cnot: 832
#   cz: 173
#   measure: 334
#   reset: 340
#   Depth: 432
#   T depth: 75


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell256 bell257 bell258 bell259 bell26 bell260 bell261 bell262 bell263 bell264 bell265 bell266 bell267 bell268 bell269 bell27 bell270 bell271 bell272 bell273 bell274 bell275 bell276 bell277 bell278 bell279 bell28 bell280 bell281 bell282 bell283 bell284 bell285 bell286 bell287 bell288 bell289 bell29 bell290 bell291 bell292 bell293 bell294 bell295 bell296 bell297 bell298 bell299 bell3 bell30 bell300 bell301 bell302 bell303 bell304 bell305 bell306 bell307 bell308 bell309 bell31 bell310 bell311 bell312 bell313 bell314 bell315 bell316 bell317 bell318 bell319 bell32 bell320 bell321 bell322 bell323 bell324 bell325 bell326 bell327 bell328 bell329 bell33 bell330 bell331 bell332 bell333 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
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
cz bell0 a6
T* c0
H bell4
cnot bell4 bell5
cnot a5 bell5
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
cz bell4 a5
T* c0
H bell8
cnot bell8 bell9
cnot a4 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
cnot bell6 c0
H bell6
measure bell6
cz bell6 b2
T* c0
H bell10
cnot bell10 bell11
cnot b3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
T c0
cnot bell8 c0
H bell8
measure bell8
cz bell8 a4
T* c0
H bell12
cnot bell12 bell13
cnot a3 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
cnot bell10 c0
H bell10
measure bell10
cz bell10 b3
T* c0
H bell14
cnot bell14 bell15
cnot b4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
T c0
cnot bell12 c0
H bell12
measure bell12
cz bell12 a3
T* c0
H bell16
cnot bell16 bell17
cnot a2 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
cnot bell14 c0
H bell14
measure bell14
cz bell14 b4
T* c0
H bell18
cnot bell18 bell19
cnot b5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c0
T c0
cnot bell16 c0
H bell16
measure bell16
cz bell16 a2
T* c0
H bell20
cnot bell20 bell21
cnot a1 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c0
cnot bell18 c0
H bell18
measure bell18
cz bell18 b5
T* c0
H bell22
cnot bell22 bell23
cnot b6 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c0
T c0
cnot bell20 c0
H bell20
measure bell20
cz bell20 a1
T* c0
cnot bell22 c0
H bell22
measure bell22
cz bell22 b6
H c0
T c1
Z c1
H bell24
cnot bell24 bell25
cnot a6 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c1
T* c1
H bell26
cnot bell26 bell27
cnot b2 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c1
T c1
cnot bell24 c1
H bell24
measure bell24
cz bell24 a6
T* c1
H bell28
cnot bell28 bell29
cnot a5 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c1
cnot bell26 c1
H bell26
measure bell26
cz bell26 b2
T* c1
H bell30
cnot bell30 bell31
cnot b3 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c1
T c1
cnot bell28 c1
H bell28
measure bell28
cz bell28 a5
T* c1
H bell32
cnot bell32 bell33
cnot a4 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c1
cnot bell30 c1
H bell30
measure bell30
cz bell30 b3
T* c1
H bell34
cnot bell34 bell35
cnot b4 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c1
T c1
cnot bell32 c1
H bell32
measure bell32
cz bell32 a4
T* c1
H bell36
cnot bell36 bell37
cnot a3 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c1
cnot bell34 c1
H bell34
measure bell34
cz bell34 b4
T* c1
H bell38
cnot bell38 bell39
cnot b5 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c1
T c1
cnot bell36 c1
H bell36
measure bell36
cz bell36 a3
T* c1
H bell40
cnot bell40 bell41
cnot a2 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c1
cnot bell38 c1
H bell38
measure bell38
cz bell38 b5
T* c1
H bell42
cnot bell42 bell43
cnot b6 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c1
T c1
cnot bell40 c1
H bell40
measure bell40
cz bell40 a2
T* c1
cnot bell42 c1
H bell42
measure bell42
cz bell42 b6
H c1
Z c2
H bell44
cnot bell44 bell45
cnot a6 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c2
T* c2
H bell46
cnot bell46 bell47
cnot b3 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c2
T c2
cnot bell44 c2
T* c2
H bell48
cnot bell48 bell49
cnot a5 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c2
cnot bell46 c2
T* c2
H bell50
cnot bell50 bell51
cnot b4 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c2
T c2
cnot bell48 c2
T* c2
H bell52
cnot bell52 bell53
cnot a4 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c2
cnot bell50 c2
T* c2
H bell54
cnot bell54 bell55
cnot b5 bell55
measure bell55
cnot bell55 bell54
cnot bell54 c2
T c2
cnot bell52 c2
T* c2
H bell56
cnot bell56 bell57
cnot a3 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c2
cnot bell54 c2
T* c2
H bell58
cnot bell58 bell59
cnot b6 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c2
T c2
cnot bell56 c2
T* c2
cnot bell58 c2
H c2
T* c3
Z c3
cnot bell44 c3
T* c3
cnot bell50 c3
T c3
cnot bell44 c3
H bell44
measure bell44
cz bell44 a6
T* c3
cnot bell48 c3
cnot bell50 c3
H bell50
measure bell50
cz bell50 b4
T* c3
cnot bell54 c3
T c3
cnot bell48 c3
H bell48
measure bell48
cz bell48 a5
T* c3
cnot bell52 c3
cnot bell54 c3
H bell54
measure bell54
cz bell54 b5
T* c3
cnot bell58 c3
T c3
cnot bell52 c3
H bell52
measure bell52
cz bell52 a4
T* c3
cnot bell58 c3
H bell58
measure bell58
cz bell58 b6
H c3
S c4
H bell60
cnot bell60 bell61
cnot a6 bell61
measure bell61
cnot bell61 bell60
cnot bell60 c4
T* c4
H bell62
cnot bell62 bell63
cnot b5 bell63
measure bell63
cnot bell63 bell62
cnot bell62 c4
T c4
cnot bell60 c4
H bell60
measure bell60
cz bell60 a6
T* c4
H bell64
cnot bell64 bell65
cnot a5 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c4
cnot bell62 c4
H bell62
measure bell62
cz bell62 b5
T* c4
H bell66
cnot bell66 bell67
cnot b6 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c4
T c4
cnot bell64 c4
H bell64
measure bell64
cz bell64 a5
T* c4
cnot bell66 c4
H bell66
measure bell66
cz bell66 b6
H c4
T c5
H bell68
cnot bell68 bell69
cnot a6 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c5
T* c5
H bell70
cnot bell70 bell71
cnot b6 bell71
measure bell71
cnot bell71 bell70
cnot bell70 c5
T c5
cnot bell68 c5
H bell68
measure bell68
cz bell68 a6
T* c5
cnot bell70 c5
H bell70
measure bell70
cz bell70 b6
H c5
H bell72
cnot bell72 bell73
cnot c5 bell73
measure bell73
cnot bell73 bell72
cnot bell72 c6
H bell72
measure bell72
cz bell72 c5
H bell74
cnot bell74 bell75
cnot c4 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c5
H bell74
measure bell74
cz bell74 c4
H bell76
cnot bell76 bell77
cnot c3 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c4
H bell76
measure bell76
cz bell76 c3
cnot c2 c3
H bell78
cnot bell78 bell79
cnot c1 bell79
measure bell79
cnot bell79 bell78
cnot bell78 c2
H bell78
measure bell78
cz bell78 c1
H bell80
cnot bell80 bell81
cnot c0 bell81
measure bell81
cnot bell81 bell80
cnot bell80 c1
H bell80
measure bell80
cz bell80 c0
H c0
H c1
H c2
H c3
H c4
H c5
H c6
T c0
H bell82
cnot bell82 bell83
cnot a0 bell83
measure bell83
cnot bell83 bell82
cnot bell82 c0
T* c0
H bell84
cnot bell84 bell85
cnot b0 bell85
measure bell85
cnot bell85 bell84
cnot bell84 c0
T c0
cnot bell82 c0
H bell82
measure bell82
cz bell82 a0
T* c0
cnot bell84 c0
H bell84
measure bell84
cz bell84 b0
H c0
S c1
H bell86
cnot bell86 bell87
cnot a1 bell87
measure bell87
cnot bell87 bell86
cnot bell86 c1
T* c1
H bell88
cnot bell88 bell89
cnot b0 bell89
measure bell89
cnot bell89 bell88
cnot bell88 c1
T c1
cnot bell86 c1
H bell86
measure bell86
cz bell86 a1
T* c1
H bell90
cnot bell90 bell91
cnot a0 bell91
measure bell91
cnot bell91 bell90
cnot bell90 c1
cnot bell88 c1
H bell88
measure bell88
cz bell88 b0
T* c1
H bell92
cnot bell92 bell93
cnot b1 bell93
measure bell93
cnot bell93 bell92
cnot bell92 c1
T c1
cnot bell90 c1
H bell90
measure bell90
cz bell90 a0
T* c1
cnot bell92 c1
H bell92
measure bell92
cz bell92 b1
H c1
T* c2
Z c2
H bell94
cnot bell94 bell95
cnot a2 bell95
measure bell95
cnot bell95 bell94
cnot bell94 c2
T* c2
H bell96
cnot bell96 bell97
cnot b0 bell97
measure bell97
cnot bell97 bell96
cnot bell96 c2
T c2
cnot bell94 c2
T* c2
H bell98
cnot bell98 bell99
cnot a1 bell99
measure bell99
cnot bell99 bell98
cnot bell98 c2
cnot bell96 c2
T* c2
H bell100
cnot bell100 bell101
cnot b1 bell101
measure bell101
cnot bell101 bell100
cnot bell100 c2
T c2
cnot bell98 c2
T* c2
H bell102
cnot bell102 bell103
cnot a0 bell103
measure bell103
cnot bell103 bell102
cnot bell102 c2
cnot bell100 c2
T* c2
H bell104
cnot bell104 bell105
cnot b2 bell105
measure bell105
cnot bell105 bell104
cnot bell104 c2
T c2
cnot bell102 c2
T* c2
cnot bell104 c2
H c2
Z c3
cnot bell56 c3
T* c3
cnot bell96 c3
T c3
cnot bell56 c3
H bell56
measure bell56
cz bell56 a3
T* c3
cnot bell94 c3
cnot bell96 c3
H bell96
measure bell96
cz bell96 b0
T* c3
cnot bell100 c3
T c3
cnot bell94 c3
H bell94
measure bell94
cz bell94 a2
T* c3
cnot bell98 c3
cnot bell100 c3
H bell100
measure bell100
cz bell100 b1
T* c3
cnot bell104 c3
T c3
cnot bell98 c3
H bell98
measure bell98
cz bell98 a1
T* c3
cnot bell102 c3
cnot bell104 c3
H bell104
measure bell104
cz bell104 b2
T* c3
cnot bell46 c3
T c3
cnot bell102 c3
H bell102
measure bell102
cz bell102 a0
T* c3
cnot bell46 c3
H bell46
measure bell46
cz bell46 b3
H c3
T c4
Z c4
H bell106
cnot bell106 bell107
cnot a4 bell107
measure bell107
cnot bell107 bell106
cnot bell106 c4
T* c4
H bell108
cnot bell108 bell109
cnot b0 bell109
measure bell109
cnot bell109 bell108
cnot bell108 c4
T c4
cnot bell106 c4
H bell106
measure bell106
cz bell106 a4
T* c4
H bell110
cnot bell110 bell111
cnot a3 bell111
measure bell111
cnot bell111 bell110
cnot bell110 c4
cnot bell108 c4
H bell108
measure bell108
cz bell108 b0
T* c4
H bell112
cnot bell112 bell113
cnot b1 bell113
measure bell113
cnot bell113 bell112
cnot bell112 c4
T c4
cnot bell110 c4
H bell110
measure bell110
cz bell110 a3
T* c4
H bell114
cnot bell114 bell115
cnot a2 bell115
measure bell115
cnot bell115 bell114
cnot bell114 c4
cnot bell112 c4
H bell112
measure bell112
cz bell112 b1
T* c4
H bell116
cnot bell116 bell117
cnot b2 bell117
measure bell117
cnot bell117 bell116
cnot bell116 c4
T c4
cnot bell114 c4
H bell114
measure bell114
cz bell114 a2
T* c4
H bell118
cnot bell118 bell119
cnot a1 bell119
measure bell119
cnot bell119 bell118
cnot bell118 c4
cnot bell116 c4
H bell116
measure bell116
cz bell116 b2
T* c4
H bell120
cnot bell120 bell121
cnot b3 bell121
measure bell121
cnot bell121 bell120
cnot bell120 c4
T c4
cnot bell118 c4
H bell118
measure bell118
cz bell118 a1
T* c4
H bell122
cnot bell122 bell123
cnot a0 bell123
measure bell123
cnot bell123 bell122
cnot bell122 c4
cnot bell120 c4
H bell120
measure bell120
cz bell120 b3
T* c4
H bell124
cnot bell124 bell125
cnot b4 bell125
measure bell125
cnot bell125 bell124
cnot bell124 c4
T c4
cnot bell122 c4
H bell122
measure bell122
cz bell122 a0
T* c4
cnot bell124 c4
H bell124
measure bell124
cz bell124 b4
H c4
S* c5
H bell126
cnot bell126 bell127
cnot a5 bell127
measure bell127
cnot bell127 bell126
cnot bell126 c5
T* c5
H bell128
cnot bell128 bell129
cnot b0 bell129
measure bell129
cnot bell129 bell128
cnot bell128 c5
T c5
cnot bell126 c5
H bell126
measure bell126
cz bell126 a5
T* c5
H bell130
cnot bell130 bell131
cnot a4 bell131
measure bell131
cnot bell131 bell130
cnot bell130 c5
cnot bell128 c5
H bell128
measure bell128
cz bell128 b0
T* c5
H bell132
cnot bell132 bell133
cnot b1 bell133
measure bell133
cnot bell133 bell132
cnot bell132 c5
T c5
cnot bell130 c5
H bell130
measure bell130
cz bell130 a4
T* c5
H bell134
cnot bell134 bell135
cnot a3 bell135
measure bell135
cnot bell135 bell134
cnot bell134 c5
cnot bell132 c5
H bell132
measure bell132
cz bell132 b1
T* c5
H bell136
cnot bell136 bell137
cnot b2 bell137
measure bell137
cnot bell137 bell136
cnot bell136 c5
T c5
cnot bell134 c5
H bell134
measure bell134
cz bell134 a3
T* c5
H bell138
cnot bell138 bell139
cnot a2 bell139
measure bell139
cnot bell139 bell138
cnot bell138 c5
cnot bell136 c5
H bell136
measure bell136
cz bell136 b2
T* c5
H bell140
cnot bell140 bell141
cnot b3 bell141
measure bell141
cnot bell141 bell140
cnot bell140 c5
T c5
cnot bell138 c5
H bell138
measure bell138
cz bell138 a2
T* c5
H bell142
cnot bell142 bell143
cnot a1 bell143
measure bell143
cnot bell143 bell142
cnot bell142 c5
cnot bell140 c5
H bell140
measure bell140
cz bell140 b3
T* c5
H bell144
cnot bell144 bell145
cnot b4 bell145
measure bell145
cnot bell145 bell144
cnot bell144 c5
T c5
cnot bell142 c5
H bell142
measure bell142
cz bell142 a1
T* c5
H bell146
cnot bell146 bell147
cnot a0 bell147
measure bell147
cnot bell147 bell146
cnot bell146 c5
cnot bell144 c5
H bell144
measure bell144
cz bell144 b4
T* c5
H bell148
cnot bell148 bell149
cnot b5 bell149
measure bell149
cnot bell149 bell148
cnot bell148 c5
T c5
cnot bell146 c5
H bell146
measure bell146
cz bell146 a0
T* c5
cnot bell148 c5
H bell148
measure bell148
cz bell148 b5
H c5
T* c6
H bell150
cnot bell150 bell151
cnot a6 bell151
measure bell151
cnot bell151 bell150
cnot bell150 c6
T* c6
H bell152
cnot bell152 bell153
cnot b0 bell153
measure bell153
cnot bell153 bell152
cnot bell152 c6
T c6
cnot bell150 c6
H bell150
measure bell150
cz bell150 a6
T* c6
H bell154
cnot bell154 bell155
cnot a5 bell155
measure bell155
cnot bell155 bell154
cnot bell154 c6
cnot bell152 c6
H bell152
measure bell152
cz bell152 b0
T* c6
H bell156
cnot bell156 bell157
cnot b1 bell157
measure bell157
cnot bell157 bell156
cnot bell156 c6
T c6
cnot bell154 c6
H bell154
measure bell154
cz bell154 a5
T* c6
H bell158
cnot bell158 bell159
cnot a4 bell159
measure bell159
cnot bell159 bell158
cnot bell158 c6
cnot bell156 c6
H bell156
measure bell156
cz bell156 b1
T* c6
H bell160
cnot bell160 bell161
cnot b2 bell161
measure bell161
cnot bell161 bell160
cnot bell160 c6
T c6
cnot bell158 c6
H bell158
measure bell158
cz bell158 a4
T* c6
H bell162
cnot bell162 bell163
cnot a3 bell163
measure bell163
cnot bell163 bell162
cnot bell162 c6
cnot bell160 c6
H bell160
measure bell160
cz bell160 b2
T* c6
H bell164
cnot bell164 bell165
cnot b3 bell165
measure bell165
cnot bell165 bell164
cnot bell164 c6
T c6
cnot bell162 c6
H bell162
measure bell162
cz bell162 a3
T* c6
H bell166
cnot bell166 bell167
cnot a2 bell167
measure bell167
cnot bell167 bell166
cnot bell166 c6
cnot bell164 c6
H bell164
measure bell164
cz bell164 b3
T* c6
H bell168
cnot bell168 bell169
cnot b4 bell169
measure bell169
cnot bell169 bell168
cnot bell168 c6
T c6
cnot bell166 c6
H bell166
measure bell166
cz bell166 a2
T* c6
H bell170
cnot bell170 bell171
cnot a1 bell171
measure bell171
cnot bell171 bell170
cnot bell170 c6
cnot bell168 c6
H bell168
measure bell168
cz bell168 b4
T* c6
H bell172
cnot bell172 bell173
cnot b5 bell173
measure bell173
cnot bell173 bell172
cnot bell172 c6
T c6
cnot bell170 c6
H bell170
measure bell170
cz bell170 a1
T* c6
H bell174
cnot bell174 bell175
cnot a0 bell175
measure bell175
cnot bell175 bell174
cnot bell174 c6
cnot bell172 c6
H bell172
measure bell172
cz bell172 b5
T* c6
H bell176
cnot bell176 bell177
cnot b6 bell177
measure bell177
cnot bell177 bell176
cnot bell176 c6
T c6
cnot bell174 c6
H bell174
measure bell174
cz bell174 a0
T* c6
cnot bell176 c6
H bell176
measure bell176
cz bell176 b6
H c6
T* a0
T* a1
T* b0
H bell178
cnot bell178 bell179
cnot a0 bell179
measure bell179
cnot bell179 bell178
cnot bell178 b0
T* b0
cnot a1 b0
cnot bell178 b0
H bell178
measure bell178
cz bell178 a0
T* b0
T* b1
H bell180
cnot bell180 bell181
cnot a0 bell181
measure bell181
cnot bell181 bell180
cnot bell180 b1
T* b1
H bell182
cnot bell182 bell183
cnot a1 bell183
measure bell183
cnot bell183 bell182
cnot bell182 b1
H bell182
measure bell182
cz bell182 a1
cnot bell180 b1
H bell180
measure bell180
cz bell180 a0
T* b1
T* a2
H bell184
cnot bell184 bell185
cnot b0 bell185
measure bell185
cnot bell185 bell184
cnot bell184 a2
H bell186
cnot bell186 bell187
cnot a1 bell187
measure bell187
cnot bell187 bell186
cnot bell186 a2
H bell186
measure bell186
cz bell186 a1
T* a2
H bell188
cnot bell188 bell189
cnot b1 bell189
measure bell189
cnot bell189 bell188
cnot bell188 a2
H bell188
measure bell188
cz bell188 b1
cnot bell184 a2
H bell184
measure bell184
cz bell184 b0
T* a2
T* b2
H bell190
cnot bell190 bell191
cnot a0 bell191
measure bell191
cnot bell191 bell190
cnot bell190 b2
T* b2
H bell192
cnot bell192 bell193
cnot a1 bell193
measure bell193
cnot bell193 bell192
cnot bell192 b2
H bell192
measure bell192
cz bell192 a1
cnot bell190 b2
H bell190
measure bell190
cz bell190 a0
T* b2
H bell194
cnot bell194 bell195
cnot b2 bell195
measure bell195
cnot bell195 bell194
H bell196
cnot bell196 bell197
cnot b1 bell197
measure bell197
cnot bell197 bell196
cnot bell196 bell194
H bell198
cnot bell198 bell199
cnot a2 bell199
measure bell199
cnot bell199 bell198
cnot bell198 bell194
H bell200
cnot bell200 bell201
cnot bell194 bell201
measure bell201
cnot bell201 bell200
reset bell201
cnot b2 bell200
cnot bell200 b2
H bell200
measure bell200
cz bell200 a2
cz bell200 b1
H bell194
measure bell194
cz bell194 b2
T* b2
T* a3
H bell202
cnot bell202 bell203
cnot b0 bell203
measure bell203
cnot bell203 bell202
cnot bell202 a3
H bell204
cnot bell204 bell205
cnot a1 bell205
measure bell205
cnot bell205 bell204
cnot bell204 a3
T* a3
cnot bell196 a3
cnot bell202 a3
H bell202
measure bell202
cz bell202 b0
T* a3
H bell206
cnot bell206 bell207
cnot b2 bell207
measure bell207
cnot bell207 bell206
cnot bell206 a3
cnot bell198 a3
T* a3
T* b3
H bell208
cnot bell208 bell209
cnot a0 bell209
measure bell209
cnot bell209 bell208
cnot bell208 b3
T* b3
cnot bell204 b3
H bell204
measure bell204
cz bell204 a1
cnot bell208 b3
H bell208
measure bell208
cz bell208 a0
T* b3
cnot bell196 b3
H bell196
measure bell196
cz bell196 b1
cnot bell198 b3
H bell198
measure bell198
cz bell198 a2
T* b3
cnot bell206 b3
H bell206
measure bell206
cz bell206 b2
cnot a3 b3
T* b3
T* a4
H bell210
cnot bell210 bell211
cnot b0 bell211
measure bell211
cnot bell211 bell210
cnot bell210 a4
H bell212
cnot bell212 bell213
cnot a1 bell213
measure bell213
cnot bell213 bell212
cnot bell212 a4
H bell212
measure bell212
cz bell212 a1
T* a4
H bell214
cnot bell214 bell215
cnot b1 bell215
measure bell215
cnot bell215 bell214
cnot bell214 a4
H bell214
measure bell214
cz bell214 b1
cnot bell210 a4
T* a4
H bell216
cnot bell216 bell217
cnot b2 bell217
measure bell217
cnot bell217 bell216
cnot bell216 a4
H bell216
measure bell216
cz bell216 b2
H bell218
cnot bell218 bell219
cnot a2 bell219
measure bell219
cnot bell219 bell218
cnot bell218 a4
H bell218
measure bell218
cz bell218 a2
T* a4
H bell220
cnot bell220 bell221
cnot b3 bell221
measure bell221
cnot bell221 bell220
cnot bell220 a4
H bell222
cnot bell222 bell223
cnot a3 bell223
measure bell223
cnot bell223 bell222
cnot bell222 a4
H bell222
measure bell222
cz bell222 a3
T* a4
T* b4
H bell224
cnot bell224 bell225
cnot a0 bell225
measure bell225
cnot bell225 bell224
cnot bell224 b4
T* b4
H bell226
cnot bell226 bell227
cnot a1 bell227
measure bell227
cnot bell227 bell226
cnot bell226 b4
H bell226
measure bell226
cz bell226 a1
cnot bell224 b4
H bell224
measure bell224
cz bell224 a0
T* b4
H bell228
cnot bell228 bell229
cnot b1 bell229
measure bell229
cnot bell229 bell228
cnot bell228 b4
H bell228
measure bell228
cz bell228 b1
H bell230
cnot bell230 bell231
cnot a2 bell231
measure bell231
cnot bell231 bell230
cnot bell230 b4
H bell230
measure bell230
cz bell230 a2
T* b4
H bell232
cnot bell232 bell233
cnot b2 bell233
measure bell233
cnot bell233 bell232
cnot bell232 b4
H bell232
measure bell232
cz bell232 b2
H bell234
cnot bell234 bell235
cnot a3 bell235
measure bell235
cnot bell235 bell234
cnot bell234 b4
H bell234
measure bell234
cz bell234 a3
T* b4
H bell236
cnot bell236 bell237
cnot b4 bell237
measure bell237
cnot bell237 bell236
cnot bell220 bell236
cnot a4 bell236
H bell238
cnot bell238 bell239
cnot bell236 bell239
measure bell239
cnot bell239 bell238
reset bell239
cnot b4 bell238
cnot bell238 b4
H bell238
measure bell238
cz bell238 a4
cz bell238 b3
H bell236
measure bell236
cz bell236 b4
T* b4
T* a5
cnot bell210 a5
H bell240
cnot bell240 bell241
cnot a1 bell241
measure bell241
cnot bell241 bell240
cnot bell240 a5
H bell240
measure bell240
cz bell240 a1
T* a5
H bell242
cnot bell242 bell243
cnot b1 bell243
measure bell243
cnot bell243 bell242
cnot bell242 a5
H bell242
measure bell242
cz bell242 b1
cnot bell210 a5
H bell210
measure bell210
cz bell210 b0
T* a5
H bell244
cnot bell244 bell245
cnot b2 bell245
measure bell245
cnot bell245 bell244
cnot bell244 a5
H bell244
measure bell244
cz bell244 b2
H bell246
cnot bell246 bell247
cnot a2 bell247
measure bell247
cnot bell247 bell246
cnot bell246 a5
H bell246
measure bell246
cz bell246 a2
T* a5
cnot bell220 a5
H bell220
measure bell220
cz bell220 b3
H bell248
cnot bell248 bell249
cnot a3 bell249
measure bell249
cnot bell249 bell248
cnot bell248 a5
H bell248
measure bell248
cz bell248 a3
T* a5
H bell250
cnot bell250 bell251
cnot b4 bell251
measure bell251
cnot bell251 bell250
cnot bell250 a5
H bell250
measure bell250
cz bell250 b4
cnot a4 a5
T* a5
T* b5
H bell252
cnot bell252 bell253
cnot a0 bell253
measure bell253
cnot bell253 bell252
cnot bell252 b5
T* b5
H bell254
cnot bell254 bell255
cnot a1 bell255
measure bell255
cnot bell255 bell254
cnot bell254 b5
H bell254
measure bell254
cz bell254 a1
cnot bell252 b5
H bell252
measure bell252
cz bell252 a0
T* b5
H bell256
cnot bell256 bell257
cnot b1 bell257
measure bell257
cnot bell257 bell256
cnot bell256 b5
H bell256
measure bell256
cz bell256 b1
H bell258
cnot bell258 bell259
cnot a2 bell259
measure bell259
cnot bell259 bell258
cnot bell258 b5
H bell258
measure bell258
cz bell258 a2
T* b5
H bell260
cnot bell260 bell261
cnot b5 bell261
measure bell261
cnot bell261 bell260
H bell262
cnot bell262 bell263
cnot b2 bell263
measure bell263
cnot bell263 bell262
cnot bell262 bell260
H bell264
cnot bell264 bell265
cnot a3 bell265
measure bell265
cnot bell265 bell264
cnot bell264 bell260
H bell266
cnot bell266 bell267
cnot bell260 bell267
measure bell267
cnot bell267 bell266
reset bell267
cnot b5 bell266
cnot bell266 b5
H bell266
measure bell266
cz bell266 a3
cz bell266 b2
H bell260
measure bell260
cz bell260 b5
T* b5
H bell268
cnot bell268 bell269
cnot b3 bell269
measure bell269
cnot bell269 bell268
cnot bell268 b5
H bell268
measure bell268
cz bell268 b3
H bell270
cnot bell270 bell271
cnot a4 bell271
measure bell271
cnot bell271 bell270
cnot bell270 b5
H bell270
measure bell270
cz bell270 a4
T* b5
H bell272
cnot bell272 bell273
cnot b5 bell273
measure bell273
cnot bell273 bell272
H bell274
cnot bell274 bell275
cnot b4 bell275
measure bell275
cnot bell275 bell274
cnot bell274 bell272
H bell276
cnot bell276 bell277
cnot a5 bell277
measure bell277
cnot bell277 bell276
cnot bell276 bell272
H bell278
cnot bell278 bell279
cnot bell272 bell279
measure bell279
cnot bell279 bell278
reset bell279
cnot b5 bell278
cnot bell278 b5
H bell278
measure bell278
cz bell278 a5
cz bell278 b4
H bell272
measure bell272
cz bell272 b5
T* b5
T* a6
H bell280
cnot bell280 bell281
cnot b0 bell281
measure bell281
cnot bell281 bell280
cnot bell280 a6
H bell282
cnot bell282 bell283
cnot a1 bell283
measure bell283
cnot bell283 bell282
cnot bell282 a6
T* a6
H bell284
cnot bell284 bell285
cnot b1 bell285
measure bell285
cnot bell285 bell284
cnot bell284 a6
cnot bell280 a6
H bell280
measure bell280
cz bell280 b0
T* a6
cnot bell262 a6
H bell286
cnot bell286 bell287
cnot a2 bell287
measure bell287
cnot bell287 bell286
cnot bell286 a6
T* a6
H bell288
cnot bell288 bell289
cnot b3 bell289
measure bell289
cnot bell289 bell288
cnot bell288 a6
cnot bell264 a6
T* a6
cnot bell274 a6
H bell290
cnot bell290 bell291
cnot a4 bell291
measure bell291
cnot bell291 bell290
cnot bell290 a6
T* a6
H bell292
cnot bell292 bell293
cnot b5 bell293
measure bell293
cnot bell293 bell292
cnot bell292 a6
cnot bell276 a6
T* a6
T* b6
H bell294
cnot bell294 bell295
cnot a0 bell295
measure bell295
cnot bell295 bell294
cnot bell294 b6
T* b6
cnot bell282 b6
H bell282
measure bell282
cz bell282 a1
cnot bell294 b6
H bell294
measure bell294
cz bell294 a0
T* b6
cnot bell284 b6
H bell284
measure bell284
cz bell284 b1
cnot bell286 b6
H bell286
measure bell286
cz bell286 a2
T* b6
cnot bell262 b6
H bell262
measure bell262
cz bell262 b2
cnot bell264 b6
H bell264
measure bell264
cz bell264 a3
T* b6
cnot bell288 b6
H bell288
measure bell288
cz bell288 b3
cnot bell290 b6
H bell290
measure bell290
cz bell290 a4
T* b6
cnot bell274 b6
H bell274
measure bell274
cz bell274 b4
cnot bell276 b6
H bell276
measure bell276
cz bell276 a5
T* b6
cnot bell292 b6
cnot a6 b6
T* b6
H bell296
cnot bell296 bell297
cnot b1 bell297
measure bell297
cnot bell297 bell296
cnot bell296 a2
H bell296
measure bell296
cz bell296 b1
H bell298
cnot bell298 bell299
cnot b2 bell299
measure bell299
cnot bell299 bell298
cnot bell298 a3
H bell298
measure bell298
cz bell298 b2
H bell300
cnot bell300 bell301
cnot b3 bell301
measure bell301
cnot bell301 bell300
cnot bell300 a4
H bell300
measure bell300
cz bell300 b3
H bell302
cnot bell302 bell303
cnot b4 bell303
measure bell303
cnot bell303 bell302
cnot bell302 a5
H bell302
measure bell302
cz bell302 b4
cnot bell292 a6
H bell292
measure bell292
cz bell292 b5
cnot a6 b6
cnot a4 a5
H bell304
cnot bell304 bell305
cnot a3 bell305
measure bell305
cnot bell305 bell304
cnot bell304 a5
cnot bell304 a4
H bell304
measure bell304
cz bell304 a3
H bell306
cnot bell306 bell307
cnot a5 bell307
measure bell307
cnot bell307 bell306
cnot bell306 b6
H bell308
cnot bell308 bell309
cnot b5 bell309
measure bell309
cnot bell309 bell308
cnot bell306 bell308
H bell310
cnot bell310 bell311
cnot b4 bell311
measure bell311
cnot bell311 bell310
cnot a4 bell310
cnot a3 b3
cnot bell306 a6
H bell306
measure bell306
cz bell306 a5
H bell312
cnot bell312 bell313
cnot a1 bell313
measure bell313
cnot bell313 bell312
cnot bell312 a2
H bell312
measure bell312
cz bell312 a1
H bell314
cnot bell314 bell315
cnot a2 bell315
measure bell315
cnot bell315 bell314
cnot bell314 b6
cnot bell314 bell308
H bell316
cnot bell316 bell317
cnot bell308 bell317
measure bell317
cnot bell317 bell316
reset bell317
cnot b5 bell316
cnot bell316 b5
H bell316
measure bell316
cz bell316 a2
cz bell316 a5
H bell308
measure bell308
cz bell308 b5
H bell314
measure bell314
cz bell314 a2
H bell318
cnot bell318 bell319
cnot a2 bell319
measure bell319
cnot bell319 bell318
cnot bell318 bell310
H bell320
cnot bell320 bell321
cnot bell310 bell321
measure bell321
cnot bell321 bell320
reset bell321
cnot b4 bell320
cnot bell320 b4
H bell320
measure bell320
cz bell320 a2
cz bell320 a4
H bell310
measure bell310
cz bell310 b4
H bell318
measure bell318
cz bell318 a2
H bell322
cnot bell322 bell323
cnot a2 bell323
measure bell323
cnot bell323 bell322
cnot bell322 b3
H bell322
measure bell322
cz bell322 a2
H bell324
cnot bell324 bell325
cnot a2 bell325
measure bell325
cnot bell325 bell324
cnot bell324 b2
H bell324
measure bell324
cz bell324 a2
H bell326
cnot bell326 bell327
cnot a1 bell327
measure bell327
cnot bell327 bell326
cnot bell326 b1
H bell326
measure bell326
cz bell326 a1
cnot a1 b0
H bell328
cnot bell328 bell329
cnot a2 bell329
measure bell329
cnot bell329 bell328
cnot bell328 a6
H bell328
measure bell328
cz bell328 a2
H bell330
cnot bell330 bell331
cnot a2 bell331
measure bell331
cnot bell331 bell330
cnot bell330 a5
cnot bell330 a4
H bell330
measure bell330
cz bell330 a2
H bell332
cnot bell332 bell333
cnot a2 bell333
measure bell333
cnot bell333 bell332
cnot bell332 a3
H bell332
measure bell332
cz bell332 a2
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
reset bell214
reset bell215
reset bell216
reset bell217
reset bell218
reset bell219
reset bell220
reset bell221
reset bell222
reset bell223
reset bell224
reset bell225
reset bell226
reset bell227
reset bell228
reset bell229
reset bell230
reset bell231
reset bell232
reset bell233
reset bell234
reset bell235
reset bell236
reset bell237
reset bell238
reset bell239
reset bell240
reset bell241
reset bell242
reset bell243
reset bell244
reset bell245
reset bell246
reset bell247
reset bell248
reset bell249
reset bell250
reset bell251
reset bell252
reset bell253
reset bell254
reset bell255
reset bell256
reset bell257
reset bell258
reset bell259
reset bell260
reset bell261
reset bell262
reset bell263
reset bell264
reset bell265
reset bell266
reset bell267
reset bell268
reset bell269
reset bell270
reset bell271
reset bell272
reset bell273
reset bell274
reset bell275
reset bell276
reset bell277
reset bell278
reset bell279
reset bell280
reset bell281
reset bell282
reset bell283
reset bell284
reset bell285
reset bell286
reset bell287
reset bell288
reset bell289
reset bell290
reset bell291
reset bell292
reset bell293
reset bell294
reset bell295
reset bell296
reset bell297
reset bell298
reset bell299
reset bell300
reset bell301
reset bell302
reset bell303
reset bell304
reset bell305
reset bell306
reset bell307
reset bell308
reset bell309
reset bell310
reset bell311
reset bell312
reset bell313
reset bell314
reset bell315
reset bell316
reset bell317
reset bell318
reset bell319
reset bell320
reset bell321
reset bell322
reset bell323
reset bell324
reset bell325
reset bell326
reset bell327
reset bell328
reset bell329
reset bell330
reset bell331
reset bell332
reset bell333
END
