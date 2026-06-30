# Hyperedge cut (ebits): 62

# Actual ebits used (Synthesis): 139
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/ham15-low.qc):
#   Qubits: 17
#   H: 46
#   T: 161
#   cnot: 236
#   Depth: 238
#   T depth: 85
# Result (45.612ms):
#   Qubits: 295
#   H: 316
#   S: 3
#   T: 113
#   cnot: 640
#   cz: 141
#   measure: 278
#   reset: 280
#   swap: 1
#   Depth: 598
#   T depth: 92


# Result Circuit
.v a b c d e f g h i j k l m n o 0 1 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell256 bell257 bell258 bell259 bell26 bell260 bell261 bell262 bell263 bell264 bell265 bell266 bell267 bell268 bell269 bell27 bell270 bell271 bell272 bell273 bell274 bell275 bell276 bell277 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a b c d e f g h i j k l m n o
.o a b c d e f g h i j k l m n o
BEGIN 
H bell0
cnot bell0 bell1
cnot k bell1
measure bell1
cnot bell1 bell0
cnot bell0 a
H bell0
measure bell0
cz bell0 k
H bell2
cnot bell2 bell3
cnot k bell3
measure bell3
cnot bell3 bell2
cnot bell2 f
H bell2
measure bell2
cz bell2 k
H bell4
cnot bell4 bell5
cnot k bell5
measure bell5
cnot bell5 bell4
cnot bell4 g
H bell4
measure bell4
cz bell4 k
H bell6
cnot bell6 bell7
cnot h bell7
measure bell7
cnot bell7 bell6
H bell8
cnot bell8 bell9
cnot k bell9
measure bell9
cnot bell9 bell8
cnot bell8 bell6
H bell8
measure bell8
cz bell8 k
H bell10
cnot bell10 bell11
cnot m bell11
measure bell11
cnot bell11 bell10
cnot bell10 i
cnot m n
H bell12
cnot bell12 bell13
cnot n bell13
measure bell13
cnot bell13 bell12
cnot bell12 l
H bell12
measure bell12
cz bell12 n
H bell14
cnot bell14 bell15
cnot l bell15
measure bell15
cnot bell15 bell14
cnot bell14 n
H bell14
measure bell14
cz bell14 l
H bell16
cnot bell16 bell17
cnot i bell17
measure bell17
cnot bell17 bell16
cnot bell16 bell6
H bell18
cnot bell18 bell19
cnot bell6 bell19
measure bell19
cnot bell19 bell18
reset bell19
cnot h bell18
cnot bell18 h
H bell18
measure bell18
cz bell18 i
cz bell18 k
H bell6
measure bell6
cz bell6 h
H bell16
measure bell16
cz bell16 i
cnot i e
H i
T i
H bell20
cnot bell20 bell21
cnot l bell21
measure bell21
cnot bell21 bell20
cnot bell20 i
T* i
cnot bell10 i
T i
cnot bell20 i
H bell20
measure bell20
cz bell20 l
T* i
cnot bell10 i
H bell10
measure bell10
cz bell10 m
H i
T m
H bell22
cnot bell22 bell23
cnot l bell23
measure bell23
cnot bell23 bell22
cnot bell22 m
T* m
H bell24
cnot bell24 bell25
cnot o bell25
measure bell25
cnot bell25 bell24
cnot bell24 a
H bell24
measure bell24
cz bell24 o
cnot i e
H bell26
cnot bell26 bell27
cnot o bell27
measure bell27
cnot bell27 bell26
cnot bell26 g
H bell26
measure bell26
cz bell26 o
H bell28
cnot bell28 bell29
cnot i bell29
measure bell29
cnot bell29 bell28
cnot bell28 h
H bell28
measure bell28
cz bell28 i
H bell30
cnot bell30 bell31
cnot o bell31
measure bell31
cnot bell31 bell30
cnot bell30 i
H bell30
measure bell30
cz bell30 o
H bell32
cnot bell32 bell33
cnot o bell33
measure bell33
cnot bell33 bell32
cnot bell32 n
cnot bell22 m
H bell22
measure bell22
cz bell22 l
H bell34
cnot bell34 bell35
cnot m bell35
measure bell35
cnot bell35 bell34
cnot bell34 d
H bell34
measure bell34
cz bell34 m
H m
T m
cnot n m
T* m
cnot bell32 m
T m
cnot n m
T* m
cnot bell32 m
H bell32
measure bell32
cz bell32 o
H m
T o
H bell36
cnot bell36 bell37
cnot n bell37
measure bell37
cnot bell37 bell36
cnot bell36 o
T* o
H bell38
cnot bell38 bell39
cnot m bell39
measure bell39
cnot bell39 bell38
cnot bell38 d
H bell38
measure bell38
cz bell38 m
cnot bell36 o
H bell36
measure bell36
cz bell36 n
cnot m n
H o
T o
H bell40
cnot bell40 bell41
cnot m bell41
measure bell41
cnot bell41 bell40
cnot bell40 o
T* o
H bell42
cnot bell42 bell43
cnot n bell43
measure bell43
cnot bell43 bell42
cnot bell42 o
T o
cnot bell40 o
H bell40
measure bell40
cz bell40 m
T* o
cnot bell42 o
H bell42
measure bell42
cz bell42 n
H o
T m
H bell44
cnot bell44 bell45
cnot m bell45
measure bell45
cnot bell45 bell44
cnot bell44 k
H bell44
measure bell44
cz bell44 m
swap 0 1
H m
T m
cnot n m
T* m
H bell46
cnot bell46 bell47
cnot o bell47
measure bell47
cnot bell47 bell46
cnot bell46 m
T m
cnot n m
T* m
cnot bell46 m
H bell46
measure bell46
cz bell46 o
H m
H bell48
cnot bell48 bell49
cnot k bell49
measure bell49
cnot bell49 bell48
cnot bell48 e
cnot bell48 i
H bell48
measure bell48
cz bell48 k
H bell50
cnot bell50 bell51
cnot k bell51
measure bell51
cnot bell51 bell50
cnot bell50 j
H bell50
measure bell50
cz bell50 k
H bell52
cnot bell52 bell53
cnot m bell53
measure bell53
cnot bell53 bell52
cnot bell52 k
H bell52
measure bell52
cz bell52 m
H bell54
cnot bell54 bell55
cnot k bell55
measure bell55
cnot bell55 bell54
cnot bell54 d
H bell54
measure bell54
cz bell54 k
H bell56
cnot bell56 bell57
cnot k bell57
measure bell57
cnot bell57 bell56
cnot bell56 c
H bell56
measure bell56
cz bell56 k
H bell58
cnot bell58 bell59
cnot k bell59
measure bell59
cnot bell59 bell58
cnot bell58 b
H bell58
measure bell58
cz bell58 k
H 1
T 1
H bell60
cnot bell60 bell61
cnot l bell61
measure bell61
cnot bell61 bell60
cnot bell60 1
T* 1
H bell62
cnot bell62 bell63
cnot m bell63
measure bell63
cnot bell63 bell62
cnot bell62 1
T 1
cnot bell60 1
T* 1
cnot bell62 1
H 1
H 0
T 0
H bell64
cnot bell64 bell65
cnot 1 bell65
measure bell65
cnot bell65 bell64
cnot bell64 0
T* 0
H bell66
cnot bell66 bell67
cnot n bell67
measure bell67
cnot bell67 bell66
cnot bell66 0
T 0
cnot bell64 0
T* 0
cnot bell66 0
H 0
H k
T k
H bell68
cnot bell68 bell69
cnot 0 bell69
measure bell69
cnot bell69 bell68
cnot bell68 k
T* k
H bell70
cnot bell70 bell71
cnot o bell71
measure bell71
cnot bell71 bell70
cnot bell70 k
T k
cnot bell68 k
H bell68
measure bell68
cz bell68 0
T* k
cnot bell70 k
H bell70
measure bell70
cz bell70 o
H k
T 0
H bell72
cnot bell72 bell73
cnot o bell73
measure bell73
cnot bell73 bell72
cnot bell72 0
T* 0
cnot bell72 0
H bell72
measure bell72
cz bell72 o
H 0
T* 0
cnot bell64 0
T 0
cnot bell66 0
T* 0
cnot bell64 0
H bell64
measure bell64
cz bell64 1
T 0
cnot bell66 0
H 1
T* 1
cnot bell60 1
T 1
cnot bell62 1
T* 1
cnot bell60 1
H bell60
measure bell60
cz bell60 l
T 1
cnot bell62 1
H bell62
measure bell62
cz bell62 m
H 1
H bell74
cnot bell74 bell75
cnot k bell75
measure bell75
cnot bell75 bell74
cnot bell74 b
H bell74
measure bell74
cz bell74 k
H bell76
cnot bell76 bell77
cnot k bell77
measure bell77
cnot bell77 bell76
cnot bell76 c
H bell76
measure bell76
cz bell76 k
H bell78
cnot bell78 bell79
cnot k bell79
measure bell79
cnot bell79 bell78
cnot bell78 d
H bell78
measure bell78
cz bell78 k
H bell80
cnot bell80 bell81
cnot k bell81
measure bell81
cnot bell81 bell80
cnot bell80 e
H bell80
measure bell80
cz bell80 k
H bell82
cnot bell82 bell83
cnot k bell83
measure bell83
cnot bell83 bell82
cnot bell82 g
H bell82
measure bell82
cz bell82 k
H bell84
cnot bell84 bell85
cnot k bell85
measure bell85
cnot bell85 bell84
cnot bell84 j
H bell84
measure bell84
cz bell84 k
H bell86
cnot bell86 bell87
cnot l bell87
measure bell87
cnot bell87 bell86
cnot bell86 k
H bell86
measure bell86
cz bell86 l
T 0
H bell88
cnot bell88 bell89
cnot m bell89
measure bell89
cnot bell89 bell88
cnot bell88 0
T* 0
cnot bell66 0
T 0
cnot bell88 0
T* 0
cnot bell66 0
H 0
T l
H l
T l
H bell90
cnot bell90 bell91
cnot 0 bell91
measure bell91
cnot bell91 bell90
cnot bell90 l
T* l
H bell92
cnot bell92 bell93
cnot o bell93
measure bell93
cnot bell93 bell92
cnot bell92 l
T l
cnot bell90 l
H bell90
measure bell90
cz bell90 0
T* l
cnot bell92 l
H bell92
measure bell92
cz bell92 o
H l
T 0
H bell94
cnot bell94 bell95
cnot o bell95
measure bell95
cnot bell95 bell94
cnot bell94 0
T* 0
cnot bell94 0
H bell94
measure bell94
cz bell94 o
H 0
T* 0
cnot bell88 0
T 0
cnot bell66 0
T* 0
cnot bell88 0
H bell88
measure bell88
cz bell88 m
T 0
cnot bell66 0
H bell66
measure bell66
cz bell66 n
H bell96
cnot bell96 bell97
cnot k bell97
measure bell97
cnot bell97 bell96
cnot bell96 f
H bell96
measure bell96
cz bell96 k
H bell98
cnot bell98 bell99
cnot m bell99
measure bell99
cnot bell99 bell98
cnot bell98 h
H bell98
measure bell98
cz bell98 m
H bell100
cnot bell100 bell101
cnot n bell101
measure bell101
cnot bell101 bell100
cnot bell100 k
H bell100
measure bell100
cz bell100 n
H bell102
cnot bell102 bell103
cnot l bell103
measure bell103
cnot bell103 bell102
cnot bell102 k
H bell102
measure bell102
cz bell102 l
H bell104
cnot bell104 bell105
cnot l bell105
measure bell105
cnot bell105 bell104
cnot bell104 m
H bell104
measure bell104
cz bell104 l
T 0
H bell106
cnot bell106 bell107
cnot m bell107
measure bell107
cnot bell107 bell106
cnot bell106 0
T* 0
H bell108
cnot bell108 bell109
cnot n bell109
measure bell109
cnot bell109 bell108
cnot bell108 0
T 0
cnot bell106 0
T* 0
cnot bell108 0
H 0
H l
T l
H bell110
cnot bell110 bell111
cnot 0 bell111
measure bell111
cnot bell111 bell110
cnot bell110 l
T* l
H bell112
cnot bell112 bell113
cnot o bell113
measure bell113
cnot bell113 bell112
cnot bell112 l
T l
cnot bell110 l
H bell110
measure bell110
cz bell110 0
T* l
cnot bell112 l
H bell112
measure bell112
cz bell112 o
H l
T 0
H bell114
cnot bell114 bell115
cnot o bell115
measure bell115
cnot bell115 bell114
cnot bell114 0
T* 0
cnot bell114 0
H bell114
measure bell114
cz bell114 o
H 0
T* 0
cnot bell106 0
T 0
cnot bell108 0
T* 0
cnot bell106 0
H bell106
measure bell106
cz bell106 m
T 0
cnot bell108 0
H bell108
measure bell108
cz bell108 n
H bell116
cnot bell116 bell117
cnot n bell117
measure bell117
cnot bell117 bell116
cnot bell116 c
H bell116
measure bell116
cz bell116 n
H bell118
cnot bell118 bell119
cnot n bell119
measure bell119
cnot bell119 bell118
cnot bell118 d
H bell118
measure bell118
cz bell118 n
H bell120
cnot bell120 bell121
cnot l bell121
measure bell121
cnot bell121 bell120
cnot bell120 f
H bell120
measure bell120
cz bell120 l
H bell122
cnot bell122 bell123
cnot n bell123
measure bell123
cnot bell123 bell122
cnot bell122 e
H bell122
measure bell122
cz bell122 n
H bell124
cnot bell124 bell125
cnot l bell125
measure bell125
cnot bell125 bell124
cnot bell124 m
H bell124
measure bell124
cz bell124 l
H bell126
cnot bell126 bell127
cnot m bell127
measure bell127
cnot bell127 bell126
cnot bell126 j
H bell126
measure bell126
cz bell126 m
T 0
H bell128
cnot bell128 bell129
cnot l bell129
measure bell129
cnot bell129 bell128
cnot bell128 0
T* 0
H bell130
cnot bell130 bell131
cnot m bell131
measure bell131
cnot bell131 bell130
cnot bell130 0
T 0
cnot bell128 0
H bell128
measure bell128
cz bell128 l
T* 0
cnot bell130 0
H 0
S n
cnot m n
H bell132
cnot bell132 bell133
cnot l bell133
measure bell133
cnot bell133 bell132
cnot bell132 n
H bell134
cnot bell134 bell135
cnot o bell135
measure bell135
cnot bell135 bell134
cnot bell134 n
cnot m n
cnot bell132 n
H bell132
measure bell132
cz bell132 l
T* n
cnot bell134 n
H n
T n
H bell136
cnot bell136 bell137
cnot 0 bell137
measure bell137
cnot bell137 bell136
cnot bell136 n
T* n
cnot bell134 n
T n
cnot bell136 n
H bell136
measure bell136
cz bell136 0
T* n
cnot bell134 n
H bell134
measure bell134
cz bell134 o
H n
T 0
H bell138
cnot bell138 bell139
cnot o bell139
measure bell139
cnot bell139 bell138
cnot bell138 0
T* 0
cnot bell138 0
H bell138
measure bell138
cz bell138 o
H 0
T* 0
H bell140
cnot bell140 bell141
cnot l bell141
measure bell141
cnot bell141 bell140
cnot bell140 0
T 0
cnot bell130 0
T* 0
cnot bell140 0
H bell140
measure bell140
cz bell140 l
T 0
cnot bell130 0
H bell130
measure bell130
cz bell130 m
H bell142
cnot bell142 bell143
cnot n bell143
measure bell143
cnot bell143 bell142
cnot bell142 c
H bell142
measure bell142
cz bell142 n
H bell144
cnot bell144 bell145
cnot n bell145
measure bell145
cnot bell145 bell144
cnot bell144 d
H bell144
measure bell144
cz bell144 n
H bell146
cnot bell146 bell147
cnot n bell147
measure bell147
cnot bell147 bell146
cnot bell146 k
H bell146
measure bell146
cz bell146 n
H bell148
cnot bell148 bell149
cnot k bell149
measure bell149
cnot bell149 bell148
cnot bell148 i
H bell148
measure bell148
cz bell148 k
H bell150
cnot bell150 bell151
cnot m bell151
measure bell151
cnot bell151 bell150
cnot bell150 c
H bell150
measure bell150
cz bell150 m
H bell152
cnot bell152 bell153
cnot k bell153
measure bell153
cnot bell153 bell152
cnot bell152 a
H bell152
measure bell152
cz bell152 k
H bell154
cnot bell154 bell155
cnot m bell155
measure bell155
cnot bell155 bell154
cnot bell154 a
H bell154
measure bell154
cz bell154 m
H m
T m
H bell156
cnot bell156 bell157
cnot l bell157
measure bell157
cnot bell157 bell156
cnot bell156 m
T* m
H bell158
cnot bell158 bell159
cnot o bell159
measure bell159
cnot bell159 bell158
cnot bell158 m
T m
cnot bell156 m
H bell156
measure bell156
cz bell156 l
T* m
cnot bell158 m
H bell158
measure bell158
cz bell158 o
H m
H bell160
cnot bell160 bell161
cnot m bell161
measure bell161
cnot bell161 bell160
cnot bell160 c
H bell162
cnot bell162 bell163
cnot o bell163
measure bell163
cnot bell163 bell162
cnot bell162 g
H bell162
measure bell162
cz bell162 o
H bell164
cnot bell164 bell165
cnot h bell165
measure bell165
cnot bell165 bell164
cnot bell160 bell164
H bell160
measure bell160
cz bell160 m
H bell166
cnot bell166 bell167
cnot o bell167
measure bell167
cnot bell167 bell166
cnot bell166 k
H bell166
measure bell166
cz bell166 o
H bell168
cnot bell168 bell169
cnot o bell169
measure bell169
cnot bell169 bell168
cnot bell168 n
H bell168
measure bell168
cz bell168 o
H bell170
cnot bell170 bell171
cnot k bell171
measure bell171
cnot bell171 bell170
cnot bell170 bell164
H bell172
cnot bell172 bell173
cnot bell164 bell173
measure bell173
cnot bell173 bell172
reset bell173
cnot h bell172
cnot bell172 h
H bell172
measure bell172
cz bell172 k
cz bell172 m
H bell164
measure bell164
cz bell164 h
H bell170
measure bell170
cz bell170 k
H bell174
cnot bell174 bell175
cnot n bell175
measure bell175
cnot bell175 bell174
cnot bell174 e
H bell174
measure bell174
cz bell174 n
T 0
H bell176
cnot bell176 bell177
cnot l bell177
measure bell177
cnot bell177 bell176
cnot bell176 0
T* 0
H bell178
cnot bell178 bell179
cnot m bell179
measure bell179
cnot bell179 bell178
cnot bell178 0
T 0
cnot bell176 0
H bell176
measure bell176
cz bell176 l
T* 0
cnot bell178 0
H 0
S* o
H bell180
cnot bell180 bell181
cnot l bell181
measure bell181
cnot bell181 bell180
cnot bell180 o
T* o
cnot bell180 o
H bell180
measure bell180
cz bell180 l
H o
T o
H bell182
cnot bell182 bell183
cnot 0 bell183
measure bell183
cnot bell183 bell182
cnot bell182 o
T* o
H bell184
cnot bell184 bell185
cnot n bell185
measure bell185
cnot bell185 bell184
cnot bell184 o
T o
cnot bell182 o
H bell182
measure bell182
cz bell182 0
T* o
cnot bell184 o
H bell184
measure bell184
cz bell184 n
H o
T 0
H bell186
cnot bell186 bell187
cnot n bell187
measure bell187
cnot bell187 bell186
cnot bell186 0
T* 0
cnot bell186 0
H bell186
measure bell186
cz bell186 n
H 0
T* 0
H bell188
cnot bell188 bell189
cnot l bell189
measure bell189
cnot bell189 bell188
cnot bell188 0
T 0
cnot bell178 0
T* 0
cnot bell188 0
H bell188
measure bell188
cz bell188 l
T 0
cnot bell178 0
H bell178
measure bell178
cz bell178 m
H 0
T l
H bell190
cnot bell190 bell191
cnot o bell191
measure bell191
cnot bell191 bell190
cnot bell190 g
H bell190
measure bell190
cz bell190 o
H bell192
cnot bell192 bell193
cnot o bell193
measure bell193
cnot bell193 bell192
cnot bell192 k
H bell192
measure bell192
cz bell192 o
H bell194
cnot bell194 bell195
cnot o bell195
measure bell195
cnot bell195 bell194
cnot bell194 l
H bell194
measure bell194
cz bell194 o
H bell196
cnot bell196 bell197
cnot o bell197
measure bell197
cnot bell197 bell196
cnot bell196 m
H bell196
measure bell196
cz bell196 o
H bell198
cnot bell198 bell199
cnot m bell199
measure bell199
cnot bell199 bell198
cnot bell198 e
H bell198
measure bell198
cz bell198 m
H bell200
cnot bell200 bell201
cnot m bell201
measure bell201
cnot bell201 bell200
cnot bell200 a
H bell200
measure bell200
cz bell200 m
H o
T o
H bell202
cnot bell202 bell203
cnot l bell203
measure bell203
cnot bell203 bell202
cnot bell202 o
T* o
H bell204
cnot bell204 bell205
cnot n bell205
measure bell205
cnot bell205 bell204
cnot bell204 o
T o
cnot bell202 o
H bell202
measure bell202
cz bell202 l
T* o
cnot bell204 o
H bell204
measure bell204
cz bell204 n
H o
T l
S n
H bell206
cnot bell206 bell207
cnot l bell207
measure bell207
cnot bell207 bell206
cnot bell206 n
T* n
cnot bell206 m
H bell206
measure bell206
cz bell206 l
H bell208
cnot bell208 bell209
cnot k bell209
measure bell209
cnot bell209 bell208
cnot bell208 g
H bell208
measure bell208
cz bell208 k
H bell210
cnot bell210 bell211
cnot k bell211
measure bell211
cnot bell211 bell210
cnot bell210 j
H bell210
measure bell210
cz bell210 k
H bell212
cnot bell212 bell213
cnot o bell213
measure bell213
cnot bell213 bell212
cnot bell212 l
H bell212
measure bell212
cz bell212 o
H bell214
cnot bell214 bell215
cnot o bell215
measure bell215
cnot bell215 bell214
cnot bell214 m
H bell214
measure bell214
cz bell214 o
H bell216
cnot bell216 bell217
cnot l bell217
measure bell217
cnot bell217 bell216
cnot bell216 n
cnot bell216 m
H bell216
measure bell216
cz bell216 l
H bell218
cnot bell218 bell219
cnot n bell219
measure bell219
cnot bell219 bell218
cnot bell218 k
H bell218
measure bell218
cz bell218 n
H bell220
cnot bell220 bell221
cnot k bell221
measure bell221
cnot bell221 bell220
cnot bell220 n
H bell220
measure bell220
cz bell220 k
H bell222
cnot bell222 bell223
cnot n bell223
measure bell223
cnot bell223 bell222
cnot bell222 o
H bell222
measure bell222
cz bell222 n
H bell224
cnot bell224 bell225
cnot j bell225
measure bell225
cnot bell225 bell224
cnot bell224 m
H bell224
measure bell224
cz bell224 j
H bell226
cnot bell226 bell227
cnot j bell227
measure bell227
cnot bell227 bell226
cnot bell226 i
H bell226
measure bell226
cz bell226 j
H bell228
cnot bell228 bell229
cnot i bell229
measure bell229
cnot bell229 bell228
cnot bell228 m
H bell228
measure bell228
cz bell228 i
H bell230
cnot bell230 bell231
cnot i bell231
measure bell231
cnot bell231 bell230
cnot bell230 l
H bell230
measure bell230
cz bell230 i
H bell232
cnot bell232 bell233
cnot i bell233
measure bell233
cnot bell233 bell232
cnot bell232 h
H bell232
measure bell232
cz bell232 i
H bell234
cnot bell234 bell235
cnot h bell235
measure bell235
cnot bell235 bell234
cnot bell234 l
H bell234
measure bell234
cz bell234 h
H bell236
cnot bell236 bell237
cnot j bell237
measure bell237
cnot bell237 bell236
cnot bell236 n
H bell236
measure bell236
cz bell236 j
H bell238
cnot bell238 bell239
cnot h bell239
measure bell239
cnot bell239 bell238
cnot bell238 k
H bell238
measure bell238
cz bell238 h
H bell240
cnot bell240 bell241
cnot h bell241
measure bell241
cnot bell241 bell240
cnot bell240 g
H bell240
measure bell240
cz bell240 h
H bell242
cnot bell242 bell243
cnot g bell243
measure bell243
cnot bell243 bell242
cnot bell242 j
H bell242
measure bell242
cz bell242 g
H bell244
cnot bell244 bell245
cnot j bell245
measure bell245
cnot bell245 bell244
cnot bell244 f
H bell244
measure bell244
cz bell244 j
H bell246
cnot bell246 bell247
cnot f bell247
measure bell247
cnot bell247 bell246
cnot bell246 j
H bell246
measure bell246
cz bell246 f
H bell248
cnot bell248 bell249
cnot f bell249
measure bell249
cnot bell249 bell248
cnot bell248 i
H bell248
measure bell248
cz bell248 f
cnot i e
cnot e i
H bell250
cnot bell250 bell251
cnot g bell251
measure bell251
cnot bell251 bell250
cnot bell250 k
H bell250
measure bell250
cz bell250 g
H bell252
cnot bell252 bell253
cnot e bell253
measure bell253
cnot bell253 bell252
cnot bell252 h
H bell252
measure bell252
cz bell252 e
H bell254
cnot bell254 bell255
cnot h bell255
measure bell255
cnot bell255 bell254
cnot bell254 d
H bell254
measure bell254
cz bell254 h
H bell256
cnot bell256 bell257
cnot d bell257
measure bell257
cnot bell257 bell256
cnot bell256 g
H bell256
measure bell256
cz bell256 d
H bell258
cnot bell258 bell259
cnot g bell259
measure bell259
cnot bell259 bell258
cnot bell258 c
H bell258
measure bell258
cz bell258 g
H bell260
cnot bell260 bell261
cnot c bell261
measure bell261
cnot bell261 bell260
cnot bell260 g
H bell260
measure bell260
cz bell260 c
H bell262
cnot bell262 bell263
cnot c bell263
measure bell263
cnot bell263 bell262
cnot bell262 f
H bell262
measure bell262
cz bell262 c
H bell264
cnot bell264 bell265
cnot f bell265
measure bell265
cnot bell265 bell264
cnot bell264 b
H bell264
measure bell264
cz bell264 f
H bell266
cnot bell266 bell267
cnot b bell267
measure bell267
cnot bell267 bell266
cnot bell266 f
H bell266
measure bell266
cz bell266 b
H bell268
cnot bell268 bell269
cnot d bell269
measure bell269
cnot bell269 bell268
cnot bell268 h
H bell268
measure bell268
cz bell268 d
H bell270
cnot bell270 bell271
cnot b bell271
measure bell271
cnot bell271 bell270
cnot bell270 e
H bell270
measure bell270
cz bell270 b
H bell272
cnot bell272 bell273
cnot e bell273
measure bell273
cnot bell273 bell272
cnot bell272 a
H bell272
measure bell272
cz bell272 e
H bell274
cnot bell274 bell275
cnot a bell275
measure bell275
cnot bell275 bell274
cnot bell274 e
H bell274
measure bell274
cz bell274 a
H bell276
cnot bell276 bell277
cnot a bell277
measure bell277
cnot bell277 bell276
cnot bell276 d
H bell276
measure bell276
cz bell276 a
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
END
