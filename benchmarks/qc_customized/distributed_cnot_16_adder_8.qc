# Hyperedge cut (ebits): 80

# Actual ebits used (Synthesis): 132
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/adder_8.qc):
#   Qubits: 24
#   H: 80
#   T: 399
#   X: 12
#   cnot: 409
#   Depth: 191
#   T depth: 82
# Result (114.674ms):
#   Qubits: 288
#   H: 344
#   S: 44
#   T: 215
#   Z: 23
#   cnot: 797
#   cz: 133
#   measure: 264
#   reset: 265
#   Depth: 346
#   T depth: 74


# Result Circuit
.v b0 a0 b1 a1 c1 b2 a2 b3 a3 c3 d3 b4 a4 b5 a5 c5 d5 e5 b6 a6 b7 a7 z c7 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell256 bell257 bell258 bell259 bell26 bell260 bell261 bell262 bell263 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i b0 a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 b6 a6 b7 a7 z
.o b0 a0 b1 a1 c1 b2 a2 b3 a3 c3 d3 b4 a4 b5 a5 c5 d5 e5 b6 a6 b7 a7 z c7
BEGIN 
H bell0
cnot bell0 bell1
cnot a7 bell1
measure bell1
cnot bell1 bell0
cnot bell0 z
H bell0
measure bell0
cz bell0 a7
H bell2
cnot bell2 bell3
cnot a7 bell3
measure bell3
cnot bell3 bell2
cnot bell2 b7
H bell2
measure bell2
cz bell2 a7
H bell4
cnot bell4 bell5
cnot a5 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c5
H bell4
measure bell4
cz bell4 a5
H bell6
cnot bell6 bell7
cnot a3 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c3
H bell8
cnot bell8 bell9
cnot a5 bell9
measure bell9
cnot bell9 bell8
cnot bell8 b5
H bell8
measure bell8
cz bell8 a5
cnot bell6 b3
H bell6
measure bell6
cz bell6 a3
H bell10
cnot bell10 bell11
cnot a1 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c1
H bell10
measure bell10
cz bell10 a1
cnot a1 b1
H a1
H a3
H a5
H a7
T a1
H bell12
cnot bell12 bell13
cnot a0 bell13
measure bell13
cnot bell13 bell12
cnot bell12 a1
T* a1
H bell14
cnot bell14 bell15
cnot b0 bell15
measure bell15
cnot bell15 bell14
cnot bell14 a1
T a1
cnot bell12 a1
T* a1
cnot bell14 a1
H a1
T a3
H bell16
cnot bell16 bell17
cnot a2 bell17
measure bell17
cnot bell17 bell16
cnot bell16 a3
T* a3
H bell18
cnot bell18 bell19
cnot b2 bell19
measure bell19
cnot bell19 bell18
cnot bell18 a3
T a3
cnot bell16 a3
H bell16
measure bell16
cz bell16 a2
T* a3
cnot bell18 a3
H a3
T a5
H bell20
cnot bell20 bell21
cnot a4 bell21
measure bell21
cnot bell21 bell20
cnot bell20 a5
T* a5
cnot b4 a5
T a5
cnot bell20 a5
T* a5
cnot b4 a5
H a5
T a7
H bell22
cnot bell22 bell23
cnot a6 bell23
measure bell23
cnot bell23 bell22
cnot bell22 a7
T* a7
cnot b6 a7
T a7
cnot bell22 a7
T* a7
cnot b6 a7
H a7
H c1
H c3
H c5
H z
H d3
H d5
H c7
T c1
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
T c1
cnot bell24 c1
H bell24
measure bell24
cz bell24 a1
T* c1
cnot bell18 a3
H bell18
measure bell18
cz bell18 b2
cnot b4 a5
cnot b6 a7
cnot bell26 c1
H bell26
measure bell26
cz bell26 b1
cnot bell22 a7
cnot bell22 b6
cnot bell20 a5
cnot bell20 b4
H bell28
cnot bell28 bell29
cnot a2 bell29
measure bell29
cnot bell29 bell28
cnot bell28 b2
H bell28
measure bell28
cz bell28 a2
H bell30
cnot bell30 bell31
cnot a2 bell31
measure bell31
cnot bell31 bell30
cnot bell30 a3
H bell30
measure bell30
cz bell30 a2
H c1
S d3
cnot a3 d3
T* d3
H bell32
cnot bell32 bell33
cnot b3 bell33
measure bell33
cnot bell33 bell32
cnot bell32 d3
T d3
cnot a3 d3
S* d3
H bell34
cnot bell34 bell35
cnot b2 bell35
measure bell35
cnot bell35 bell34
cnot bell34 d3
cnot a3 d3
T d3
cnot bell32 d3
T* d3
cnot bell34 d3
H bell34
measure bell34
cz bell34 b2
cnot a3 d3
H d3
T c5
H bell36
cnot bell36 bell37
cnot b4 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c5
H bell38
cnot bell38 bell39
cnot a5 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c5
T* c5
H bell40
cnot bell40 bell41
cnot b5 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c5
T c5
cnot bell36 c5
cnot bell38 c5
T* c5
cnot bell40 c5
H c5
S d5
cnot bell38 d5
T* d5
cnot bell40 d5
T d5
cnot bell38 d5
S* d5
cnot bell36 d5
cnot bell38 d5
T d5
cnot bell40 d5
H bell40
measure bell40
cz bell40 b5
T* d5
cnot bell36 d5
H bell36
measure bell36
cz bell36 b4
cnot bell38 d5
H bell38
measure bell38
cz bell38 a5
H d5
S c7
H bell42
cnot bell42 bell43
cnot a7 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c7
T* c7
H bell44
cnot bell44 bell45
cnot b7 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c7
T c7
cnot bell42 c7
S* c7
H bell46
cnot bell46 bell47
cnot b6 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c7
cnot bell42 c7
T c7
cnot bell44 c7
T* c7
cnot bell46 c7
cnot bell42 c7
H c7
H e5
T e5
H bell48
cnot bell48 bell49
cnot c7 bell49
measure bell49
cnot bell49 bell48
cnot bell48 e5
T* e5
H bell50
cnot bell50 bell51
cnot d5 bell51
measure bell51
cnot bell51 bell50
cnot bell50 e5
T e5
cnot bell48 e5
H bell48
measure bell48
cz bell48 c7
T* e5
cnot bell50 e5
H e5
S c3
H bell52
cnot bell52 bell53
cnot b2 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c3
H bell54
cnot bell54 bell55
cnot a3 bell55
measure bell55
cnot bell55 bell54
cnot bell54 c3
T* c3
cnot b3 c3
T c3
cnot bell52 c3
H bell52
measure bell52
cz bell52 b2
cnot bell54 c3
H bell54
measure bell54
cz bell54 a3
T* c3
H bell56
cnot bell56 bell57
cnot c1 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c3
cnot b3 c3
T* c3
H bell58
cnot bell58 bell59
cnot d3 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c3
T c3
cnot bell56 c3
H bell56
measure bell56
cz bell56 c1
T* c3
cnot bell58 c3
H bell58
measure bell58
cz bell58 d3
H c3
T c5
H bell60
cnot bell60 bell61
cnot c7 bell61
measure bell61
cnot bell61 bell60
cnot bell60 c5
T* c5
H bell62
cnot bell62 bell63
cnot z bell63
measure bell63
cnot bell63 bell62
cnot bell62 c5
T c5
cnot bell60 c5
H bell60
measure bell60
cz bell60 c7
T* c5
cnot bell62 c5
H bell62
measure bell62
cz bell62 z
H c5
T c5
H bell64
cnot bell64 bell65
cnot c3 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c5
T* c5
cnot d5 c5
T c5
cnot bell64 c5
H bell64
measure bell64
cz bell64 c3
T* c5
cnot d5 c5
H c5
T* z
Z z
cnot bell46 z
cnot bell42 z
T* z
cnot bell44 z
T z
cnot bell46 z
cnot bell42 z
T* z
H bell66
cnot bell66 bell67
cnot c3 bell67
measure bell67
cnot bell67 bell66
cnot bell66 z
cnot bell44 z
T* z
H bell68
cnot bell68 bell69
cnot e5 bell69
measure bell69
cnot bell69 bell68
cnot bell68 z
T z
cnot bell66 z
H bell66
measure bell66
cz bell66 c3
T* z
cnot c7 z
cnot bell68 z
H bell68
measure bell68
cz bell68 e5
T* z
cnot c7 z
H z
T e5
H bell70
cnot bell70 bell71
cnot c3 bell71
measure bell71
cnot bell71 bell70
cnot bell70 e5
T* e5
cnot bell70 e5
H bell70
measure bell70
cz bell70 c3
H e5
T e5
H bell72
cnot bell72 bell73
cnot c7 bell73
measure bell73
cnot bell73 bell72
cnot bell72 e5
T* e5
cnot bell50 e5
T e5
cnot bell72 e5
H bell72
measure bell72
cz bell72 c7
T* e5
cnot bell50 e5
H bell50
measure bell50
cz bell50 d5
H e5
T d3
H bell74
cnot bell74 bell75
cnot c1 bell75
measure bell75
cnot bell75 bell74
cnot bell74 d3
T* d3
cnot bell74 d3
H bell74
measure bell74
cz bell74 c1
H d3
T* d5
Z d5
H bell76
cnot bell76 bell77
cnot c3 bell77
measure bell77
cnot bell77 bell76
cnot bell76 d5
T* d5
H bell78
cnot bell78 bell79
cnot c7 bell79
measure bell79
cnot bell79 bell78
cnot bell78 d5
cnot bell76 d5
H bell76
measure bell76
cz bell76 c3
S* d5
cnot bell78 d5
H bell78
measure bell78
cz bell78 c7
H d5
T* c7
Z c7
H c7
S c7
cnot bell42 c7
T* c7
cnot bell44 c7
T c7
cnot bell42 c7
S* c7
cnot bell46 c7
H bell46
measure bell46
cz bell46 b6
cnot bell42 c7
H bell42
measure bell42
cz bell42 a7
T c7
cnot bell44 c7
H bell44
measure bell44
cz bell44 b7
T* c7
H bell80
cnot bell80 bell81
cnot b2 bell81
measure bell81
cnot bell81 bell80
cnot bell80 a3
H bell80
measure bell80
cz bell80 b2
cnot b4 a5
cnot b6 a7
H bell82
cnot bell82 bell83
cnot a7 bell83
measure bell83
cnot bell83 bell82
cnot bell82 c7
H bell82
measure bell82
cz bell82 a7
cnot bell22 b6
cnot bell20 b4
H bell84
cnot bell84 bell85
cnot a2 bell85
measure bell85
cnot bell85 bell84
cnot bell84 b2
H bell84
measure bell84
cz bell84 a2
H c7
T a1
cnot b1 a1
T* a1
cnot b1 a1
H a1
T* a3
Z a3
H bell86
cnot bell86 bell87
cnot b2 bell87
measure bell87
cnot bell87 bell86
cnot bell86 a3
H bell88
cnot bell88 bell89
cnot a2 bell89
measure bell89
cnot bell89 bell88
cnot bell88 a3
S a3
cnot bell32 a3
S* a3
cnot bell86 a3
cnot bell88 a3
T a3
Z a3
cnot d3 a3
T a3
cnot bell86 a3
cnot bell88 a3
T a3
cnot bell32 a3
H bell32
measure bell32
cz bell32 b3
T* a3
cnot bell86 a3
cnot bell88 a3
T* a3
cnot d3 a3
H a3
T* a5
Z a5
cnot b4 a5
cnot bell20 a5
S a5
H bell90
cnot bell90 bell91
cnot b5 bell91
measure bell91
cnot bell91 bell90
cnot bell90 a5
S* a5
cnot b4 a5
cnot bell20 a5
T a5
Z a5
H bell92
cnot bell92 bell93
cnot d5 bell93
measure bell93
cnot bell93 bell92
cnot bell92 a5
T a5
cnot b4 a5
cnot bell20 a5
T a5
cnot bell90 a5
H bell90
measure bell90
cz bell90 b5
T* a5
cnot b4 a5
cnot bell20 a5
T* a5
cnot bell92 a5
H bell92
measure bell92
cz bell92 d5
H a5
T* a7
Z a7
cnot b6 a7
cnot bell22 a7
S a7
H bell94
cnot bell94 bell95
cnot b7 bell95
measure bell95
cnot bell95 bell94
cnot bell94 a7
S* a7
cnot b6 a7
cnot bell22 a7
T a7
Z a7
cnot bell94 a7
H bell94
measure bell94
cz bell94 b7
H a7
T a1
cnot bell12 a1
T* a1
cnot bell14 a1
T a1
cnot bell12 a1
T* a1
cnot bell14 a1
H a1
T a3
cnot bell88 a3
T* a3
cnot bell86 a3
T a3
cnot bell88 a3
H bell88
measure bell88
cz bell88 a2
T* a3
cnot bell86 a3
H bell86
measure bell86
cz bell86 b2
H a3
T a5
cnot bell20 a5
T* a5
cnot b4 a5
T a5
cnot bell20 a5
H bell20
measure bell20
cz bell20 a4
T* a5
cnot b4 a5
H a5
T a7
cnot bell22 a7
T* a7
cnot b6 a7
T a7
cnot bell22 a7
H bell22
measure bell22
cz bell22 a6
T* a7
cnot b6 a7
H a7
T b1
H bell96
cnot bell96 bell97
cnot c1 bell97
measure bell97
cnot bell97 bell96
cnot bell96 a2
H bell96
measure bell96
cz bell96 c1
H bell98
cnot bell98 bell99
cnot c1 bell99
measure bell99
cnot bell99 bell98
cnot bell98 a3
H bell98
measure bell98
cz bell98 c1
H bell100
cnot bell100 bell101
cnot c3 bell101
measure bell101
cnot bell101 bell100
cnot bell100 a4
H bell100
measure bell100
cz bell100 c3
H bell102
cnot bell102 bell103
cnot c3 bell103
measure bell103
cnot bell103 bell102
cnot bell102 a5
H bell104
cnot bell104 bell105
cnot c5 bell105
measure bell105
cnot bell105 bell104
cnot bell104 a6
H bell104
measure bell104
cz bell104 c5
H bell106
cnot bell106 bell107
cnot c5 bell107
measure bell107
cnot bell107 bell106
cnot bell106 a7
H bell108
cnot bell108 bell109
cnot c1 bell109
measure bell109
cnot bell109 bell108
cnot bell108 b2
H bell108
measure bell108
cz bell108 c1
H bell110
cnot bell110 bell111
cnot c1 bell111
measure bell111
cnot bell111 bell110
cnot bell110 b3
H bell110
measure bell110
cz bell110 c1
cnot bell106 b6
H bell106
measure bell106
cz bell106 c5
cnot bell102 b4
H bell102
measure bell102
cz bell102 c3
H bell112
cnot bell112 bell113
cnot c3 bell113
measure bell113
cnot bell113 bell112
cnot bell112 b5
H bell112
measure bell112
cz bell112 c3
H bell114
cnot bell114 bell115
cnot c5 bell115
measure bell115
cnot bell115 bell114
cnot bell114 b7
H bell114
measure bell114
cz bell114 c5
H bell116
cnot bell116 bell117
cnot a7 bell117
measure bell117
cnot bell117 bell116
cnot bell116 b7
H bell116
measure bell116
cz bell116 a7
H bell118
cnot bell118 bell119
cnot a6 bell119
measure bell119
cnot bell119 bell118
cnot bell118 a7
cnot bell118 b6
H bell118
measure bell118
cz bell118 a6
H bell120
cnot bell120 bell121
cnot a5 bell121
measure bell121
cnot bell121 bell120
cnot bell120 b5
H bell120
measure bell120
cz bell120 a5
H bell122
cnot bell122 bell123
cnot a4 bell123
measure bell123
cnot bell123 bell122
cnot bell122 a5
cnot bell122 b4
H bell122
measure bell122
cz bell122 a4
H bell124
cnot bell124 bell125
cnot a3 bell125
measure bell125
cnot bell125 bell124
cnot bell124 b3
H bell124
measure bell124
cz bell124 a3
H bell126
cnot bell126 bell127
cnot a2 bell127
measure bell127
cnot bell127 bell126
cnot bell126 b2
H bell126
measure bell126
cz bell126 a2
cnot a1 b1
H bell128
cnot bell128 bell129
cnot a2 bell129
measure bell129
cnot bell129 bell128
cnot bell128 a3
H bell128
measure bell128
cz bell128 a2
H a1
H bell130
cnot bell130 bell131
cnot b3 bell131
measure bell131
cnot bell131 bell130
cnot bell130 c1
H bell132
cnot bell132 bell133
cnot a3 bell133
measure bell133
cnot bell133 bell132
cnot bell132 c1
H bell134
cnot bell134 bell135
cnot a2 bell135
measure bell135
cnot bell135 bell134
cnot bell134 c1
T c1
Z c1
H bell136
cnot bell136 bell137
cnot d3 bell137
measure bell137
cnot bell137 bell136
cnot bell136 c1
S* c1
cnot bell136 c1
H bell136
measure bell136
cz bell136 d3
cnot bell130 c1
H bell130
measure bell130
cz bell130 b3
cnot bell132 c1
H bell132
measure bell132
cz bell132 a3
cnot bell134 c1
H bell134
measure bell134
cz bell134 a2
H a3
H bell138
cnot bell138 bell139
cnot b5 bell139
measure bell139
cnot bell139 bell138
cnot bell138 c3
H bell140
cnot bell140 bell141
cnot a5 bell141
measure bell141
cnot bell141 bell140
cnot bell140 c3
H bell142
cnot bell142 bell143
cnot a4 bell143
measure bell143
cnot bell143 bell142
cnot bell142 c3
T c3
Z c3
H bell144
cnot bell144 bell145
cnot d5 bell145
measure bell145
cnot bell145 bell144
cnot bell144 c3
S* c3
cnot bell144 c3
H bell144
measure bell144
cz bell144 d5
cnot bell138 c3
H bell138
measure bell138
cz bell138 b5
cnot bell140 c3
H bell140
measure bell140
cz bell140 a5
cnot bell142 c3
H bell142
measure bell142
cz bell142 a4
H a5
H bell146
cnot bell146 bell147
cnot b7 bell147
measure bell147
cnot bell147 bell146
cnot bell146 c5
H bell148
cnot bell148 bell149
cnot a7 bell149
measure bell149
cnot bell149 bell148
cnot bell148 c5
H bell150
cnot bell150 bell151
cnot a6 bell151
measure bell151
cnot bell151 bell150
cnot bell150 c5
T c5
Z c5
cnot bell146 c5
H bell146
measure bell146
cz bell146 b7
cnot bell148 c5
H bell148
measure bell148
cz bell148 a7
cnot bell150 c5
H bell150
measure bell150
cz bell150 a6
H a7
T a1
cnot bell12 a1
T* a1
cnot bell14 a1
T a1
cnot bell12 a1
T* a1
cnot bell14 a1
H a1
T a3
H bell152
cnot bell152 bell153
cnot a2 bell153
measure bell153
cnot bell153 bell152
cnot bell152 a3
T* a3
H bell154
cnot bell154 bell155
cnot b2 bell155
measure bell155
cnot bell155 bell154
cnot bell154 a3
T a3
cnot bell152 a3
T* a3
cnot bell154 a3
H a3
T a5
H bell156
cnot bell156 bell157
cnot a4 bell157
measure bell157
cnot bell157 bell156
cnot bell156 a5
T* a5
cnot b4 a5
T a5
cnot bell156 a5
T* a5
cnot b4 a5
H a5
T a7
H bell158
cnot bell158 bell159
cnot a6 bell159
measure bell159
cnot bell159 bell158
cnot bell158 a7
T* a7
cnot b6 a7
T a7
cnot bell158 a7
T* a7
cnot b6 a7
H a7
H bell160
cnot bell160 bell161
cnot a7 bell161
measure bell161
cnot bell161 bell160
cnot bell160 b7
H bell160
measure bell160
cz bell160 a7
H bell162
cnot bell162 bell163
cnot a5 bell163
measure bell163
cnot bell163 bell162
cnot bell162 b5
H bell162
measure bell162
cz bell162 a5
H bell164
cnot bell164 bell165
cnot a3 bell165
measure bell165
cnot bell165 bell164
cnot bell164 b3
H bell164
measure bell164
cz bell164 a3
cnot a1 b1
H a1
H a3
H a5
H a7
T a1
cnot bell12 a1
T* a1
cnot bell14 a1
T a1
cnot bell12 a1
T* a1
cnot bell14 a1
H bell14
measure bell14
cz bell14 b0
H a1
T a3
cnot bell152 a3
T* a3
cnot bell154 a3
T a3
cnot bell152 a3
H bell152
measure bell152
cz bell152 a2
T* a3
cnot bell154 a3
H bell154
measure bell154
cz bell154 b2
H a3
T a5
cnot bell156 a5
T* a5
cnot b4 a5
T a5
cnot bell156 a5
H bell156
measure bell156
cz bell156 a4
T* a5
cnot b4 a5
H a5
T a7
cnot bell158 a7
T* a7
cnot b6 a7
T a7
cnot bell158 a7
H bell158
measure bell158
cz bell158 a6
T* a7
cnot b6 a7
H a7
H bell166
cnot bell166 bell167
cnot c1 bell167
measure bell167
cnot bell167 bell166
cnot bell166 a2
H bell166
measure bell166
cz bell166 c1
H bell168
cnot bell168 bell169
cnot c3 bell169
measure bell169
cnot bell169 bell168
cnot bell168 a4
H bell168
measure bell168
cz bell168 c3
H bell170
cnot bell170 bell171
cnot c5 bell171
measure bell171
cnot bell171 bell170
cnot bell170 a6
H bell170
measure bell170
cz bell170 c5
H bell172
cnot bell172 bell173
cnot c1 bell173
measure bell173
cnot bell173 bell172
cnot bell172 b2
H bell172
measure bell172
cz bell172 c1
H bell174
cnot bell174 bell175
cnot c3 bell175
measure bell175
cnot bell175 bell174
cnot bell174 b4
H bell174
measure bell174
cz bell174 c3
H bell176
cnot bell176 bell177
cnot c5 bell177
measure bell177
cnot bell177 bell176
cnot bell176 b6
H bell176
measure bell176
cz bell176 c5
H bell178
cnot bell178 bell179
cnot a6 bell179
measure bell179
cnot bell179 bell178
cnot bell178 a7
H bell178
measure bell178
cz bell178 a6
H bell180
cnot bell180 bell181
cnot a4 bell181
measure bell181
cnot bell181 bell180
cnot bell180 a5
H bell182
cnot bell182 bell183
cnot a5 bell183
measure bell183
cnot bell183 bell182
cnot bell182 b5
H bell182
measure bell182
cz bell182 a5
H bell184
cnot bell184 bell185
cnot b3 bell185
measure bell185
cnot bell185 bell184
cnot a3 bell184
H bell186
cnot bell186 bell187
cnot a2 bell187
measure bell187
cnot bell187 bell186
cnot bell186 bell184
H bell188
cnot bell188 bell189
cnot bell184 bell189
measure bell189
cnot bell189 bell188
reset bell189
cnot b3 bell188
cnot bell188 b3
H bell188
measure bell188
cz bell188 a2
cz bell188 a3
H bell184
measure bell184
cz bell184 b3
cnot a1 b1
cnot a0 b0
cnot bell186 a3
H a1
H a3
H a5
T a1
cnot bell12 a1
T* a1
H bell190
cnot bell190 bell191
cnot b0 bell191
measure bell191
cnot bell191 bell190
cnot bell190 a1
T* a1
cnot bell12 a1
T a1
cnot bell190 a1
H a1
T a3
cnot bell186 a3
T* a3
H bell192
cnot bell192 bell193
cnot b2 bell193
measure bell193
cnot bell193 bell192
cnot bell192 a3
T* a3
cnot bell186 a3
T a3
cnot bell192 a3
H a3
T a5
cnot bell180 a5
T* a5
cnot b4 a5
T* a5
cnot bell180 a5
T a5
cnot b4 a5
H a5
Z d3
cnot a3 d3
T* d3
H bell194
cnot bell194 bell195
cnot b3 bell195
measure bell195
cnot bell195 bell194
cnot bell194 d3
T* d3
cnot a3 d3
S d3
cnot bell192 d3
cnot a3 d3
cnot bell186 d3
T d3
cnot bell194 d3
T d3
cnot bell192 a3
H bell192
measure bell192
cz bell192 b2
cnot b4 a5
cnot bell180 a5
cnot a3 d3
cnot bell180 b4
H bell180
measure bell180
cz bell180 a4
cnot bell186 d3
H bell186
measure bell186
cz bell186 a2
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
cnot a2 bell199
measure bell199
cnot bell199 bell198
cnot bell198 a3
H bell198
measure bell198
cz bell198 a2
H d3
Z d5
H bell200
cnot bell200 bell201
cnot a5 bell201
measure bell201
cnot bell201 bell200
cnot bell200 d5
T d5
H bell202
cnot bell202 bell203
cnot b5 bell203
measure bell203
cnot bell203 bell202
cnot bell202 d5
T d5
cnot bell200 d5
S d5
H bell204
cnot bell204 bell205
cnot b4 bell205
measure bell205
cnot bell205 bell204
cnot bell204 d5
cnot bell200 d5
T* d5
cnot bell202 d5
T* d5
cnot bell204 d5
H bell204
measure bell204
cz bell204 b4
cnot bell200 d5
H bell200
measure bell200
cz bell200 a5
H d5
H bell206
cnot bell206 bell207
cnot a6 bell207
measure bell207
cnot bell207 bell206
cnot bell206 c5
S c5
H bell208
cnot bell208 bell209
cnot b6 bell209
measure bell209
cnot bell209 bell208
cnot bell208 c5
S c5
cnot bell206 c5
H bell206
measure bell206
cz bell206 a6
cnot bell208 c5
H bell208
measure bell208
cz bell208 b6
H c5
T* c3
Z c3
H bell210
cnot bell210 bell211
cnot a4 bell211
measure bell211
cnot bell211 bell210
cnot bell210 c3
S c3
H bell212
cnot bell212 bell213
cnot b4 bell213
measure bell213
cnot bell213 bell212
cnot bell212 c3
cnot bell210 c3
H bell210
measure bell210
cz bell210 a4
S c3
H bell214
cnot bell214 bell215
cnot c5 bell215
measure bell215
cnot bell215 bell214
cnot bell214 c3
cnot bell212 c3
H bell212
measure bell212
cz bell212 b4
T* c3
H bell216
cnot bell216 bell217
cnot d5 bell217
measure bell217
cnot bell217 bell216
cnot bell216 c3
T c3
cnot bell214 c3
H bell214
measure bell214
cz bell214 c5
T* c3
cnot bell216 c3
H bell216
measure bell216
cz bell216 d5
H c3
S c1
H bell218
cnot bell218 bell219
cnot a2 bell219
measure bell219
cnot bell219 bell218
cnot bell218 c1
S c1
H bell220
cnot bell220 bell221
cnot b2 bell221
measure bell221
cnot bell221 bell220
cnot bell220 c1
cnot bell218 c1
H bell218
measure bell218
cz bell218 a2
S c1
H bell222
cnot bell222 bell223
cnot c3 bell223
measure bell223
cnot bell223 bell222
cnot bell222 c1
cnot bell220 c1
H bell220
measure bell220
cz bell220 b2
T* c1
H bell224
cnot bell224 bell225
cnot d3 bell225
measure bell225
cnot bell225 bell224
cnot bell224 c1
T c1
cnot bell222 c1
H bell222
measure bell222
cz bell222 c3
T* c1
cnot bell224 c1
H bell224
measure bell224
cz bell224 d3
H c1
T d3
H bell226
cnot bell226 bell227
cnot c3 bell227
measure bell227
cnot bell227 bell226
cnot bell226 d3
T* d3
cnot bell226 d3
H bell226
measure bell226
cz bell226 c3
H d3
T d5
cnot c5 d5
T* d5
cnot c5 d5
H d5
T c1
H bell228
cnot bell228 bell229
cnot a1 bell229
measure bell229
cnot bell229 bell228
cnot bell228 c1
T* c1
H bell230
cnot bell230 bell231
cnot b1 bell231
measure bell231
cnot bell231 bell230
cnot bell230 c1
T* c1
cnot bell228 c1
H bell228
measure bell228
cz bell228 a1
T c1
H bell232
cnot bell232 bell233
cnot b2 bell233
measure bell233
cnot bell233 bell232
cnot bell232 a3
H bell232
measure bell232
cz bell232 b2
cnot b4 a5
cnot bell230 c1
H bell230
measure bell230
cz bell230 b1
H bell234
cnot bell234 bell235
cnot a4 bell235
measure bell235
cnot bell235 bell234
cnot bell234 b4
H bell234
measure bell234
cz bell234 a4
H bell236
cnot bell236 bell237
cnot a2 bell237
measure bell237
cnot bell237 bell236
cnot bell236 b2
H bell236
measure bell236
cz bell236 a2
H c1
S c3
H bell238
cnot bell238 bell239
cnot a3 bell239
measure bell239
cnot bell239 bell238
cnot bell238 c3
T* c3
cnot b3 c3
T* c3
cnot bell238 c3
H bell238
measure bell238
cz bell238 a3
T c3
cnot b3 c3
H c3
S d3
cnot a3 d3
T* d3
cnot bell194 d3
T* d3
cnot a3 d3
S d3
H bell240
cnot bell240 bell241
cnot b2 bell241
measure bell241
cnot bell241 bell240
cnot bell240 d3
cnot a3 d3
H bell242
cnot bell242 bell243
cnot a2 bell243
measure bell243
cnot bell243 bell242
cnot bell242 d3
T d3
cnot bell194 d3
T d3
cnot bell240 d3
cnot a3 d3
cnot bell242 d3
H d3
S c5
H bell244
cnot bell244 bell245
cnot a5 bell245
measure bell245
cnot bell245 bell244
cnot bell244 c5
T* c5
cnot bell202 c5
T* c5
cnot bell244 c5
T c5
cnot bell202 c5
H c5
S d5
cnot bell244 d5
T* d5
cnot bell202 d5
T* d5
cnot bell244 d5
S d5
H bell246
cnot bell246 bell247
cnot b4 bell247
measure bell247
cnot bell247 bell246
cnot bell246 d5
cnot bell244 d5
H bell248
cnot bell248 bell249
cnot a4 bell249
measure bell249
cnot bell249 bell248
cnot bell248 d5
T d5
cnot bell202 d5
H bell202
measure bell202
cz bell202 b5
T d5
cnot bell246 d5
H bell246
measure bell246
cz bell246 b4
cnot bell244 d5
H bell244
measure bell244
cz bell244 a5
cnot bell248 d5
H bell248
measure bell248
cz bell248 a4
H d5
T a1
cnot b1 a1
T a1
cnot b1 a1
H a1
T* a3
Z a3
cnot bell240 a3
cnot bell242 a3
S* a3
cnot bell194 a3
S* a3
cnot bell240 a3
cnot bell242 a3
T* a3
Z a3
cnot bell194 a3
H bell194
measure bell194
cz bell194 b3
H a3
T* a5
Z a5
cnot b4 a5
H bell250
cnot bell250 bell251
cnot a4 bell251
measure bell251
cnot bell251 bell250
cnot bell250 a5
S* a5
H bell252
cnot bell252 bell253
cnot b5 bell253
measure bell253
cnot bell253 bell252
cnot bell252 a5
S* a5
cnot b4 a5
cnot bell250 a5
T* a5
Z a5
cnot bell252 a5
H bell252
measure bell252
cz bell252 b5
H a5
T a1
cnot bell12 a1
T* a1
cnot bell190 a1
T* a1
cnot bell12 a1
H bell12
measure bell12
cz bell12 a0
T a1
cnot bell190 a1
H bell190
measure bell190
cz bell190 b0
H a1
T a3
cnot bell242 a3
T* a3
cnot bell240 a3
T* a3
cnot bell242 a3
H bell242
measure bell242
cz bell242 a2
T a3
cnot bell240 a3
H bell240
measure bell240
cz bell240 b2
H a3
T a5
cnot bell250 a5
T* a5
cnot b4 a5
T* a5
cnot bell250 a5
H bell250
measure bell250
cz bell250 a4
T a5
cnot b4 a5
H a5
S* a0
S b0
cnot a0 b0
S* b0
Z a2
S* b2
Z a4
S* b4
S a6
T* b1
T* b3
Z b3
T* b5
Z b5
H bell254
cnot bell254 bell255
cnot a6 bell255
measure bell255
cnot bell255 bell254
cnot bell254 b6
S* b6
cnot bell254 b6
H bell254
measure bell254
cz bell254 a6
H bell256
cnot bell256 bell257
cnot a5 bell257
measure bell257
cnot bell257 bell256
cnot bell256 c5
H bell256
measure bell256
cz bell256 a5
H bell258
cnot bell258 bell259
cnot a3 bell259
measure bell259
cnot bell259 bell258
cnot bell258 c3
H bell260
cnot bell260 bell261
cnot a5 bell261
measure bell261
cnot bell261 bell260
cnot bell260 b5
H bell260
measure bell260
cz bell260 a5
cnot bell258 b3
H bell258
measure bell258
cz bell258 a3
H bell262
cnot bell262 bell263
cnot a1 bell263
measure bell263
cnot bell263 bell262
cnot bell262 c1
H bell262
measure bell262
cz bell262 a1
cnot a1 b1
cnot a0 b0
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
END
