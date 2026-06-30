# Hyperedge cut (ebits): 59

# Actual ebits used (Synthesis): 144
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/ham15-med.qc):
#   Qubits: 17
#   H: 164
#   T: 574
#   cnot: 534
#   Depth: 667
#   T depth: 291
# Result (101.142ms):
#   Qubits: 305
#   H: 386
#   S: 33
#   T: 372
#   Z: 7
#   cnot: 883
#   cz: 144
#   measure: 288
#   reset: 288
#   swap: 1
#   Depth: 1148
#   T depth: 282


# Result Circuit
.v a b c d e f g h i j k l m n o 0 1 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell256 bell257 bell258 bell259 bell26 bell260 bell261 bell262 bell263 bell264 bell265 bell266 bell267 bell268 bell269 bell27 bell270 bell271 bell272 bell273 bell274 bell275 bell276 bell277 bell278 bell279 bell28 bell280 bell281 bell282 bell283 bell284 bell285 bell286 bell287 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a b c d e f g h i j k l m n o
.o a b c d e f g h i j k l m n o
BEGIN 
H bell0
cnot bell0 bell1
cnot o bell1
measure bell1
cnot bell1 bell0
cnot bell0 j
H bell0
measure bell0
cz bell0 o
H bell2
cnot bell2 bell3
cnot n bell3
measure bell3
cnot bell3 bell2
cnot bell2 o
H bell2
measure bell2
cz bell2 n
H 1
T 1
H bell4
cnot bell4 bell5
cnot l bell5
measure bell5
cnot bell5 bell4
cnot bell4 1
T* 1
H bell6
cnot bell6 bell7
cnot m bell7
measure bell7
cnot bell7 bell6
cnot bell6 1
T 1
cnot bell4 1
T* 1
cnot bell6 1
H 1
H 0
T 0
cnot 1 0
T* 0
H bell8
cnot bell8 bell9
cnot n bell9
measure bell9
cnot bell9 bell8
cnot bell8 0
T 0
cnot 1 0
T* 0
cnot bell8 0
H 0
H e
T e
H bell10
cnot bell10 bell11
cnot 0 bell11
measure bell11
cnot bell11 bell10
cnot bell10 e
T* e
H bell12
cnot bell12 bell13
cnot o bell13
measure bell13
cnot bell13 bell12
cnot bell12 e
T e
cnot bell10 e
H bell10
measure bell10
cz bell10 0
T* e
cnot bell12 e
H bell12
measure bell12
cz bell12 o
H e
T 0
H bell14
cnot bell14 bell15
cnot o bell15
measure bell15
cnot bell15 bell14
cnot bell14 0
T* 0
cnot bell14 0
H bell14
measure bell14
cz bell14 o
H 0
T 0
cnot 1 0
T* 0
cnot bell8 0
T 0
cnot 1 0
T* 0
cnot bell8 0
S 1
cnot bell8 1
S* 1
cnot bell8 1
H bell8
measure bell8
cz bell8 n
H 1
T 1
cnot bell4 1
T* 1
cnot bell6 1
T 1
cnot bell4 1
H bell4
measure bell4
cz bell4 l
T* 1
cnot bell6 1
H bell6
measure bell6
cz bell6 m
S l
H bell16
cnot bell16 bell17
cnot m bell17
measure bell17
cnot bell17 bell16
cnot bell16 l
S* l
T o
H bell18
cnot bell18 bell19
cnot o bell19
measure bell19
cnot bell19 bell18
cnot bell18 l
H bell18
measure bell18
cz bell18 o
cnot bell16 l
H bell16
measure bell16
cz bell16 m
H o
T o
H bell20
cnot bell20 bell21
cnot m bell21
measure bell21
cnot bell21 bell20
cnot bell20 o
T* o
H bell22
cnot bell22 bell23
cnot n bell23
measure bell23
cnot bell23 bell22
cnot bell22 o
T o
cnot bell20 o
H bell20
measure bell20
cz bell20 m
T* o
cnot bell22 o
H bell22
measure bell22
cz bell22 n
H o
T* n
Z n
H bell24
cnot bell24 bell25
cnot m bell25
measure bell25
cnot bell25 bell24
cnot bell24 n
T* n
cnot bell24 n
H bell24
measure bell24
cz bell24 m
H n
T n
H bell26
cnot bell26 bell27
cnot l bell27
measure bell27
cnot bell27 bell26
cnot bell26 n
T* n
H bell28
cnot bell28 bell29
cnot o bell29
measure bell29
cnot bell29 bell28
cnot bell28 n
T n
cnot bell26 n
H bell26
measure bell26
cz bell26 l
T* n
cnot bell28 n
H bell28
measure bell28
cz bell28 o
H n
T 1
H bell30
cnot bell30 bell31
cnot l bell31
measure bell31
cnot bell31 bell30
cnot bell30 1
T* 1
H bell32
cnot bell32 bell33
cnot m bell33
measure bell33
cnot bell33 bell32
cnot bell32 1
T 1
cnot bell30 1
T* 1
cnot bell32 1
H 1
T 0
cnot 1 0
T* 0
H bell34
cnot bell34 bell35
cnot n bell35
measure bell35
cnot bell35 bell34
cnot bell34 0
T 0
cnot 1 0
T* 0
cnot bell34 0
H 0
H b
T b
H bell36
cnot bell36 bell37
cnot 0 bell37
measure bell37
cnot bell37 bell36
cnot bell36 b
T* b
H bell38
cnot bell38 bell39
cnot o bell39
measure bell39
cnot bell39 bell38
cnot bell38 b
T b
cnot bell36 b
H bell36
measure bell36
cz bell36 0
T* b
cnot bell38 b
H bell38
measure bell38
cz bell38 o
H b
T 0
H bell40
cnot bell40 bell41
cnot o bell41
measure bell41
cnot bell41 bell40
cnot bell40 0
T* 0
cnot bell40 0
H bell40
measure bell40
cz bell40 o
H 0
T 0
cnot 1 0
T* 0
cnot bell34 0
T 0
cnot 1 0
T* 0
cnot bell34 0
S 1
cnot bell34 1
S* 1
cnot bell34 1
H bell34
measure bell34
cz bell34 n
H 1
T 1
cnot bell30 1
T* 1
cnot bell32 1
T 1
cnot bell30 1
T* 1
cnot bell32 1
H bell42
cnot bell42 bell43
cnot o bell43
measure bell43
cnot bell43 bell42
cnot bell42 k
H bell42
measure bell42
cz bell42 o
T 0
cnot bell30 0
T* 0
cnot bell32 0
T 0
cnot bell30 0
H bell30
measure bell30
cz bell30 l
T* 0
cnot bell32 0
H 0
S o
H bell44
cnot bell44 bell45
cnot l bell45
measure bell45
cnot bell45 bell44
cnot bell44 o
T* o
cnot bell44 o
H bell44
measure bell44
cz bell44 l
H o
T o
H bell46
cnot bell46 bell47
cnot 0 bell47
measure bell47
cnot bell47 bell46
cnot bell46 o
T* o
H bell48
cnot bell48 bell49
cnot n bell49
measure bell49
cnot bell49 bell48
cnot bell48 o
T o
cnot bell46 o
H bell46
measure bell46
cz bell46 0
T* o
cnot bell48 o
H bell48
measure bell48
cz bell48 n
H o
T 0
H bell50
cnot bell50 bell51
cnot n bell51
measure bell51
cnot bell51 bell50
cnot bell50 0
T* 0
cnot bell50 0
H 0
T 0
H bell52
cnot bell52 bell53
cnot l bell53
measure bell53
cnot bell53 bell52
cnot bell52 0
T* 0
cnot bell32 0
T 0
cnot bell52 0
H bell52
measure bell52
cz bell52 l
T* 0
cnot bell32 0
H j
T j
H bell54
cnot bell54 bell55
cnot l bell55
measure bell55
cnot bell55 bell54
cnot bell54 j
T* j
H bell56
cnot bell56 bell57
cnot o bell57
measure bell57
cnot bell57 bell56
cnot bell56 j
T j
cnot bell54 j
H bell54
measure bell54
cz bell54 l
T* j
cnot bell56 j
H bell56
measure bell56
cz bell56 o
T 1
H bell58
cnot bell58 bell59
cnot l bell59
measure bell59
cnot bell59 bell58
cnot bell58 1
T* 1
cnot bell32 1
T 1
cnot bell58 1
T* 1
cnot bell32 1
H 1
T 0
cnot 1 0
T* 0
cnot bell50 0
T 0
cnot 1 0
T* 0
cnot bell50 0
H 0
H f
T f
H bell60
cnot bell60 bell61
cnot 0 bell61
measure bell61
cnot bell61 bell60
cnot bell60 f
T* f
H bell62
cnot bell62 bell63
cnot o bell63
measure bell63
cnot bell63 bell62
cnot bell62 f
T f
cnot bell60 f
H bell60
measure bell60
cz bell60 0
T* f
cnot bell62 f
H bell62
measure bell62
cz bell62 o
H f
T 0
H bell64
cnot bell64 bell65
cnot o bell65
measure bell65
cnot bell65 bell64
cnot bell64 0
T* 0
cnot bell64 0
H bell64
measure bell64
cz bell64 o
H 0
T 0
cnot 1 0
T* 0
cnot bell50 0
T 0
cnot 1 0
T* 0
cnot bell50 0
S 1
cnot bell50 1
S* 1
cnot bell50 1
H bell50
measure bell50
cz bell50 n
H 1
T 1
cnot bell58 1
T* 1
cnot bell32 1
T 1
cnot bell58 1
T* 1
cnot bell32 1
H bell32
measure bell32
cz bell32 m
H a
T a
H bell66
cnot bell66 bell67
cnot m bell67
measure bell67
cnot bell67 bell66
cnot bell66 a
T* a
H bell68
cnot bell68 bell69
cnot o bell69
measure bell69
cnot bell69 bell68
cnot bell68 a
T a
cnot bell66 a
H bell66
measure bell66
cz bell66 m
T* a
cnot bell68 a
T a
H bell70
cnot bell70 bell71
cnot n bell71
measure bell71
cnot bell71 bell70
cnot bell70 a
T* a
cnot bell68 a
T a
cnot bell70 a
H bell70
measure bell70
cz bell70 n
T* a
cnot bell68 a
T 1
cnot bell58 1
T* 1
H bell72
cnot bell72 bell73
cnot m bell73
measure bell73
cnot bell73 bell72
cnot bell72 1
T 1
cnot bell58 1
T* 1
cnot bell72 1
H 1
T 0
cnot 1 0
T* 0
H bell74
cnot bell74 bell75
cnot n bell75
measure bell75
cnot bell75 bell74
cnot bell74 0
T 0
cnot 1 0
T* 0
cnot bell74 0
H 0
T a
H bell76
cnot bell76 bell77
cnot 0 bell77
measure bell77
cnot bell77 bell76
cnot bell76 a
T* a
cnot bell68 a
T a
cnot bell76 a
H bell76
measure bell76
cz bell76 0
T* a
cnot bell68 a
H bell68
measure bell68
cz bell68 o
T 0
H bell78
cnot bell78 bell79
cnot o bell79
measure bell79
cnot bell79 bell78
cnot bell78 0
T* 0
cnot bell78 0
H bell78
measure bell78
cz bell78 o
H 0
T 0
cnot 1 0
T* 0
cnot bell74 0
T 0
cnot 1 0
T* 0
cnot bell74 0
S 1
cnot bell74 1
S* 1
cnot bell74 1
H 1
T 1
cnot bell58 1
T* 1
cnot bell72 1
T 1
cnot bell58 1
T* 1
cnot bell72 1
H bell72
measure bell72
cz bell72 m
H bell80
cnot bell80 bell81
cnot o bell81
measure bell81
cnot bell81 bell80
cnot bell80 m
H bell80
measure bell80
cz bell80 o
T 1
cnot bell58 1
T* 1
H bell82
cnot bell82 bell83
cnot m bell83
measure bell83
cnot bell83 bell82
cnot bell82 1
T 1
cnot bell58 1
T* 1
cnot bell82 1
H 1
T 0
cnot 1 0
T* 0
cnot bell74 0
T 0
cnot 1 0
T* 0
cnot bell74 0
H 0
H d
T d
H bell84
cnot bell84 bell85
cnot 0 bell85
measure bell85
cnot bell85 bell84
cnot bell84 d
T* d
H bell86
cnot bell86 bell87
cnot o bell87
measure bell87
cnot bell87 bell86
cnot bell86 d
T d
cnot bell84 d
H bell84
measure bell84
cz bell84 0
T* d
cnot bell86 d
H bell86
measure bell86
cz bell86 o
H d
T 0
H bell88
cnot bell88 bell89
cnot o bell89
measure bell89
cnot bell89 bell88
cnot bell88 0
T* 0
cnot bell88 0
H bell88
measure bell88
cz bell88 o
H 0
T 0
cnot 1 0
T* 0
cnot bell74 0
T 0
cnot 1 0
T* 0
cnot bell74 0
S 1
cnot bell74 1
S* 1
cnot bell74 1
H 1
T 1
cnot bell58 1
T* 1
cnot bell82 1
T 1
cnot bell58 1
T* 1
cnot bell82 1
H bell82
measure bell82
cz bell82 m
T j
H bell90
cnot bell90 bell91
cnot m bell91
measure bell91
cnot bell91 bell90
cnot bell90 j
T* j
H bell92
cnot bell92 bell93
cnot o bell93
measure bell93
cnot bell93 bell92
cnot bell92 j
T j
cnot bell90 j
H bell90
measure bell90
cz bell90 m
T* j
cnot bell92 j
H bell92
measure bell92
cz bell92 o
H c
T c
H bell94
cnot bell94 bell95
cnot m bell95
measure bell95
cnot bell95 bell94
cnot bell94 c
T* c
H bell96
cnot bell96 bell97
cnot o bell97
measure bell97
cnot bell97 bell96
cnot bell96 c
T c
cnot bell94 c
H bell94
measure bell94
cz bell94 m
T* c
cnot bell96 c
T 1
cnot bell58 1
T* 1
H bell98
cnot bell98 bell99
cnot m bell99
measure bell99
cnot bell99 bell98
cnot bell98 1
T 1
cnot bell58 1
T* 1
cnot bell98 1
H 1
T 0
cnot 1 0
T* 0
cnot bell74 0
T 0
cnot 1 0
T* 0
cnot bell74 0
H 0
T c
H bell100
cnot bell100 bell101
cnot 0 bell101
measure bell101
cnot bell101 bell100
cnot bell100 c
T* c
cnot bell96 c
T c
cnot bell100 c
H bell100
measure bell100
cz bell100 0
T* c
cnot bell96 c
H bell96
measure bell96
cz bell96 o
T 0
H bell102
cnot bell102 bell103
cnot o bell103
measure bell103
cnot bell103 bell102
cnot bell102 0
T* 0
cnot bell102 0
H bell102
measure bell102
cz bell102 o
H 0
T 0
cnot 1 0
T* 0
cnot bell74 0
T 0
cnot 1 0
T* 0
cnot bell74 0
S 1
cnot bell74 1
S* 1
cnot bell74 1
H bell74
measure bell74
cz bell74 n
H 1
T 1
cnot bell58 1
T* 1
cnot bell98 1
T 1
cnot bell58 1
T* 1
cnot bell98 1
T 0
cnot bell58 0
T* 0
cnot bell98 0
T 0
cnot bell58 0
T* 0
cnot bell98 0
H 0
Z n
H bell104
cnot bell104 bell105
cnot o bell105
measure bell105
cnot bell105 bell104
cnot bell104 n
T* n
cnot bell104 n
H n
T n
H bell106
cnot bell106 bell107
cnot 0 bell107
measure bell107
cnot bell107 bell106
cnot bell106 n
T* n
cnot bell104 n
T n
cnot bell106 n
H bell106
measure bell106
cz bell106 0
T* n
cnot bell104 n
H bell104
measure bell104
cz bell104 o
H n
T 0
H bell108
cnot bell108 bell109
cnot o bell109
measure bell109
cnot bell109 bell108
cnot bell108 0
T* 0
cnot bell108 0
H bell108
measure bell108
cz bell108 o
H 0
T 0
cnot bell58 0
T* 0
cnot bell98 0
T 0
cnot bell58 0
H bell58
measure bell58
cz bell58 l
T* 0
cnot bell98 0
T 0
cnot bell98 0
T* 0
H bell110
cnot bell110 bell111
cnot n bell111
measure bell111
cnot bell111 bell110
cnot bell110 0
T 0
cnot bell98 0
T* 0
cnot bell110 0
H 0
T c
H bell112
cnot bell112 bell113
cnot 0 bell113
measure bell113
cnot bell113 bell112
cnot bell112 c
T* c
H bell114
cnot bell114 bell115
cnot o bell115
measure bell115
cnot bell115 bell114
cnot bell114 c
T c
cnot bell112 c
H bell112
measure bell112
cz bell112 0
T* c
cnot bell114 c
H bell114
measure bell114
cz bell114 o
H c
T 0
H bell116
cnot bell116 bell117
cnot o bell117
measure bell117
cnot bell117 bell116
cnot bell116 0
T* 0
cnot bell116 0
H bell116
measure bell116
cz bell116 o
H 0
T 0
cnot bell98 0
T* 0
cnot bell110 0
T 0
cnot bell98 0
T* 0
cnot bell110 0
T 0
cnot bell98 0
T* 0
cnot bell110 0
T 0
cnot bell98 0
H bell98
measure bell98
cz bell98 m
T* 0
cnot bell110 0
H 0
H bell118
cnot bell118 bell119
cnot m bell119
measure bell119
cnot bell119 bell118
cnot bell118 l
S l
H bell120
cnot bell120 bell121
cnot o bell121
measure bell121
cnot bell121 bell120
cnot bell120 l
cnot bell118 l
H bell118
measure bell118
cz bell118 m
T* l
cnot bell120 l
H l
T l
H bell122
cnot bell122 bell123
cnot 0 bell123
measure bell123
cnot bell123 bell122
cnot bell122 l
T* l
cnot bell120 l
T l
cnot bell122 l
H bell122
measure bell122
cz bell122 0
T* l
cnot bell120 l
H bell120
measure bell120
cz bell120 o
H l
T 0
H bell124
cnot bell124 bell125
cnot o bell125
measure bell125
cnot bell125 bell124
cnot bell124 0
T* 0
cnot bell124 0
H bell124
measure bell124
cz bell124 o
H 0
T 0
H bell126
cnot bell126 bell127
cnot m bell127
measure bell127
cnot bell127 bell126
cnot bell126 0
T* 0
cnot bell110 0
T 0
cnot bell126 0
T* 0
cnot bell110 0
T a
H bell128
cnot bell128 bell129
cnot l bell129
measure bell129
cnot bell129 bell128
cnot bell128 a
T* a
H bell130
cnot bell130 bell131
cnot o bell131
measure bell131
cnot bell131 bell130
cnot bell130 a
T a
cnot bell128 a
H bell128
measure bell128
cz bell128 l
T* a
cnot bell130 a
H bell130
measure bell130
cz bell130 o
H a
T 1
H bell132
cnot bell132 bell133
cnot l bell133
measure bell133
cnot bell133 bell132
cnot bell132 1
T* 1
cnot bell126 1
T 1
cnot bell132 1
T* 1
cnot bell126 1
H 1
T 0
cnot 1 0
T* 0
cnot bell110 0
T 0
cnot 1 0
T* 0
cnot bell110 0
H 0
H g
T g
H bell134
cnot bell134 bell135
cnot 0 bell135
measure bell135
cnot bell135 bell134
cnot bell134 g
T* g
H bell136
cnot bell136 bell137
cnot o bell137
measure bell137
cnot bell137 bell136
cnot bell136 g
T g
cnot bell134 g
H bell134
measure bell134
cz bell134 0
T* g
cnot bell136 g
H bell136
measure bell136
cz bell136 o
H g
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
T 0
cnot 1 0
T* 0
cnot bell110 0
T 0
cnot 1 0
T* 0
cnot bell110 0
S 1
cnot bell110 1
S* 1
cnot bell110 1
H bell110
measure bell110
cz bell110 n
H 1
T 1
cnot bell132 1
T* 1
cnot bell126 1
T 1
cnot bell132 1
H bell132
measure bell132
cz bell132 l
T* 1
cnot bell126 1
H bell126
measure bell126
cz bell126 m
S* n
H bell140
cnot bell140 bell141
cnot m bell141
measure bell141
cnot bell141 bell140
cnot bell140 n
Z n
cnot bell140 n
H bell140
measure bell140
cz bell140 m
H n
T n
H bell142
cnot bell142 bell143
cnot l bell143
measure bell143
cnot bell143 bell142
cnot bell142 n
T* n
H bell144
cnot bell144 bell145
cnot o bell145
measure bell145
cnot bell145 bell144
cnot bell144 n
T n
cnot bell142 n
H bell142
measure bell142
cz bell142 l
T* n
cnot bell144 n
H bell144
measure bell144
cz bell144 o
H n
Z l
H bell146
cnot bell146 bell147
cnot m bell147
measure bell147
cnot bell147 bell146
cnot bell146 l
S* l
H bell148
cnot bell148 bell149
cnot o bell149
measure bell149
cnot bell149 bell148
cnot bell148 l
cnot bell146 l
H bell146
measure bell146
cz bell146 m
S* l
cnot bell148 l
H l
T l
H bell150
cnot bell150 bell151
cnot n bell151
measure bell151
cnot bell151 bell150
cnot bell150 l
T* l
cnot bell148 l
T l
cnot bell150 l
H bell150
measure bell150
cz bell150 n
T* l
cnot bell148 l
H bell148
measure bell148
cz bell148 o
H l
T 1
H bell152
cnot bell152 bell153
cnot l bell153
measure bell153
cnot bell153 bell152
cnot bell152 1
T* 1
H bell154
cnot bell154 bell155
cnot m bell155
measure bell155
cnot bell155 bell154
cnot bell154 1
T 1
cnot bell152 1
T* 1
cnot bell154 1
H 1
T 0
cnot 1 0
T* 0
H bell156
cnot bell156 bell157
cnot n bell157
measure bell157
cnot bell157 bell156
cnot bell156 0
T 0
cnot 1 0
T* 0
cnot bell156 0
H 0
H h
T h
H bell158
cnot bell158 bell159
cnot 0 bell159
measure bell159
cnot bell159 bell158
cnot bell158 h
T* h
H bell160
cnot bell160 bell161
cnot o bell161
measure bell161
cnot bell161 bell160
cnot bell160 h
T h
cnot bell158 h
H bell158
measure bell158
cz bell158 0
T* h
cnot bell160 h
H bell160
measure bell160
cz bell160 o
H h
T 0
H bell162
cnot bell162 bell163
cnot o bell163
measure bell163
cnot bell163 bell162
cnot bell162 0
T* 0
cnot bell162 0
H bell162
measure bell162
cz bell162 o
H 0
T 0
cnot 1 0
T* 0
cnot bell156 0
T 0
cnot 1 0
T* 0
cnot bell156 0
S 1
cnot bell156 1
S* 1
cnot bell156 1
H 1
T 1
cnot bell152 1
T* 1
cnot bell154 1
T 1
cnot bell152 1
T* 1
cnot bell154 1
H bell154
measure bell154
cz bell154 m
T 0
cnot bell152 0
T* 0
cnot bell156 0
T 0
cnot bell152 0
H bell152
measure bell152
cz bell152 l
T* 0
cnot bell156 0
H 0
T* m
H bell164
cnot bell164 bell165
cnot l bell165
measure bell165
cnot bell165 bell164
cnot bell164 m
S* m
H bell166
cnot bell166 bell167
cnot o bell167
measure bell167
cnot bell167 bell166
cnot bell166 m
cnot bell164 m
H bell164
measure bell164
cz bell164 l
S m
cnot bell166 m
H m
T m
H bell168
cnot bell168 bell169
cnot 0 bell169
measure bell169
cnot bell169 bell168
cnot bell168 m
T* m
cnot bell166 m
T m
cnot bell168 m
H bell168
measure bell168
cz bell168 0
T* m
cnot bell166 m
H bell166
measure bell166
cz bell166 o
H m
T 0
H bell170
cnot bell170 bell171
cnot o bell171
measure bell171
cnot bell171 bell170
cnot bell170 0
T* 0
cnot bell170 0
H bell170
measure bell170
cz bell170 o
H 0
T 0
H bell172
cnot bell172 bell173
cnot l bell173
measure bell173
cnot bell173 bell172
cnot bell172 0
T* 0
cnot bell156 0
T 0
cnot bell172 0
T* 0
cnot bell156 0
T 1
cnot bell172 1
T* 1
H bell174
cnot bell174 bell175
cnot m bell175
measure bell175
cnot bell175 bell174
cnot bell174 1
T 1
cnot bell172 1
T* 1
cnot bell174 1
H 1
T 0
cnot 1 0
T* 0
cnot bell156 0
T 0
cnot 1 0
T* 0
cnot bell156 0
H 0
T j
H bell176
cnot bell176 bell177
cnot 0 bell177
measure bell177
cnot bell177 bell176
cnot bell176 j
T* j
H bell178
cnot bell178 bell179
cnot o bell179
measure bell179
cnot bell179 bell178
cnot bell178 j
T j
cnot bell176 j
H bell176
measure bell176
cz bell176 0
T* j
cnot bell178 j
H bell178
measure bell178
cz bell178 o
H j
T 0
H bell180
cnot bell180 bell181
cnot o bell181
measure bell181
cnot bell181 bell180
cnot bell180 0
T* 0
cnot bell180 0
H bell180
measure bell180
cz bell180 o
H 0
T 0
cnot 1 0
T* 0
cnot bell156 0
T 0
cnot 1 0
T* 0
cnot bell156 0
S 1
cnot bell156 1
S* 1
cnot bell156 1
H 1
T 1
cnot bell172 1
T* 1
cnot bell174 1
T 1
cnot bell172 1
T* 1
cnot bell174 1
T 1
cnot bell172 1
T* 1
cnot bell174 1
T 1
cnot bell172 1
T* 1
cnot bell174 1
H 1
T 0
cnot 1 0
T* 0
cnot bell156 0
T 0
cnot 1 0
T* 0
cnot bell156 0
H 0
H k
T k
H bell182
cnot bell182 bell183
cnot 0 bell183
measure bell183
cnot bell183 bell182
cnot bell182 k
T* k
H bell184
cnot bell184 bell185
cnot o bell185
measure bell185
cnot bell185 bell184
cnot bell184 k
T k
cnot bell182 k
H bell182
measure bell182
cz bell182 0
T* k
cnot bell184 k
H bell184
measure bell184
cz bell184 o
T 0
H bell186
cnot bell186 bell187
cnot o bell187
measure bell187
cnot bell187 bell186
cnot bell186 0
T* 0
cnot bell186 0
H bell186
measure bell186
cz bell186 o
H 0
T 0
cnot 1 0
T* 0
cnot bell156 0
T 0
cnot 1 0
T* 0
cnot bell156 0
S 1
cnot bell156 1
S* 1
cnot bell156 1
H bell156
measure bell156
cz bell156 n
H 1
T 1
cnot bell172 1
T* 1
cnot bell174 1
T 1
cnot bell172 1
H bell172
measure bell172
cz bell172 l
T* 1
cnot bell174 1
H bell174
measure bell174
cz bell174 m
Z o
H bell188
cnot bell188 bell189
cnot n bell189
measure bell189
cnot bell189 bell188
cnot bell188 o
T* o
cnot bell188 o
H bell188
measure bell188
cz bell188 n
H o
T o
H bell190
cnot bell190 bell191
cnot l bell191
measure bell191
cnot bell191 bell190
cnot bell190 o
T* o
H bell192
cnot bell192 bell193
cnot m bell193
measure bell193
cnot bell193 bell192
cnot bell192 o
T o
cnot bell190 o
H bell190
measure bell190
cz bell190 l
T* o
cnot bell192 o
H bell192
measure bell192
cz bell192 m
H o
T k
H bell194
cnot bell194 bell195
cnot l bell195
measure bell195
cnot bell195 bell194
cnot bell194 k
T* k
H bell196
cnot bell196 bell197
cnot n bell197
measure bell197
cnot bell197 bell196
cnot bell196 k
T k
cnot bell194 k
H bell194
measure bell194
cz bell194 l
T* k
cnot bell196 k
H bell196
measure bell196
cz bell196 n
H k
H bell198
cnot bell198 bell199
cnot o bell199
measure bell199
cnot bell199 bell198
cnot bell198 n
H bell198
measure bell198
cz bell198 o
T 1
H bell200
cnot bell200 bell201
cnot l bell201
measure bell201
cnot bell201 bell200
cnot bell200 1
T* 1
H bell202
cnot bell202 bell203
cnot m bell203
measure bell203
cnot bell203 bell202
cnot bell202 1
T 1
cnot bell200 1
T* 1
cnot bell202 1
H 1
T 0
cnot 1 0
T* 0
H bell204
cnot bell204 bell205
cnot n bell205
measure bell205
cnot bell205 bell204
cnot bell204 0
T 0
cnot 1 0
T* 0
cnot bell204 0
H 0
H i
T i
H bell206
cnot bell206 bell207
cnot 0 bell207
measure bell207
cnot bell207 bell206
cnot bell206 i
T* i
H bell208
cnot bell208 bell209
cnot o bell209
measure bell209
cnot bell209 bell208
cnot bell208 i
T i
cnot bell206 i
H bell206
measure bell206
cz bell206 0
T* i
cnot bell208 i
H bell208
measure bell208
cz bell208 o
H i
T 0
H bell210
cnot bell210 bell211
cnot o bell211
measure bell211
cnot bell211 bell210
cnot bell210 0
T* 0
cnot bell210 0
H bell210
measure bell210
cz bell210 o
H 0
T 0
cnot 1 0
T* 0
cnot bell204 0
T 0
cnot 1 0
T* 0
cnot bell204 0
H 0
S 1
cnot bell204 1
S* 1
cnot bell204 1
H bell204
measure bell204
cz bell204 n
H 1
T 1
cnot bell200 1
T* 1
cnot bell202 1
T 1
cnot bell200 1
H bell200
measure bell200
cz bell200 l
T* 1
cnot bell202 1
H bell202
measure bell202
cz bell202 m
H 1
Z l
S n
T o
H bell212
cnot bell212 bell213
cnot n bell213
measure bell213
cnot bell213 bell212
cnot bell212 o
S o
H bell214
cnot bell214 bell215
cnot l bell215
measure bell215
cnot bell215 bell214
cnot bell214 o
H bell214
measure bell214
cz bell214 l
T o
Z o
T* m
H bell216
cnot bell216 bell217
cnot l bell217
measure bell217
cnot bell217 bell216
cnot bell216 m
H bell216
measure bell216
cz bell216 l
T m
H bell218
cnot bell218 bell219
cnot k bell219
measure bell219
cnot bell219 bell218
cnot bell218 j
H bell218
measure bell218
cz bell218 k
H bell220
cnot bell220 bell221
cnot o bell221
measure bell221
cnot bell221 bell220
cnot bell220 l
H bell220
measure bell220
cz bell220 o
cnot bell212 o
H bell212
measure bell212
cz bell212 n
H bell222
cnot bell222 bell223
cnot o bell223
measure bell223
cnot bell223 bell222
cnot bell222 m
H bell222
measure bell222
cz bell222 o
swap m n
H bell224
cnot bell224 bell225
cnot l bell225
measure bell225
cnot bell225 bell224
cnot bell224 n
H bell224
measure bell224
cz bell224 l
H bell226
cnot bell226 bell227
cnot k bell227
measure bell227
cnot bell227 bell226
cnot bell226 n
H bell226
measure bell226
cz bell226 k
H bell228
cnot bell228 bell229
cnot k bell229
measure bell229
cnot bell229 bell228
cnot bell228 o
H bell228
measure bell228
cz bell228 k
H bell230
cnot bell230 bell231
cnot j bell231
measure bell231
cnot bell231 bell230
cnot bell230 m
H bell230
measure bell230
cz bell230 j
H bell232
cnot bell232 bell233
cnot m bell233
measure bell233
cnot bell233 bell232
cnot bell232 i
H bell232
measure bell232
cz bell232 m
H bell234
cnot bell234 bell235
cnot i bell235
measure bell235
cnot bell235 bell234
cnot bell234 m
H bell234
measure bell234
cz bell234 i
H bell236
cnot bell236 bell237
cnot i bell237
measure bell237
cnot bell237 bell236
cnot bell236 l
H bell236
measure bell236
cz bell236 i
H bell238
cnot bell238 bell239
cnot l bell239
measure bell239
cnot bell239 bell238
cnot bell238 h
H bell238
measure bell238
cz bell238 l
H bell240
cnot bell240 bell241
cnot h bell241
measure bell241
cnot bell241 bell240
cnot bell240 l
H bell240
measure bell240
cz bell240 h
H bell242
cnot bell242 bell243
cnot j bell243
measure bell243
cnot bell243 bell242
cnot bell242 n
H bell242
measure bell242
cz bell242 j
H bell244
cnot bell244 bell245
cnot h bell245
measure bell245
cnot bell245 bell244
cnot bell244 k
H bell244
measure bell244
cz bell244 h
H bell246
cnot bell246 bell247
cnot k bell247
measure bell247
cnot bell247 bell246
cnot bell246 g
H bell246
measure bell246
cz bell246 k
H bell248
cnot bell248 bell249
cnot g bell249
measure bell249
cnot bell249 bell248
cnot bell248 j
H bell248
measure bell248
cz bell248 g
H bell250
cnot bell250 bell251
cnot j bell251
measure bell251
cnot bell251 bell250
cnot bell250 f
H bell250
measure bell250
cz bell250 j
H bell252
cnot bell252 bell253
cnot f bell253
measure bell253
cnot bell253 bell252
cnot bell252 j
H bell252
measure bell252
cz bell252 f
H bell254
cnot bell254 bell255
cnot f bell255
measure bell255
cnot bell255 bell254
cnot bell254 i
H bell254
measure bell254
cz bell254 f
H bell256
cnot bell256 bell257
cnot i bell257
measure bell257
cnot bell257 bell256
cnot bell256 e
H bell256
measure bell256
cz bell256 i
H bell258
cnot bell258 bell259
cnot e bell259
measure bell259
cnot bell259 bell258
cnot bell258 i
H bell258
measure bell258
cz bell258 e
H bell260
cnot bell260 bell261
cnot g bell261
measure bell261
cnot bell261 bell260
cnot bell260 k
H bell260
measure bell260
cz bell260 g
H bell262
cnot bell262 bell263
cnot e bell263
measure bell263
cnot bell263 bell262
cnot bell262 h
H bell262
measure bell262
cz bell262 e
H bell264
cnot bell264 bell265
cnot h bell265
measure bell265
cnot bell265 bell264
cnot bell264 d
H bell264
measure bell264
cz bell264 h
H bell266
cnot bell266 bell267
cnot d bell267
measure bell267
cnot bell267 bell266
cnot bell266 g
H bell266
measure bell266
cz bell266 d
H bell268
cnot bell268 bell269
cnot g bell269
measure bell269
cnot bell269 bell268
cnot bell268 c
H bell268
measure bell268
cz bell268 g
H bell270
cnot bell270 bell271
cnot c bell271
measure bell271
cnot bell271 bell270
cnot bell270 g
H bell270
measure bell270
cz bell270 c
H bell272
cnot bell272 bell273
cnot c bell273
measure bell273
cnot bell273 bell272
cnot bell272 f
H bell272
measure bell272
cz bell272 c
H bell274
cnot bell274 bell275
cnot f bell275
measure bell275
cnot bell275 bell274
cnot bell274 b
H bell274
measure bell274
cz bell274 f
H bell276
cnot bell276 bell277
cnot b bell277
measure bell277
cnot bell277 bell276
cnot bell276 f
H bell276
measure bell276
cz bell276 b
H bell278
cnot bell278 bell279
cnot d bell279
measure bell279
cnot bell279 bell278
cnot bell278 h
H bell278
measure bell278
cz bell278 d
H bell280
cnot bell280 bell281
cnot b bell281
measure bell281
cnot bell281 bell280
cnot bell280 e
H bell280
measure bell280
cz bell280 b
H bell282
cnot bell282 bell283
cnot e bell283
measure bell283
cnot bell283 bell282
cnot bell282 a
H bell282
measure bell282
cz bell282 e
H bell284
cnot bell284 bell285
cnot a bell285
measure bell285
cnot bell285 bell284
cnot bell284 e
H bell284
measure bell284
cz bell284 a
H bell286
cnot bell286 bell287
cnot a bell287
measure bell287
cnot bell287 bell286
cnot bell286 d
H bell286
measure bell286
cz bell286 a
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
END
