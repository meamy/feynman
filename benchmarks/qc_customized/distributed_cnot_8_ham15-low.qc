# Hyperedge cut (ebits): 51

# Actual ebits used (Synthesis): 91
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/ham15-low.qc):
#   Qubits: 17
#   H: 46
#   T: 161
#   cnot: 236
#   Depth: 238
#   T depth: 85
# Result (51.512ms):
#   Qubits: 199
#   H: 220
#   S: 3
#   T: 113
#   cnot: 494
#   cz: 92
#   measure: 182
#   reset: 183
#   swap: 1
#   Depth: 480
#   T depth: 91


# Result Circuit
.v a b c d e f g h i j k l m n o 0 1 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
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
cnot k g
H bell4
cnot bell4 bell5
cnot h bell5
measure bell5
cnot bell5 bell4
H bell6
cnot bell6 bell7
cnot k bell7
measure bell7
cnot bell7 bell6
cnot bell6 bell4
H bell6
measure bell6
cz bell6 k
H bell8
cnot bell8 bell9
cnot m bell9
measure bell9
cnot bell9 bell8
cnot bell8 i
cnot m n
cnot n l
cnot l n
cnot i bell4
H bell10
cnot bell10 bell11
cnot bell4 bell11
measure bell11
cnot bell11 bell10
reset bell11
cnot h bell10
cnot bell10 h
H bell10
measure bell10
cz bell10 i
cz bell10 k
H bell4
measure bell4
cz bell4 h
cnot i e
H i
T i
H bell12
cnot bell12 bell13
cnot l bell13
measure bell13
cnot bell13 bell12
cnot bell12 i
T* i
cnot bell8 i
T i
cnot bell12 i
H bell12
measure bell12
cz bell12 l
T* i
cnot bell8 i
H bell8
measure bell8
cz bell8 m
H i
T m
cnot l m
T* m
H bell14
cnot bell14 bell15
cnot o bell15
measure bell15
cnot bell15 bell14
cnot bell14 a
H bell14
measure bell14
cz bell14 o
cnot i e
H bell16
cnot bell16 bell17
cnot o bell17
measure bell17
cnot bell17 bell16
cnot bell16 g
H bell16
measure bell16
cz bell16 o
H bell18
cnot bell18 bell19
cnot i bell19
measure bell19
cnot bell19 bell18
cnot bell18 h
H bell18
measure bell18
cz bell18 i
H bell20
cnot bell20 bell21
cnot o bell21
measure bell21
cnot bell21 bell20
cnot bell20 i
H bell20
measure bell20
cz bell20 o
H bell22
cnot bell22 bell23
cnot o bell23
measure bell23
cnot bell23 bell22
cnot bell22 n
cnot l m
H bell24
cnot bell24 bell25
cnot m bell25
measure bell25
cnot bell25 bell24
cnot bell24 d
H bell24
measure bell24
cz bell24 m
H m
T m
cnot n m
T* m
cnot bell22 m
T m
cnot n m
T* m
cnot bell22 m
H bell22
measure bell22
cz bell22 o
H m
T o
H bell26
cnot bell26 bell27
cnot n bell27
measure bell27
cnot bell27 bell26
cnot bell26 o
T* o
H bell28
cnot bell28 bell29
cnot m bell29
measure bell29
cnot bell29 bell28
cnot bell28 d
H bell28
measure bell28
cz bell28 m
cnot bell26 o
H bell26
measure bell26
cz bell26 n
cnot m n
H o
T o
H bell30
cnot bell30 bell31
cnot m bell31
measure bell31
cnot bell31 bell30
cnot bell30 o
T* o
H bell32
cnot bell32 bell33
cnot n bell33
measure bell33
cnot bell33 bell32
cnot bell32 o
T o
cnot bell30 o
H bell30
measure bell30
cz bell30 m
T* o
cnot bell32 o
H o
T m
H bell34
cnot bell34 bell35
cnot m bell35
measure bell35
cnot bell35 bell34
cnot bell34 k
H bell34
measure bell34
cz bell34 m
swap 0 1
H m
T m
cnot n m
T* m
H bell36
cnot bell36 bell37
cnot o bell37
measure bell37
cnot bell37 bell36
cnot bell36 m
T m
cnot n m
T* m
cnot bell36 m
H bell36
measure bell36
cz bell36 o
H m
H bell38
cnot bell38 bell39
cnot k bell39
measure bell39
cnot bell39 bell38
cnot bell38 e
cnot bell38 i
H bell38
measure bell38
cz bell38 k
H bell40
cnot bell40 bell41
cnot k bell41
measure bell41
cnot bell41 bell40
cnot bell40 j
H bell40
measure bell40
cz bell40 k
H bell42
cnot bell42 bell43
cnot m bell43
measure bell43
cnot bell43 bell42
cnot bell42 k
H bell42
measure bell42
cz bell42 m
H bell44
cnot bell44 bell45
cnot k bell45
measure bell45
cnot bell45 bell44
cnot bell44 d
H bell44
measure bell44
cz bell44 k
cnot k c
H bell46
cnot bell46 bell47
cnot k bell47
measure bell47
cnot bell47 bell46
cnot bell46 b
H bell46
measure bell46
cz bell46 k
H 1
T 1
H bell48
cnot bell48 bell49
cnot l bell49
measure bell49
cnot bell49 bell48
cnot bell48 1
T* 1
H bell50
cnot bell50 bell51
cnot m bell51
measure bell51
cnot bell51 bell50
cnot bell50 1
T 1
cnot bell48 1
T* 1
cnot bell50 1
H 1
H 0
T 0
H bell52
cnot bell52 bell53
cnot 1 bell53
measure bell53
cnot bell53 bell52
cnot bell52 0
T* 0
cnot bell32 0
T 0
cnot bell52 0
T* 0
cnot bell32 0
H 0
H k
T k
H bell54
cnot bell54 bell55
cnot 0 bell55
measure bell55
cnot bell55 bell54
cnot bell54 k
T* k
H bell56
cnot bell56 bell57
cnot o bell57
measure bell57
cnot bell57 bell56
cnot bell56 k
T k
cnot bell54 k
H bell54
measure bell54
cz bell54 0
T* k
cnot bell56 k
H bell56
measure bell56
cz bell56 o
H k
T 0
cnot o 0
T* 0
cnot o 0
H 0
T* 0
cnot bell52 0
T 0
cnot bell32 0
T* 0
cnot bell52 0
H bell52
measure bell52
cz bell52 1
T 0
cnot bell32 0
H 1
T* 1
cnot bell48 1
T 1
cnot bell50 1
T* 1
cnot bell48 1
H bell48
measure bell48
cz bell48 l
T 1
cnot bell50 1
H bell50
measure bell50
cz bell50 m
H 1
H bell58
cnot bell58 bell59
cnot k bell59
measure bell59
cnot bell59 bell58
cnot bell58 b
H bell58
measure bell58
cz bell58 k
cnot k c
H bell60
cnot bell60 bell61
cnot k bell61
measure bell61
cnot bell61 bell60
cnot bell60 d
H bell60
measure bell60
cz bell60 k
H bell62
cnot bell62 bell63
cnot k bell63
measure bell63
cnot bell63 bell62
cnot bell62 e
H bell62
measure bell62
cz bell62 k
cnot k g
H bell64
cnot bell64 bell65
cnot k bell65
measure bell65
cnot bell65 bell64
cnot bell64 j
H bell64
measure bell64
cz bell64 k
H bell66
cnot bell66 bell67
cnot l bell67
measure bell67
cnot bell67 bell66
cnot bell66 k
H bell66
measure bell66
cz bell66 l
T 0
H bell68
cnot bell68 bell69
cnot m bell69
measure bell69
cnot bell69 bell68
cnot bell68 0
T* 0
cnot bell32 0
T 0
cnot bell68 0
T* 0
cnot bell32 0
H 0
T l
H l
T l
H bell70
cnot bell70 bell71
cnot 0 bell71
measure bell71
cnot bell71 bell70
cnot bell70 l
T* l
H bell72
cnot bell72 bell73
cnot o bell73
measure bell73
cnot bell73 bell72
cnot bell72 l
T l
cnot bell70 l
H bell70
measure bell70
cz bell70 0
T* l
cnot bell72 l
H l
T 0
cnot o 0
T* 0
cnot o 0
H 0
T* 0
cnot bell68 0
T 0
cnot bell32 0
T* 0
cnot bell68 0
H bell68
measure bell68
cz bell68 m
T 0
cnot bell32 0
H bell32
measure bell32
cz bell32 n
H bell74
cnot bell74 bell75
cnot k bell75
measure bell75
cnot bell75 bell74
cnot bell74 f
H bell74
measure bell74
cz bell74 k
H bell76
cnot bell76 bell77
cnot m bell77
measure bell77
cnot bell77 bell76
cnot bell76 h
H bell76
measure bell76
cz bell76 m
H bell78
cnot bell78 bell79
cnot n bell79
measure bell79
cnot bell79 bell78
cnot bell78 k
H bell78
measure bell78
cz bell78 n
H bell80
cnot bell80 bell81
cnot l bell81
measure bell81
cnot bell81 bell80
cnot bell80 k
H bell80
measure bell80
cz bell80 l
cnot l m
T 0
H bell82
cnot bell82 bell83
cnot m bell83
measure bell83
cnot bell83 bell82
cnot bell82 0
T* 0
H bell84
cnot bell84 bell85
cnot n bell85
measure bell85
cnot bell85 bell84
cnot bell84 0
T 0
cnot bell82 0
T* 0
cnot bell84 0
H 0
H l
T l
H bell86
cnot bell86 bell87
cnot 0 bell87
measure bell87
cnot bell87 bell86
cnot bell86 l
T* l
cnot bell72 l
T l
cnot bell86 l
H bell86
measure bell86
cz bell86 0
T* l
cnot bell72 l
H l
T 0
cnot o 0
T* 0
cnot o 0
H 0
T* 0
cnot bell82 0
T 0
cnot bell84 0
T* 0
cnot bell82 0
H bell82
measure bell82
cz bell82 m
T 0
cnot bell84 0
H bell84
measure bell84
cz bell84 n
H bell88
cnot bell88 bell89
cnot n bell89
measure bell89
cnot bell89 bell88
cnot bell88 c
H bell88
measure bell88
cz bell88 n
H bell90
cnot bell90 bell91
cnot n bell91
measure bell91
cnot bell91 bell90
cnot bell90 d
H bell90
measure bell90
cz bell90 n
H bell92
cnot bell92 bell93
cnot l bell93
measure bell93
cnot bell93 bell92
cnot bell92 f
H bell92
measure bell92
cz bell92 l
H bell94
cnot bell94 bell95
cnot n bell95
measure bell95
cnot bell95 bell94
cnot bell94 e
H bell94
measure bell94
cz bell94 n
cnot l m
H bell96
cnot bell96 bell97
cnot m bell97
measure bell97
cnot bell97 bell96
cnot bell96 j
H bell96
measure bell96
cz bell96 m
T 0
H bell98
cnot bell98 bell99
cnot l bell99
measure bell99
cnot bell99 bell98
cnot bell98 0
T* 0
H bell100
cnot bell100 bell101
cnot m bell101
measure bell101
cnot bell101 bell100
cnot bell100 0
T 0
cnot bell98 0
T* 0
cnot bell100 0
H 0
S n
cnot m n
cnot l n
cnot bell72 n
cnot m n
cnot l n
T* n
cnot bell72 n
H n
T n
H bell102
cnot bell102 bell103
cnot 0 bell103
measure bell103
cnot bell103 bell102
cnot bell102 n
T* n
cnot bell72 n
T n
cnot bell102 n
H bell102
measure bell102
cz bell102 0
T* n
cnot bell72 n
H n
T 0
cnot o 0
T* 0
cnot o 0
H 0
T* 0
cnot bell98 0
T 0
cnot bell100 0
T* 0
cnot bell98 0
T 0
cnot bell100 0
H bell100
measure bell100
cz bell100 m
H bell104
cnot bell104 bell105
cnot n bell105
measure bell105
cnot bell105 bell104
cnot bell104 c
H bell104
measure bell104
cz bell104 n
H bell106
cnot bell106 bell107
cnot n bell107
measure bell107
cnot bell107 bell106
cnot bell106 d
H bell106
measure bell106
cz bell106 n
H bell108
cnot bell108 bell109
cnot n bell109
measure bell109
cnot bell109 bell108
cnot bell108 k
H bell108
measure bell108
cz bell108 n
H bell110
cnot bell110 bell111
cnot k bell111
measure bell111
cnot bell111 bell110
cnot bell110 i
H bell112
cnot bell112 bell113
cnot m bell113
measure bell113
cnot bell113 bell112
cnot bell112 c
H bell112
measure bell112
cz bell112 m
cnot bell110 a
H bell110
measure bell110
cz bell110 k
H bell114
cnot bell114 bell115
cnot m bell115
measure bell115
cnot bell115 bell114
cnot bell114 a
H bell114
measure bell114
cz bell114 m
H m
T m
cnot l m
T* m
cnot bell72 m
T m
cnot l m
T* m
cnot bell72 m
H bell72
measure bell72
cz bell72 o
H m
H bell116
cnot bell116 bell117
cnot m bell117
measure bell117
cnot bell117 bell116
cnot bell116 c
H bell116
measure bell116
cz bell116 m
H bell118
cnot bell118 bell119
cnot o bell119
measure bell119
cnot bell119 bell118
cnot bell118 g
H bell120
cnot bell120 bell121
cnot m bell121
measure bell121
cnot bell121 bell120
cnot bell120 h
H bell120
measure bell120
cz bell120 m
cnot bell118 k
H bell118
measure bell118
cz bell118 o
H bell122
cnot bell122 bell123
cnot o bell123
measure bell123
cnot bell123 bell122
cnot bell122 n
H bell122
measure bell122
cz bell122 o
H bell124
cnot bell124 bell125
cnot k bell125
measure bell125
cnot bell125 bell124
cnot bell124 h
H bell124
measure bell124
cz bell124 k
H bell126
cnot bell126 bell127
cnot n bell127
measure bell127
cnot bell127 bell126
cnot bell126 e
H bell126
measure bell126
cz bell126 n
T 0
cnot bell98 0
T* 0
H bell128
cnot bell128 bell129
cnot m bell129
measure bell129
cnot bell129 bell128
cnot bell128 0
T 0
cnot bell98 0
T* 0
cnot bell128 0
H 0
S* o
cnot bell98 o
T* o
cnot bell98 o
H o
T o
cnot 0 o
T* o
H bell130
cnot bell130 bell131
cnot n bell131
measure bell131
cnot bell131 bell130
cnot bell130 o
T o
cnot 0 o
T* o
cnot bell130 o
H o
T 0
cnot bell130 0
T* 0
cnot bell130 0
H 0
T* 0
cnot bell98 0
T 0
cnot bell128 0
T* 0
cnot bell98 0
H bell98
measure bell98
cz bell98 l
T 0
cnot bell128 0
H bell128
measure bell128
cz bell128 m
H 0
T l
H bell132
cnot bell132 bell133
cnot o bell133
measure bell133
cnot bell133 bell132
cnot bell132 g
cnot bell132 k
H bell132
measure bell132
cz bell132 o
H bell134
cnot bell134 bell135
cnot o bell135
measure bell135
cnot bell135 bell134
cnot bell134 l
cnot bell134 m
H bell134
measure bell134
cz bell134 o
H bell136
cnot bell136 bell137
cnot m bell137
measure bell137
cnot bell137 bell136
cnot bell136 e
cnot bell136 a
H bell136
measure bell136
cz bell136 m
H o
T o
H bell138
cnot bell138 bell139
cnot l bell139
measure bell139
cnot bell139 bell138
cnot bell138 o
T* o
cnot bell130 o
T o
cnot bell138 o
H bell138
measure bell138
cz bell138 l
T* o
cnot bell130 o
H bell130
measure bell130
cz bell130 n
H o
T l
S n
cnot l n
T* n
cnot l m
cnot k g
H bell140
cnot bell140 bell141
cnot k bell141
measure bell141
cnot bell141 bell140
cnot bell140 j
H bell140
measure bell140
cz bell140 k
H bell142
cnot bell142 bell143
cnot o bell143
measure bell143
cnot bell143 bell142
cnot bell142 l
cnot bell142 m
H bell142
measure bell142
cz bell142 o
cnot l n
cnot l m
H bell144
cnot bell144 bell145
cnot n bell145
measure bell145
cnot bell145 bell144
cnot bell144 k
H bell144
measure bell144
cz bell144 n
H bell146
cnot bell146 bell147
cnot k bell147
measure bell147
cnot bell147 bell146
cnot bell146 n
H bell146
measure bell146
cz bell146 k
H bell148
cnot bell148 bell149
cnot n bell149
measure bell149
cnot bell149 bell148
cnot bell148 o
H bell148
measure bell148
cz bell148 n
H bell150
cnot bell150 bell151
cnot j bell151
measure bell151
cnot bell151 bell150
cnot bell150 m
H bell150
measure bell150
cz bell150 j
H bell152
cnot bell152 bell153
cnot j bell153
measure bell153
cnot bell153 bell152
cnot bell152 i
H bell152
measure bell152
cz bell152 j
H bell154
cnot bell154 bell155
cnot i bell155
measure bell155
cnot bell155 bell154
cnot bell154 m
cnot bell154 l
H bell154
measure bell154
cz bell154 i
H bell156
cnot bell156 bell157
cnot i bell157
measure bell157
cnot bell157 bell156
cnot bell156 h
H bell156
measure bell156
cz bell156 i
H bell158
cnot bell158 bell159
cnot h bell159
measure bell159
cnot bell159 bell158
cnot bell158 l
H bell158
measure bell158
cz bell158 h
H bell160
cnot bell160 bell161
cnot j bell161
measure bell161
cnot bell161 bell160
cnot bell160 n
H bell160
measure bell160
cz bell160 j
H bell162
cnot bell162 bell163
cnot h bell163
measure bell163
cnot bell163 bell162
cnot bell162 k
cnot bell162 g
H bell162
measure bell162
cz bell162 h
H bell164
cnot bell164 bell165
cnot g bell165
measure bell165
cnot bell165 bell164
cnot bell164 j
H bell164
measure bell164
cz bell164 g
cnot j f
cnot f j
H bell166
cnot bell166 bell167
cnot f bell167
measure bell167
cnot bell167 bell166
cnot bell166 i
H bell166
measure bell166
cz bell166 f
cnot i e
cnot e i
cnot g k
H bell168
cnot bell168 bell169
cnot e bell169
measure bell169
cnot bell169 bell168
cnot bell168 h
H bell168
measure bell168
cz bell168 e
H bell170
cnot bell170 bell171
cnot h bell171
measure bell171
cnot bell171 bell170
cnot bell170 d
H bell170
measure bell170
cz bell170 h
H bell172
cnot bell172 bell173
cnot d bell173
measure bell173
cnot bell173 bell172
cnot bell172 g
H bell172
measure bell172
cz bell172 d
cnot g c
cnot c g
H bell174
cnot bell174 bell175
cnot c bell175
measure bell175
cnot bell175 bell174
cnot bell174 f
H bell174
measure bell174
cz bell174 c
cnot f b
cnot b f
H bell176
cnot bell176 bell177
cnot d bell177
measure bell177
cnot bell177 bell176
cnot bell176 h
H bell176
measure bell176
cz bell176 d
H bell178
cnot bell178 bell179
cnot b bell179
measure bell179
cnot bell179 bell178
cnot bell178 e
H bell178
measure bell178
cz bell178 b
cnot e a
cnot a e
H bell180
cnot bell180 bell181
cnot a bell181
measure bell181
cnot bell181 bell180
cnot bell180 d
H bell180
measure bell180
cz bell180 a
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
END
