# Hyperedge cut (ebits): 51

# Actual ebits used (Synthesis): 102
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/ham15-med.qc):
#   Qubits: 17
#   H: 164
#   T: 574
#   cnot: 534
#   Depth: 667
#   T depth: 291
# Result (112.048ms):
#   Qubits: 221
#   H: 302
#   S: 33
#   T: 372
#   Z: 7
#   cnot: 759
#   cz: 103
#   measure: 204
#   reset: 205
#   swap: 1
#   Depth: 1059
#   T depth: 282


# Result Circuit
.v a b c d e f g h i j k l m n o 0 1 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a b c d e f g h i j k l m n o
.o a b c d e f g h i j k l m n o
BEGIN 
cnot o j
H bell0
cnot bell0 bell1
cnot n bell1
measure bell1
cnot bell1 bell0
cnot bell0 o
H 1
T 1
H bell2
cnot bell2 bell3
cnot l bell3
measure bell3
cnot bell3 bell2
cnot bell2 1
T* 1
H bell4
cnot bell4 bell5
cnot m bell5
measure bell5
cnot bell5 bell4
cnot bell4 1
T 1
cnot bell2 1
T* 1
cnot bell4 1
H 1
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H e
T e
H bell6
cnot bell6 bell7
cnot 0 bell7
measure bell7
cnot bell7 bell6
cnot bell6 e
T* e
H bell8
cnot bell8 bell9
cnot o bell9
measure bell9
cnot bell9 bell8
cnot bell8 e
T e
cnot bell6 e
H bell6
measure bell6
cz bell6 0
T* e
cnot bell8 e
H bell8
measure bell8
cz bell8 o
H e
T 0
H bell10
cnot bell10 bell11
cnot o bell11
measure bell11
cnot bell11 bell10
cnot bell10 0
T* 0
cnot bell10 0
H bell10
measure bell10
cz bell10 o
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell2 1
T* 1
cnot bell4 1
T 1
cnot bell2 1
H bell2
measure bell2
cz bell2 l
T* 1
cnot bell4 1
H bell4
measure bell4
cz bell4 m
S l
H bell12
cnot bell12 bell13
cnot m bell13
measure bell13
cnot bell13 bell12
cnot bell12 l
S* l
T o
H bell14
cnot bell14 bell15
cnot o bell15
measure bell15
cnot bell15 bell14
cnot bell14 l
H bell14
measure bell14
cz bell14 o
cnot bell12 l
H bell12
measure bell12
cz bell12 m
H o
T o
cnot m o
T* o
cnot bell0 o
T o
cnot m o
T* o
cnot bell0 o
H bell0
measure bell0
cz bell0 n
H o
T* n
Z n
H bell16
cnot bell16 bell17
cnot m bell17
measure bell17
cnot bell17 bell16
cnot bell16 n
T* n
cnot bell16 n
H n
T n
H bell18
cnot bell18 bell19
cnot l bell19
measure bell19
cnot bell19 bell18
cnot bell18 n
T* n
H bell20
cnot bell20 bell21
cnot o bell21
measure bell21
cnot bell21 bell20
cnot bell20 n
T n
cnot bell18 n
T* n
cnot bell20 n
H bell20
measure bell20
cz bell20 o
H n
T 1
cnot bell18 1
T* 1
cnot bell16 1
T 1
cnot bell18 1
T* 1
cnot bell16 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H b
T b
H bell22
cnot bell22 bell23
cnot 0 bell23
measure bell23
cnot bell23 bell22
cnot bell22 b
T* b
H bell24
cnot bell24 bell25
cnot o bell25
measure bell25
cnot bell25 bell24
cnot bell24 b
T b
cnot bell22 b
H bell22
measure bell22
cz bell22 0
T* b
cnot bell24 b
H bell24
measure bell24
cz bell24 o
H b
T 0
H bell26
cnot bell26 bell27
cnot o bell27
measure bell27
cnot bell27 bell26
cnot bell26 0
T* 0
cnot bell26 0
H bell26
measure bell26
cz bell26 o
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell18 1
T* 1
cnot bell16 1
T 1
cnot bell18 1
T* 1
cnot bell16 1
H bell28
cnot bell28 bell29
cnot o bell29
measure bell29
cnot bell29 bell28
cnot bell28 k
H bell28
measure bell28
cz bell28 o
T 0
cnot bell18 0
T* 0
cnot bell16 0
T 0
cnot bell18 0
H bell18
measure bell18
cz bell18 l
T* 0
cnot bell16 0
H 0
S o
H bell30
cnot bell30 bell31
cnot l bell31
measure bell31
cnot bell31 bell30
cnot bell30 o
T* o
cnot bell30 o
H bell30
measure bell30
cz bell30 l
H o
T o
H bell32
cnot bell32 bell33
cnot 0 bell33
measure bell33
cnot bell33 bell32
cnot bell32 o
T* o
H bell34
cnot bell34 bell35
cnot n bell35
measure bell35
cnot bell35 bell34
cnot bell34 o
T o
cnot bell32 o
H bell32
measure bell32
cz bell32 0
T* o
cnot bell34 o
H bell34
measure bell34
cz bell34 n
H o
T 0
cnot n 0
T* 0
cnot n 0
H 0
T 0
H bell36
cnot bell36 bell37
cnot l bell37
measure bell37
cnot bell37 bell36
cnot bell36 0
T* 0
cnot bell16 0
T 0
cnot bell36 0
H bell36
measure bell36
cz bell36 l
T* 0
cnot bell16 0
H j
T j
H bell38
cnot bell38 bell39
cnot l bell39
measure bell39
cnot bell39 bell38
cnot bell38 j
T* j
cnot o j
T j
cnot bell38 j
H bell38
measure bell38
cz bell38 l
T* j
cnot o j
T 1
H bell40
cnot bell40 bell41
cnot l bell41
measure bell41
cnot bell41 bell40
cnot bell40 1
T* 1
cnot bell16 1
T 1
cnot bell40 1
T* 1
cnot bell16 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H f
T f
H bell42
cnot bell42 bell43
cnot 0 bell43
measure bell43
cnot bell43 bell42
cnot bell42 f
T* f
H bell44
cnot bell44 bell45
cnot o bell45
measure bell45
cnot bell45 bell44
cnot bell44 f
T f
cnot bell42 f
H bell42
measure bell42
cz bell42 0
T* f
cnot bell44 f
H bell44
measure bell44
cz bell44 o
H f
T 0
H bell46
cnot bell46 bell47
cnot o bell47
measure bell47
cnot bell47 bell46
cnot bell46 0
T* 0
cnot bell46 0
H bell46
measure bell46
cz bell46 o
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell40 1
T* 1
cnot bell16 1
T 1
cnot bell40 1
T* 1
cnot bell16 1
H bell16
measure bell16
cz bell16 m
H a
T a
H bell48
cnot bell48 bell49
cnot m bell49
measure bell49
cnot bell49 bell48
cnot bell48 a
T* a
H bell50
cnot bell50 bell51
cnot o bell51
measure bell51
cnot bell51 bell50
cnot bell50 a
T a
cnot bell48 a
H bell48
measure bell48
cz bell48 m
T* a
cnot bell50 a
T a
H bell52
cnot bell52 bell53
cnot n bell53
measure bell53
cnot bell53 bell52
cnot bell52 a
T* a
cnot bell50 a
T a
cnot bell52 a
H bell52
measure bell52
cz bell52 n
T* a
cnot bell50 a
T 1
cnot bell40 1
T* 1
H bell54
cnot bell54 bell55
cnot m bell55
measure bell55
cnot bell55 bell54
cnot bell54 1
T 1
cnot bell40 1
T* 1
cnot bell54 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
T a
H bell56
cnot bell56 bell57
cnot 0 bell57
measure bell57
cnot bell57 bell56
cnot bell56 a
T* a
cnot bell50 a
T a
cnot bell56 a
H bell56
measure bell56
cz bell56 0
T* a
cnot bell50 a
H bell50
measure bell50
cz bell50 o
T 0
H bell58
cnot bell58 bell59
cnot o bell59
measure bell59
cnot bell59 bell58
cnot bell58 0
T* 0
cnot bell58 0
H bell58
measure bell58
cz bell58 o
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell40 1
T* 1
cnot bell54 1
T 1
cnot bell40 1
T* 1
cnot bell54 1
H bell54
measure bell54
cz bell54 m
cnot o m
T 1
cnot bell40 1
T* 1
H bell60
cnot bell60 bell61
cnot m bell61
measure bell61
cnot bell61 bell60
cnot bell60 1
T 1
cnot bell40 1
T* 1
cnot bell60 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H d
T d
H bell62
cnot bell62 bell63
cnot 0 bell63
measure bell63
cnot bell63 bell62
cnot bell62 d
T* d
H bell64
cnot bell64 bell65
cnot o bell65
measure bell65
cnot bell65 bell64
cnot bell64 d
T d
cnot bell62 d
H bell62
measure bell62
cz bell62 0
T* d
cnot bell64 d
H bell64
measure bell64
cz bell64 o
H d
T 0
H bell66
cnot bell66 bell67
cnot o bell67
measure bell67
cnot bell67 bell66
cnot bell66 0
T* 0
cnot bell66 0
H bell66
measure bell66
cz bell66 o
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell40 1
T* 1
cnot bell60 1
T 1
cnot bell40 1
T* 1
cnot bell60 1
H bell60
measure bell60
cz bell60 m
T j
cnot m j
T* j
cnot o j
T j
cnot m j
T* j
cnot o j
H c
T c
H bell68
cnot bell68 bell69
cnot m bell69
measure bell69
cnot bell69 bell68
cnot bell68 c
T* c
H bell70
cnot bell70 bell71
cnot o bell71
measure bell71
cnot bell71 bell70
cnot bell70 c
T c
cnot bell68 c
H bell68
measure bell68
cz bell68 m
T* c
cnot bell70 c
T 1
cnot bell40 1
T* 1
H bell72
cnot bell72 bell73
cnot m bell73
measure bell73
cnot bell73 bell72
cnot bell72 1
T 1
cnot bell40 1
T* 1
cnot bell72 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
T c
H bell74
cnot bell74 bell75
cnot 0 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c
T* c
cnot bell70 c
T c
cnot bell74 c
H bell74
measure bell74
cz bell74 0
T* c
cnot bell70 c
H bell70
measure bell70
cz bell70 o
T 0
H bell76
cnot bell76 bell77
cnot o bell77
measure bell77
cnot bell77 bell76
cnot bell76 0
T* 0
cnot bell76 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell40 1
T* 1
cnot bell72 1
T 1
cnot bell40 1
T* 1
cnot bell72 1
T 0
cnot bell40 0
T* 0
cnot bell72 0
T 0
cnot bell40 0
T* 0
cnot bell72 0
H 0
Z n
cnot bell76 n
T* n
cnot bell76 n
H n
T n
cnot 0 n
T* n
cnot bell76 n
T n
cnot 0 n
T* n
cnot bell76 n
H n
T 0
cnot bell76 0
T* 0
cnot bell76 0
H bell76
measure bell76
cz bell76 o
H 0
T 0
cnot bell40 0
T* 0
cnot bell72 0
T 0
cnot bell40 0
H bell40
measure bell40
cz bell40 l
T* 0
cnot bell72 0
T 0
cnot bell72 0
T* 0
cnot n 0
T 0
cnot bell72 0
T* 0
cnot n 0
H 0
T c
H bell78
cnot bell78 bell79
cnot 0 bell79
measure bell79
cnot bell79 bell78
cnot bell78 c
T* c
H bell80
cnot bell80 bell81
cnot o bell81
measure bell81
cnot bell81 bell80
cnot bell80 c
T c
cnot bell78 c
H bell78
measure bell78
cz bell78 0
T* c
cnot bell80 c
H bell80
measure bell80
cz bell80 o
H c
T 0
H bell82
cnot bell82 bell83
cnot o bell83
measure bell83
cnot bell83 bell82
cnot bell82 0
T* 0
cnot bell82 0
H bell82
measure bell82
cz bell82 o
H 0
T 0
cnot bell72 0
T* 0
cnot n 0
T 0
cnot bell72 0
T* 0
cnot n 0
T 0
cnot bell72 0
T* 0
cnot n 0
T 0
cnot bell72 0
H bell72
measure bell72
cz bell72 m
T* 0
cnot n 0
H 0
H bell84
cnot bell84 bell85
cnot m bell85
measure bell85
cnot bell85 bell84
cnot bell84 l
S l
H bell86
cnot bell86 bell87
cnot o bell87
measure bell87
cnot bell87 bell86
cnot bell86 l
cnot bell84 l
H bell84
measure bell84
cz bell84 m
T* l
cnot bell86 l
H l
T l
H bell88
cnot bell88 bell89
cnot 0 bell89
measure bell89
cnot bell89 bell88
cnot bell88 l
T* l
cnot bell86 l
T l
cnot bell88 l
H bell88
measure bell88
cz bell88 0
T* l
cnot bell86 l
H bell86
measure bell86
cz bell86 o
H l
T 0
H bell90
cnot bell90 bell91
cnot o bell91
measure bell91
cnot bell91 bell90
cnot bell90 0
T* 0
cnot bell90 0
H bell90
measure bell90
cz bell90 o
H 0
T 0
H bell92
cnot bell92 bell93
cnot m bell93
measure bell93
cnot bell93 bell92
cnot bell92 0
T* 0
cnot n 0
T 0
cnot bell92 0
T* 0
cnot n 0
T a
H bell94
cnot bell94 bell95
cnot l bell95
measure bell95
cnot bell95 bell94
cnot bell94 a
T* a
H bell96
cnot bell96 bell97
cnot o bell97
measure bell97
cnot bell97 bell96
cnot bell96 a
T a
cnot bell94 a
H bell94
measure bell94
cz bell94 l
T* a
cnot bell96 a
H bell96
measure bell96
cz bell96 o
H a
T 1
H bell98
cnot bell98 bell99
cnot l bell99
measure bell99
cnot bell99 bell98
cnot bell98 1
T* 1
cnot bell92 1
T 1
cnot bell98 1
T* 1
cnot bell92 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H g
T g
H bell100
cnot bell100 bell101
cnot 0 bell101
measure bell101
cnot bell101 bell100
cnot bell100 g
T* g
H bell102
cnot bell102 bell103
cnot o bell103
measure bell103
cnot bell103 bell102
cnot bell102 g
T g
cnot bell100 g
H bell100
measure bell100
cz bell100 0
T* g
cnot bell102 g
H bell102
measure bell102
cz bell102 o
H g
T 0
H bell104
cnot bell104 bell105
cnot o bell105
measure bell105
cnot bell105 bell104
cnot bell104 0
T* 0
cnot bell104 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell98 1
T* 1
cnot bell92 1
T 1
cnot bell98 1
T* 1
cnot bell92 1
S* n
cnot bell92 n
Z n
cnot bell92 n
H bell92
measure bell92
cz bell92 m
H n
T n
cnot bell98 n
T* n
cnot bell104 n
T n
cnot bell98 n
H bell98
measure bell98
cz bell98 l
T* n
cnot bell104 n
H bell104
measure bell104
cz bell104 o
H n
Z l
H bell106
cnot bell106 bell107
cnot m bell107
measure bell107
cnot bell107 bell106
cnot bell106 l
S* l
H bell108
cnot bell108 bell109
cnot o bell109
measure bell109
cnot bell109 bell108
cnot bell108 l
cnot bell106 l
H bell106
measure bell106
cz bell106 m
S* l
cnot bell108 l
H l
T l
H bell110
cnot bell110 bell111
cnot n bell111
measure bell111
cnot bell111 bell110
cnot bell110 l
T* l
cnot bell108 l
T l
cnot bell110 l
H bell110
measure bell110
cz bell110 n
T* l
cnot bell108 l
H bell108
measure bell108
cz bell108 o
H l
T 1
H bell112
cnot bell112 bell113
cnot l bell113
measure bell113
cnot bell113 bell112
cnot bell112 1
T* 1
H bell114
cnot bell114 bell115
cnot m bell115
measure bell115
cnot bell115 bell114
cnot bell114 1
T 1
cnot bell112 1
T* 1
cnot bell114 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H h
T h
H bell116
cnot bell116 bell117
cnot 0 bell117
measure bell117
cnot bell117 bell116
cnot bell116 h
T* h
H bell118
cnot bell118 bell119
cnot o bell119
measure bell119
cnot bell119 bell118
cnot bell118 h
T h
cnot bell116 h
H bell116
measure bell116
cz bell116 0
T* h
cnot bell118 h
H bell118
measure bell118
cz bell118 o
H h
T 0
H bell120
cnot bell120 bell121
cnot o bell121
measure bell121
cnot bell121 bell120
cnot bell120 0
T* 0
cnot bell120 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell112 1
T* 1
cnot bell114 1
T 1
cnot bell112 1
T* 1
cnot bell114 1
H bell114
measure bell114
cz bell114 m
T 0
cnot bell112 0
T* 0
cnot n 0
T 0
cnot bell112 0
H bell112
measure bell112
cz bell112 l
T* 0
cnot n 0
H 0
T* m
H bell122
cnot bell122 bell123
cnot l bell123
measure bell123
cnot bell123 bell122
cnot bell122 m
S* m
cnot o m
cnot bell122 m
H bell122
measure bell122
cz bell122 l
S m
cnot o m
H m
T m
H bell124
cnot bell124 bell125
cnot 0 bell125
measure bell125
cnot bell125 bell124
cnot bell124 m
T* m
cnot o m
T m
cnot bell124 m
H bell124
measure bell124
cz bell124 0
T* m
cnot o m
H m
T 0
cnot bell120 0
T* 0
cnot bell120 0
H 0
T 0
H bell126
cnot bell126 bell127
cnot l bell127
measure bell127
cnot bell127 bell126
cnot bell126 0
T* 0
cnot n 0
T 0
cnot bell126 0
T* 0
cnot n 0
T 1
cnot bell126 1
T* 1
H bell128
cnot bell128 bell129
cnot m bell129
measure bell129
cnot bell129 bell128
cnot bell128 1
T 1
cnot bell126 1
T* 1
cnot bell128 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
T j
H bell130
cnot bell130 bell131
cnot 0 bell131
measure bell131
cnot bell131 bell130
cnot bell130 j
T* j
cnot o j
T j
cnot bell130 j
H bell130
measure bell130
cz bell130 0
T* j
cnot o j
H j
T 0
cnot bell120 0
T* 0
cnot bell120 0
H bell120
measure bell120
cz bell120 o
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell126 1
T* 1
cnot bell128 1
T 1
cnot bell126 1
T* 1
cnot bell128 1
T 1
cnot bell126 1
T* 1
cnot bell128 1
T 1
cnot bell126 1
T* 1
cnot bell128 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H k
T k
H bell132
cnot bell132 bell133
cnot 0 bell133
measure bell133
cnot bell133 bell132
cnot bell132 k
T* k
H bell134
cnot bell134 bell135
cnot o bell135
measure bell135
cnot bell135 bell134
cnot bell134 k
T k
cnot bell132 k
H bell132
measure bell132
cz bell132 0
T* k
cnot bell134 k
H bell134
measure bell134
cz bell134 o
T 0
H bell136
cnot bell136 bell137
cnot o bell137
measure bell137
cnot bell137 bell136
cnot bell136 0
T* 0
cnot bell136 0
H bell136
measure bell136
cz bell136 o
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell126 1
T* 1
cnot bell128 1
T 1
cnot bell126 1
H bell126
measure bell126
cz bell126 l
T* 1
cnot bell128 1
Z o
H bell138
cnot bell138 bell139
cnot n bell139
measure bell139
cnot bell139 bell138
cnot bell138 o
T* o
cnot bell138 o
H bell138
measure bell138
cz bell138 n
H o
T o
H bell140
cnot bell140 bell141
cnot l bell141
measure bell141
cnot bell141 bell140
cnot bell140 o
T* o
cnot m o
T o
cnot bell140 o
H bell140
measure bell140
cz bell140 l
T* o
cnot m o
H o
T k
cnot l k
T* k
H bell142
cnot bell142 bell143
cnot n bell143
measure bell143
cnot bell143 bell142
cnot bell142 k
T k
cnot l k
T* k
cnot bell142 k
H bell142
measure bell142
cz bell142 n
H k
H bell144
cnot bell144 bell145
cnot o bell145
measure bell145
cnot bell145 bell144
cnot bell144 n
H bell144
measure bell144
cz bell144 o
T 1
H bell146
cnot bell146 bell147
cnot l bell147
measure bell147
cnot bell147 bell146
cnot bell146 1
T* 1
cnot bell128 1
T 1
cnot bell146 1
T* 1
cnot bell128 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H i
T i
H bell148
cnot bell148 bell149
cnot 0 bell149
measure bell149
cnot bell149 bell148
cnot bell148 i
T* i
H bell150
cnot bell150 bell151
cnot o bell151
measure bell151
cnot bell151 bell150
cnot bell150 i
T i
cnot bell148 i
H bell148
measure bell148
cz bell148 0
T* i
cnot bell150 i
H bell150
measure bell150
cz bell150 o
H i
T 0
H bell152
cnot bell152 bell153
cnot o bell153
measure bell153
cnot bell153 bell152
cnot bell152 0
T* 0
cnot bell152 0
H bell152
measure bell152
cz bell152 o
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot bell146 1
T* 1
cnot bell128 1
T 1
cnot bell146 1
H bell146
measure bell146
cz bell146 l
T* 1
cnot bell128 1
H bell128
measure bell128
cz bell128 m
H 1
Z l
S n
T o
H bell154
cnot bell154 bell155
cnot n bell155
measure bell155
cnot bell155 bell154
cnot bell154 o
S o
H bell156
cnot bell156 bell157
cnot l bell157
measure bell157
cnot bell157 bell156
cnot bell156 o
T o
Z o
T* m
cnot bell156 m
H bell156
measure bell156
cz bell156 l
T m
H bell158
cnot bell158 bell159
cnot k bell159
measure bell159
cnot bell159 bell158
cnot bell158 j
H bell160
cnot bell160 bell161
cnot o bell161
measure bell161
cnot bell161 bell160
cnot bell160 l
H bell160
measure bell160
cz bell160 o
cnot bell154 o
H bell154
measure bell154
cz bell154 n
cnot o m
swap m n
H bell162
cnot bell162 bell163
cnot n bell163
measure bell163
cnot bell163 bell162
cnot l bell162
cnot k bell162
H bell164
cnot bell164 bell165
cnot bell162 bell165
measure bell165
cnot bell165 bell164
reset bell165
cnot n bell164
cnot bell164 n
H bell164
measure bell164
cz bell164 k
cz bell164 l
H bell162
measure bell162
cz bell162 n
cnot bell158 o
H bell158
measure bell158
cz bell158 k
cnot j m
H bell166
cnot bell166 bell167
cnot m bell167
measure bell167
cnot bell167 bell166
cnot bell166 i
H bell166
measure bell166
cz bell166 m
H bell168
cnot bell168 bell169
cnot i bell169
measure bell169
cnot bell169 bell168
cnot bell168 m
H bell168
measure bell168
cz bell168 i
H bell170
cnot bell170 bell171
cnot i bell171
measure bell171
cnot bell171 bell170
cnot bell170 l
H bell170
measure bell170
cz bell170 i
H bell172
cnot bell172 bell173
cnot l bell173
measure bell173
cnot bell173 bell172
cnot bell172 h
H bell172
measure bell172
cz bell172 l
H bell174
cnot bell174 bell175
cnot h bell175
measure bell175
cnot bell175 bell174
cnot bell174 l
H bell176
cnot bell176 bell177
cnot j bell177
measure bell177
cnot bell177 bell176
cnot bell176 n
H bell176
measure bell176
cz bell176 j
cnot bell174 k
H bell174
measure bell174
cz bell174 h
H bell178
cnot bell178 bell179
cnot k bell179
measure bell179
cnot bell179 bell178
cnot bell178 g
H bell178
measure bell178
cz bell178 k
H bell180
cnot bell180 bell181
cnot g bell181
measure bell181
cnot bell181 bell180
cnot bell180 j
H bell180
measure bell180
cz bell180 g
H bell182
cnot bell182 bell183
cnot j bell183
measure bell183
cnot bell183 bell182
cnot bell182 f
H bell182
measure bell182
cz bell182 j
H bell184
cnot bell184 bell185
cnot f bell185
measure bell185
cnot bell185 bell184
cnot bell184 j
H bell184
measure bell184
cz bell184 f
H bell186
cnot bell186 bell187
cnot f bell187
measure bell187
cnot bell187 bell186
cnot bell186 i
H bell186
measure bell186
cz bell186 f
H bell188
cnot bell188 bell189
cnot i bell189
measure bell189
cnot bell189 bell188
cnot bell188 e
H bell188
measure bell188
cz bell188 i
H bell190
cnot bell190 bell191
cnot e bell191
measure bell191
cnot bell191 bell190
cnot bell190 i
H bell190
measure bell190
cz bell190 e
H bell192
cnot bell192 bell193
cnot g bell193
measure bell193
cnot bell193 bell192
cnot bell192 k
H bell192
measure bell192
cz bell192 g
H bell194
cnot bell194 bell195
cnot e bell195
measure bell195
cnot bell195 bell194
cnot bell194 h
H bell194
measure bell194
cz bell194 e
cnot h d
H bell196
cnot bell196 bell197
cnot d bell197
measure bell197
cnot bell197 bell196
cnot bell196 g
H bell196
measure bell196
cz bell196 d
cnot g c
cnot c g
H bell198
cnot bell198 bell199
cnot c bell199
measure bell199
cnot bell199 bell198
cnot bell198 f
H bell198
measure bell198
cz bell198 c
cnot f b
cnot b f
cnot d h
H bell200
cnot bell200 bell201
cnot b bell201
measure bell201
cnot bell201 bell200
cnot bell200 e
H bell200
measure bell200
cz bell200 b
cnot e a
cnot a e
H bell202
cnot bell202 bell203
cnot a bell203
measure bell203
cnot bell203 bell202
cnot bell202 d
H bell202
measure bell202
cz bell202 a
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
END
