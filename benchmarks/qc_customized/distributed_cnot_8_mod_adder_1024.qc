# Hyperedge cut (ebits): 91

# Actual ebits used (Synthesis): 145
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_adder_1024.qc):
#   Qubits: 28
#   H: 570
#   T: 1995
#   cnot: 1720
#   Depth: 2218
#   T depth: 981
# Result (796.570ms):
#   Qubits: 318
#   H: 620
#   T: 1259
#   cnot: 1673
#   cz: 145
#   measure: 290
#   reset: 290
#   swap: 8
#   Depth: 2557
#   T depth: 864


# Result Circuit
.v x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 0 1 2 3 4 5 6 7 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell256 bell257 bell258 bell259 bell26 bell260 bell261 bell262 bell263 bell264 bell265 bell266 bell267 bell268 bell269 bell27 bell270 bell271 bell272 bell273 bell274 bell275 bell276 bell277 bell278 bell279 bell28 bell280 bell281 bell282 bell283 bell284 bell285 bell286 bell287 bell288 bell289 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
.o x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
BEGIN 
H bell0
cnot bell0 bell1
cnot x10 bell1
measure bell1
cnot bell1 bell0
cnot bell0 x20
H bell0
measure bell0
cz bell0 x10
H x20
T x20
cnot x19 x20
T* x20
H bell2
cnot bell2 bell3
cnot x9 bell3
measure bell3
cnot bell3 bell2
cnot bell2 x20
T x20
cnot x19 x20
T* x20
cnot bell2 x20
swap 0 1
cnot bell2 x19
H 0
T 0
H bell4
cnot bell4 bell5
cnot x18 bell5
measure bell5
cnot bell5 bell4
cnot bell4 0
T* 0
H bell6
cnot bell6 bell7
cnot x8 bell7
measure bell7
cnot bell7 bell6
cnot bell6 0
T 0
cnot bell4 0
T* 0
cnot bell6 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot bell4 0
T 0
cnot bell6 0
T* 0
cnot bell4 0
T 0
cnot bell6 0
cnot bell2 x19
T x19
cnot bell2 x19
H bell2
measure bell2
cz bell2 x9
H x19
T x19
cnot bell4 x19
T* x19
cnot bell6 x19
T x19
cnot bell4 x19
H bell4
measure bell4
cz bell4 x18
T* x19
cnot bell6 x19
H bell6
measure bell6
cz bell6 x8
H x19
cnot x8 x18
H 1
T 1
H bell8
cnot bell8 bell9
cnot x17 bell9
measure bell9
cnot bell9 bell8
cnot bell8 1
T* 1
H bell10
cnot bell10 bell11
cnot x7 bell11
measure bell11
cnot bell11 bell10
cnot bell10 1
T 1
cnot bell8 1
T* 1
cnot bell10 1
swap 2 6
H 1
T 0
cnot 1 0
T* 0
H bell12
cnot bell12 bell13
cnot x18 bell13
measure bell13
cnot bell13 bell12
cnot bell12 0
T 0
cnot 1 0
T* 0
cnot bell12 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot bell12 0
T* 0
cnot 1 0
T 0
cnot bell12 0
H 1
T* 1
cnot bell8 1
T 1
cnot bell10 1
T* 1
cnot bell8 1
T 1
cnot bell10 1
T 0
cnot bell8 0
T* 0
cnot bell10 0
T 0
cnot bell8 0
T* 0
cnot bell10 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot bell12 x19
T x19
cnot 0 x19
T* x19
cnot bell12 x19
H x19
T 0
cnot bell12 0
T* 0
cnot bell12 0
H bell12
measure bell12
cz bell12 x18
swap 2 7
H 0
T* 0
cnot bell8 0
T 0
cnot bell10 0
T* 0
cnot bell8 0
H bell8
measure bell8
cz bell8 x17
T 0
cnot bell10 0
H bell10
measure bell10
cz bell10 x7
swap 2 6
cnot x8 x18
T x18
cnot x8 x18
H x18
T x18
cnot x17 x18
T* x18
H bell14
cnot bell14 bell15
cnot x7 bell15
measure bell15
cnot bell15 bell14
cnot bell14 x18
T x18
cnot x17 x18
T* x18
cnot bell14 x18
H x18
cnot bell14 x17
H 2
T 2
H bell16
cnot bell16 bell17
cnot x16 bell17
measure bell17
cnot bell17 bell16
cnot bell16 2
T* 2
H bell18
cnot bell18 bell19
cnot x6 bell19
measure bell19
cnot bell19 bell18
cnot bell18 2
T 2
cnot bell16 2
T* 2
cnot bell18 2
H 2
T 1
H bell20
cnot bell20 bell21
cnot 2 bell21
measure bell21
cnot bell21 bell20
cnot bell20 1
T* 1
H bell22
cnot bell22 bell23
cnot x17 bell23
measure bell23
cnot bell23 bell22
cnot bell22 1
T 1
cnot bell20 1
T* 1
cnot bell22 1
H 1
T 0
cnot 1 0
T* 0
H bell24
cnot bell24 bell25
cnot x18 bell25
measure bell25
cnot bell25 bell24
cnot bell24 0
T 0
cnot 1 0
T* 0
cnot bell24 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot bell24 0
T* 0
cnot 1 0
T 0
cnot bell24 0
H 1
T* 1
cnot bell20 1
T 1
cnot bell22 1
T* 1
cnot bell20 1
H bell20
measure bell20
cz bell20 2
T 1
cnot bell22 1
H 2
T* 2
cnot bell16 2
T 2
cnot bell18 2
T* 2
cnot bell16 2
H bell16
measure bell16
cz bell16 x16
T 2
cnot bell18 2
H bell18
measure bell18
cz bell18 x6
T 1
H bell26
cnot bell26 bell27
cnot x16 bell27
measure bell27
cnot bell27 bell26
cnot bell26 1
T* 1
H bell28
cnot bell28 bell29
cnot x6 bell29
measure bell29
cnot bell29 bell28
cnot bell28 1
T 1
cnot bell26 1
T* 1
cnot bell28 1
swap 3 5
H 1
T 0
cnot 1 0
T* 0
cnot bell22 0
T 0
cnot 1 0
T* 0
cnot bell22 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot bell24 x19
T x19
cnot 0 x19
T* x19
cnot bell24 x19
H x19
T 0
cnot bell24 0
T* 0
cnot bell24 0
H bell24
measure bell24
cz bell24 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell22 0
T* 0
cnot 1 0
T 0
cnot bell22 0
H 1
T* 1
cnot bell26 1
T 1
cnot bell28 1
T* 1
cnot bell26 1
T 1
cnot bell28 1
T 0
cnot bell26 0
T* 0
cnot bell28 0
T 0
cnot bell26 0
T* 0
cnot bell28 0
H 0
T x18
H x18
T x18
H bell30
cnot bell30 bell31
cnot 0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 x18
T* x18
cnot x17 x18
T x18
cnot bell30 x18
H bell30
measure bell30
cz bell30 0
T* x18
cnot x17 x18
H x18
T 0
cnot bell22 0
T* 0
cnot bell22 0
H bell22
measure bell22
cz bell22 x17
swap 3 6
H 0
T* 0
cnot bell26 0
T 0
cnot bell28 0
T* 0
cnot bell26 0
H bell26
measure bell26
cz bell26 x16
T 0
cnot bell28 0
H bell28
measure bell28
cz bell28 x6
swap 3 5
cnot bell14 x17
T x17
cnot bell14 x17
H bell14
measure bell14
cz bell14 x7
H x17
T x17
H bell32
cnot bell32 bell33
cnot x16 bell33
measure bell33
cnot bell33 bell32
cnot bell32 x17
T* x17
H bell34
cnot bell34 bell35
cnot x6 bell35
measure bell35
cnot bell35 bell34
cnot bell34 x17
T x17
cnot bell32 x17
H bell32
measure bell32
cz bell32 x16
T* x17
cnot bell34 x17
H bell34
measure bell34
cz bell34 x6
H x17
H bell36
cnot bell36 bell37
cnot x6 bell37
measure bell37
cnot bell37 bell36
cnot bell36 x16
H 3
T 3
H bell38
cnot bell38 bell39
cnot x15 bell39
measure bell39
cnot bell39 bell38
cnot bell38 3
T* 3
H bell40
cnot bell40 bell41
cnot x5 bell41
measure bell41
cnot bell41 bell40
cnot bell40 3
T 3
cnot bell38 3
T* 3
cnot bell40 3
H 3
T 2
cnot 3 2
T* 2
H bell42
cnot bell42 bell43
cnot x16 bell43
measure bell43
cnot bell43 bell42
cnot bell42 2
T 2
cnot 3 2
T* 2
cnot bell42 2
H 2
T 1
H bell44
cnot bell44 bell45
cnot 2 bell45
measure bell45
cnot bell45 bell44
cnot bell44 1
T* 1
H bell46
cnot bell46 bell47
cnot x17 bell47
measure bell47
cnot bell47 bell46
cnot bell46 1
T 1
cnot bell44 1
T* 1
cnot bell46 1
H 1
T 0
cnot 1 0
T* 0
H bell48
cnot bell48 bell49
cnot x18 bell49
measure bell49
cnot bell49 bell48
cnot bell48 0
T 0
cnot 1 0
T* 0
cnot bell48 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot bell48 0
T* 0
cnot 1 0
T 0
cnot bell48 0
H 1
T* 1
cnot bell44 1
T 1
cnot bell46 1
T* 1
cnot bell44 1
H bell44
measure bell44
cz bell44 2
T 1
cnot bell46 1
H 2
T* 2
cnot 3 2
T 2
cnot bell42 2
T* 2
cnot 3 2
T 2
cnot bell42 2
H bell42
measure bell42
cz bell42 x16
H 3
T* 3
cnot bell38 3
T 3
cnot bell40 3
T* 3
cnot bell38 3
T 3
cnot bell40 3
T 2
cnot bell38 2
T* 2
cnot bell40 2
T 2
cnot bell38 2
T* 2
cnot bell40 2
H 2
T 1
H bell50
cnot bell50 bell51
cnot 2 bell51
measure bell51
cnot bell51 bell50
cnot bell50 1
T* 1
H bell52
cnot bell52 bell53
cnot x16 bell53
measure bell53
cnot bell53 bell52
cnot bell52 1
T 1
cnot bell50 1
T* 1
cnot bell52 1
H 1
T 0
cnot 1 0
T* 0
cnot bell46 0
T 0
cnot 1 0
T* 0
cnot bell46 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot bell48 x19
T x19
cnot 0 x19
T* x19
cnot bell48 x19
H x19
T 0
cnot bell48 0
T* 0
cnot bell48 0
H bell48
measure bell48
cz bell48 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell46 0
T* 0
cnot 1 0
T 0
cnot bell46 0
H 1
T* 1
cnot bell50 1
T 1
cnot bell52 1
T* 1
cnot bell50 1
H bell50
measure bell50
cz bell50 2
T 1
cnot bell52 1
H 2
T* 2
cnot bell38 2
T 2
cnot bell40 2
T* 2
cnot bell38 2
H bell38
measure bell38
cz bell38 x15
T 2
cnot bell40 2
H bell40
measure bell40
cz bell40 x5
T 1
H bell54
cnot bell54 bell55
cnot x15 bell55
measure bell55
cnot bell55 bell54
cnot bell54 1
T* 1
H bell56
cnot bell56 bell57
cnot x5 bell57
measure bell57
cnot bell57 bell56
cnot bell56 1
T 1
cnot bell54 1
T* 1
cnot bell56 1
H 1
T 0
cnot 1 0
T* 0
cnot bell52 0
T 0
cnot 1 0
T* 0
cnot bell52 0
H 0
T x18
H x18
T x18
H bell58
cnot bell58 bell59
cnot 0 bell59
measure bell59
cnot bell59 bell58
cnot bell58 x18
T* x18
cnot x17 x18
T x18
cnot bell58 x18
H bell58
measure bell58
cz bell58 0
T* x18
cnot x17 x18
H x18
T 0
cnot bell46 0
T* 0
cnot bell46 0
H bell46
measure bell46
cz bell46 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell52 0
T* 0
cnot 1 0
T 0
cnot bell52 0
H bell52
measure bell52
cz bell52 x16
H 1
T* 1
cnot bell54 1
T 1
cnot bell56 1
T* 1
cnot bell54 1
T 1
cnot bell56 1
T 0
cnot bell54 0
T* 0
cnot bell56 0
T 0
cnot bell54 0
T* 0
cnot bell56 0
H 0
T x17
H x17
T x17
H bell60
cnot bell60 bell61
cnot 0 bell61
measure bell61
cnot bell61 bell60
cnot bell60 x17
T* x17
H bell62
cnot bell62 bell63
cnot x16 bell63
measure bell63
cnot bell63 bell62
cnot bell62 x17
T x17
cnot bell60 x17
H bell60
measure bell60
cz bell60 0
T* x17
cnot bell62 x17
H bell62
measure bell62
cz bell62 x16
H x17
T 0
H bell64
cnot bell64 bell65
cnot x16 bell65
measure bell65
cnot bell65 bell64
cnot bell64 0
T* 0
cnot bell64 0
H bell64
measure bell64
cz bell64 x16
swap 4 5
H 0
T* 0
cnot bell54 0
T 0
cnot bell56 0
T* 0
cnot bell54 0
H bell54
measure bell54
cz bell54 x15
T 0
cnot bell56 0
H bell56
measure bell56
cz bell56 x5
cnot bell36 x16
T x16
cnot bell36 x16
H bell36
measure bell36
cz bell36 x6
H x16
T x16
cnot x15 x16
T* x16
H bell66
cnot bell66 bell67
cnot x5 bell67
measure bell67
cnot bell67 bell66
cnot bell66 x16
T x16
cnot x15 x16
T* x16
cnot bell66 x16
H x16
cnot bell66 x15
H 4
T 4
H bell68
cnot bell68 bell69
cnot x14 bell69
measure bell69
cnot bell69 bell68
cnot bell68 4
T* 4
H bell70
cnot bell70 bell71
cnot x4 bell71
measure bell71
cnot bell71 bell70
cnot bell70 4
T 4
cnot bell68 4
T* 4
cnot bell70 4
H 4
T 3
cnot 4 3
T* 3
H bell72
cnot bell72 bell73
cnot x15 bell73
measure bell73
cnot bell73 bell72
cnot bell72 3
T 3
cnot 4 3
T* 3
cnot bell72 3
H 3
T 2
cnot 3 2
T* 2
H bell74
cnot bell74 bell75
cnot x16 bell75
measure bell75
cnot bell75 bell74
cnot bell74 2
T 2
cnot 3 2
T* 2
cnot bell74 2
H 2
T 1
H bell76
cnot bell76 bell77
cnot 2 bell77
measure bell77
cnot bell77 bell76
cnot bell76 1
T* 1
H bell78
cnot bell78 bell79
cnot x17 bell79
measure bell79
cnot bell79 bell78
cnot bell78 1
T 1
cnot bell76 1
T* 1
cnot bell78 1
H 1
T 0
cnot 1 0
T* 0
H bell80
cnot bell80 bell81
cnot x18 bell81
measure bell81
cnot bell81 bell80
cnot bell80 0
T 0
cnot 1 0
T* 0
cnot bell80 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot bell80 0
T* 0
cnot 1 0
T 0
cnot bell80 0
H 1
T* 1
cnot bell76 1
T 1
cnot bell78 1
T* 1
cnot bell76 1
H bell76
measure bell76
cz bell76 2
T 1
cnot bell78 1
H 2
T* 2
cnot 3 2
T 2
cnot bell74 2
T* 2
cnot 3 2
T 2
cnot bell74 2
H bell74
measure bell74
cz bell74 x16
H 3
T* 3
cnot 4 3
T 3
cnot bell72 3
T* 3
cnot 4 3
T 3
cnot bell72 3
H 4
T* 4
cnot bell68 4
T 4
cnot bell70 4
T* 4
cnot bell68 4
T 4
cnot bell70 4
T 3
cnot bell68 3
T* 3
cnot bell70 3
T 3
cnot bell68 3
T* 3
cnot bell70 3
H 3
T 2
cnot 3 2
T* 2
cnot bell72 2
T 2
cnot 3 2
T* 2
cnot bell72 2
H 2
T 1
H bell82
cnot bell82 bell83
cnot 2 bell83
measure bell83
cnot bell83 bell82
cnot bell82 1
T* 1
H bell84
cnot bell84 bell85
cnot x16 bell85
measure bell85
cnot bell85 bell84
cnot bell84 1
T 1
cnot bell82 1
T* 1
cnot bell84 1
H 1
T 0
cnot 1 0
T* 0
cnot bell78 0
T 0
cnot 1 0
T* 0
cnot bell78 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot bell80 x19
T x19
cnot 0 x19
T* x19
cnot bell80 x19
H x19
T 0
cnot bell80 0
T* 0
cnot bell80 0
H bell80
measure bell80
cz bell80 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell78 0
T* 0
cnot 1 0
T 0
cnot bell78 0
H 1
T* 1
cnot bell82 1
T 1
cnot bell84 1
T* 1
cnot bell82 1
H bell82
measure bell82
cz bell82 2
T 1
cnot bell84 1
H 2
T* 2
cnot 3 2
T 2
cnot bell72 2
T* 2
cnot 3 2
T 2
cnot bell72 2
H bell72
measure bell72
cz bell72 x15
H 3
T* 3
cnot bell68 3
T 3
cnot bell70 3
T* 3
cnot bell68 3
T 3
cnot bell70 3
T 2
cnot bell68 2
T* 2
cnot bell70 2
T 2
cnot bell68 2
T* 2
cnot bell70 2
H 2
T 1
H bell86
cnot bell86 bell87
cnot 2 bell87
measure bell87
cnot bell87 bell86
cnot bell86 1
T* 1
H bell88
cnot bell88 bell89
cnot x15 bell89
measure bell89
cnot bell89 bell88
cnot bell88 1
T 1
cnot bell86 1
T* 1
cnot bell88 1
H 1
T 0
cnot 1 0
T* 0
cnot bell84 0
T 0
cnot 1 0
T* 0
cnot bell84 0
H 0
T x18
H x18
T x18
H bell90
cnot bell90 bell91
cnot 0 bell91
measure bell91
cnot bell91 bell90
cnot bell90 x18
T* x18
cnot x17 x18
T x18
cnot bell90 x18
H bell90
measure bell90
cz bell90 0
T* x18
cnot x17 x18
H x18
T 0
cnot bell78 0
T* 0
cnot bell78 0
H bell78
measure bell78
cz bell78 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell84 0
T* 0
cnot 1 0
T 0
cnot bell84 0
H bell84
measure bell84
cz bell84 x16
H 1
T* 1
cnot bell86 1
T 1
cnot bell88 1
T* 1
cnot bell86 1
H bell86
measure bell86
cz bell86 2
T 1
cnot bell88 1
H 2
T* 2
cnot bell68 2
T 2
cnot bell70 2
T* 2
cnot bell68 2
H bell68
measure bell68
cz bell68 x14
T 2
cnot bell70 2
H bell70
measure bell70
cz bell70 x4
T 1
H bell92
cnot bell92 bell93
cnot x14 bell93
measure bell93
cnot bell93 bell92
cnot bell92 1
T* 1
H bell94
cnot bell94 bell95
cnot x4 bell95
measure bell95
cnot bell95 bell94
cnot bell94 1
T 1
cnot bell92 1
T* 1
cnot bell94 1
H 1
T 0
cnot 1 0
T* 0
cnot bell88 0
T 0
cnot 1 0
T* 0
cnot bell88 0
H 0
T x17
H x17
T x17
H bell96
cnot bell96 bell97
cnot 0 bell97
measure bell97
cnot bell97 bell96
cnot bell96 x17
T* x17
H bell98
cnot bell98 bell99
cnot x16 bell99
measure bell99
cnot bell99 bell98
cnot bell98 x17
T x17
cnot bell96 x17
H bell96
measure bell96
cz bell96 0
T* x17
cnot bell98 x17
H bell98
measure bell98
cz bell98 x16
H x17
T 0
H bell100
cnot bell100 bell101
cnot x16 bell101
measure bell101
cnot bell101 bell100
cnot bell100 0
T* 0
cnot bell100 0
H bell100
measure bell100
cz bell100 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell88 0
T* 0
cnot 1 0
T 0
cnot bell88 0
H 1
T* 1
cnot bell92 1
T 1
cnot bell94 1
T* 1
cnot bell92 1
T 1
cnot bell94 1
T 0
cnot bell92 0
T* 0
cnot bell94 0
T 0
cnot bell92 0
T* 0
cnot bell94 0
H 0
T x16
H x16
T x16
H bell102
cnot bell102 bell103
cnot 0 bell103
measure bell103
cnot bell103 bell102
cnot bell102 x16
T* x16
cnot x15 x16
T x16
cnot bell102 x16
H bell102
measure bell102
cz bell102 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell88 0
T* 0
cnot bell88 0
H bell88
measure bell88
cz bell88 x15
H 0
T* 0
cnot bell92 0
T 0
cnot bell94 0
T* 0
cnot bell92 0
H bell92
measure bell92
cz bell92 x14
T 0
cnot bell94 0
H bell94
measure bell94
cz bell94 x4
cnot bell66 x15
T x15
cnot bell66 x15
H bell66
measure bell66
cz bell66 x5
H x15
T x15
cnot x14 x15
T* x15
H bell104
cnot bell104 bell105
cnot x4 bell105
measure bell105
cnot bell105 bell104
cnot bell104 x15
T x15
cnot x14 x15
T* x15
cnot bell104 x15
H x15
cnot bell104 x14
H 5
T 5
H bell106
cnot bell106 bell107
cnot x13 bell107
measure bell107
cnot bell107 bell106
cnot bell106 5
T* 5
H bell108
cnot bell108 bell109
cnot x3 bell109
measure bell109
cnot bell109 bell108
cnot bell108 5
T 5
cnot bell106 5
T* 5
cnot bell108 5
H 5
T 4
cnot 5 4
T* 4
H bell110
cnot bell110 bell111
cnot x14 bell111
measure bell111
cnot bell111 bell110
cnot bell110 4
T 4
cnot 5 4
T* 4
cnot bell110 4
H 4
T 3
cnot 4 3
T* 3
H bell112
cnot bell112 bell113
cnot x15 bell113
measure bell113
cnot bell113 bell112
cnot bell112 3
T 3
cnot 4 3
T* 3
cnot bell112 3
H 3
T 2
cnot 3 2
T* 2
H bell114
cnot bell114 bell115
cnot x16 bell115
measure bell115
cnot bell115 bell114
cnot bell114 2
T 2
cnot 3 2
T* 2
cnot bell114 2
H 2
T 1
H bell116
cnot bell116 bell117
cnot 2 bell117
measure bell117
cnot bell117 bell116
cnot bell116 1
T* 1
H bell118
cnot bell118 bell119
cnot x17 bell119
measure bell119
cnot bell119 bell118
cnot bell118 1
T 1
cnot bell116 1
T* 1
cnot bell118 1
H 1
T 0
cnot 1 0
T* 0
H bell120
cnot bell120 bell121
cnot x18 bell121
measure bell121
cnot bell121 bell120
cnot bell120 0
T 0
cnot 1 0
T* 0
cnot bell120 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot bell120 0
T* 0
cnot 1 0
T 0
cnot bell120 0
H 1
T* 1
cnot bell116 1
T 1
cnot bell118 1
T* 1
cnot bell116 1
H bell116
measure bell116
cz bell116 2
T 1
cnot bell118 1
H 2
T* 2
cnot 3 2
T 2
cnot bell114 2
T* 2
cnot 3 2
T 2
cnot bell114 2
H bell114
measure bell114
cz bell114 x16
H 3
T* 3
cnot 4 3
T 3
cnot bell112 3
T* 3
cnot 4 3
T 3
cnot bell112 3
H 4
T* 4
cnot 5 4
T 4
cnot bell110 4
T* 4
cnot 5 4
T 4
cnot bell110 4
H 5
T* 5
cnot bell106 5
T 5
cnot bell108 5
T* 5
cnot bell106 5
T 5
cnot bell108 5
T 4
cnot bell106 4
T* 4
cnot bell108 4
T 4
cnot bell106 4
T* 4
cnot bell108 4
H 4
T 3
cnot 4 3
T* 3
cnot bell110 3
T 3
cnot 4 3
T* 3
cnot bell110 3
H 3
T 2
cnot 3 2
T* 2
cnot bell112 2
T 2
cnot 3 2
T* 2
cnot bell112 2
H 2
T 1
H bell122
cnot bell122 bell123
cnot 2 bell123
measure bell123
cnot bell123 bell122
cnot bell122 1
T* 1
H bell124
cnot bell124 bell125
cnot x16 bell125
measure bell125
cnot bell125 bell124
cnot bell124 1
T 1
cnot bell122 1
T* 1
cnot bell124 1
H 1
T 0
cnot 1 0
T* 0
cnot bell118 0
T 0
cnot 1 0
T* 0
cnot bell118 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot bell120 x19
T x19
cnot 0 x19
T* x19
cnot bell120 x19
H x19
T 0
cnot bell120 0
T* 0
cnot bell120 0
H bell120
measure bell120
cz bell120 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell118 0
T* 0
cnot 1 0
T 0
cnot bell118 0
H 1
T* 1
cnot bell122 1
T 1
cnot bell124 1
T* 1
cnot bell122 1
H bell122
measure bell122
cz bell122 2
T 1
cnot bell124 1
H 2
T* 2
cnot 3 2
T 2
cnot bell112 2
T* 2
cnot 3 2
T 2
cnot bell112 2
H bell112
measure bell112
cz bell112 x15
H 3
T* 3
cnot 4 3
T 3
cnot bell110 3
T* 3
cnot 4 3
T 3
cnot bell110 3
H 4
T* 4
cnot bell106 4
T 4
cnot bell108 4
T* 4
cnot bell106 4
T 4
cnot bell108 4
T 3
cnot bell106 3
T* 3
cnot bell108 3
T 3
cnot bell106 3
T* 3
cnot bell108 3
H 3
T 2
cnot 3 2
T* 2
cnot bell110 2
T 2
cnot 3 2
T* 2
cnot bell110 2
H 2
T 1
H bell126
cnot bell126 bell127
cnot 2 bell127
measure bell127
cnot bell127 bell126
cnot bell126 1
T* 1
H bell128
cnot bell128 bell129
cnot x15 bell129
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
cnot bell124 0
T 0
cnot 1 0
T* 0
cnot bell124 0
H 0
T x18
H x18
T x18
H bell130
cnot bell130 bell131
cnot 0 bell131
measure bell131
cnot bell131 bell130
cnot bell130 x18
T* x18
cnot x17 x18
T x18
cnot bell130 x18
H bell130
measure bell130
cz bell130 0
T* x18
cnot x17 x18
H x18
T 0
cnot bell118 0
T* 0
cnot bell118 0
H bell118
measure bell118
cz bell118 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell124 0
T* 0
cnot 1 0
T 0
cnot bell124 0
H bell124
measure bell124
cz bell124 x16
H 1
T* 1
cnot bell126 1
T 1
cnot bell128 1
T* 1
cnot bell126 1
H bell126
measure bell126
cz bell126 2
T 1
cnot bell128 1
H 2
T* 2
cnot 3 2
T 2
cnot bell110 2
T* 2
cnot 3 2
T 2
cnot bell110 2
H bell110
measure bell110
cz bell110 x14
H 3
T* 3
cnot bell106 3
T 3
cnot bell108 3
T* 3
cnot bell106 3
T 3
cnot bell108 3
T 2
cnot bell106 2
T* 2
cnot bell108 2
T 2
cnot bell106 2
T* 2
cnot bell108 2
H 2
T 1
H bell132
cnot bell132 bell133
cnot 2 bell133
measure bell133
cnot bell133 bell132
cnot bell132 1
T* 1
H bell134
cnot bell134 bell135
cnot x14 bell135
measure bell135
cnot bell135 bell134
cnot bell134 1
T 1
cnot bell132 1
T* 1
cnot bell134 1
H 1
T 0
cnot 1 0
T* 0
cnot bell128 0
T 0
cnot 1 0
T* 0
cnot bell128 0
H 0
T x17
H x17
T x17
H bell136
cnot bell136 bell137
cnot 0 bell137
measure bell137
cnot bell137 bell136
cnot bell136 x17
T* x17
H bell138
cnot bell138 bell139
cnot x16 bell139
measure bell139
cnot bell139 bell138
cnot bell138 x17
T x17
cnot bell136 x17
H bell136
measure bell136
cz bell136 0
T* x17
cnot bell138 x17
H bell138
measure bell138
cz bell138 x16
H x17
T 0
H bell140
cnot bell140 bell141
cnot x16 bell141
measure bell141
cnot bell141 bell140
cnot bell140 0
T* 0
cnot bell140 0
H bell140
measure bell140
cz bell140 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell128 0
T* 0
cnot 1 0
T 0
cnot bell128 0
H 1
T* 1
cnot bell132 1
T 1
cnot bell134 1
T* 1
cnot bell132 1
H bell132
measure bell132
cz bell132 2
T 1
cnot bell134 1
H 2
T* 2
cnot bell106 2
T 2
cnot bell108 2
T* 2
cnot bell106 2
H bell106
measure bell106
cz bell106 x13
T 2
cnot bell108 2
H bell108
measure bell108
cz bell108 x3
T 1
H bell142
cnot bell142 bell143
cnot x13 bell143
measure bell143
cnot bell143 bell142
cnot bell142 1
T* 1
H bell144
cnot bell144 bell145
cnot x3 bell145
measure bell145
cnot bell145 bell144
cnot bell144 1
T 1
cnot bell142 1
T* 1
cnot bell144 1
H 1
T 0
cnot 1 0
T* 0
cnot bell134 0
T 0
cnot 1 0
T* 0
cnot bell134 0
H 0
T x16
H x16
T x16
H bell146
cnot bell146 bell147
cnot 0 bell147
measure bell147
cnot bell147 bell146
cnot bell146 x16
T* x16
cnot x15 x16
T x16
cnot bell146 x16
H bell146
measure bell146
cz bell146 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell128 0
T* 0
cnot bell128 0
H bell128
measure bell128
cz bell128 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell134 0
T* 0
cnot 1 0
T 0
cnot bell134 0
H 1
T* 1
cnot bell142 1
T 1
cnot bell144 1
T* 1
cnot bell142 1
T 1
cnot bell144 1
T 0
cnot bell142 0
T* 0
cnot bell144 0
T 0
cnot bell142 0
T* 0
cnot bell144 0
H 0
T x15
H x15
T x15
H bell148
cnot bell148 bell149
cnot 0 bell149
measure bell149
cnot bell149 bell148
cnot bell148 x15
T* x15
cnot x14 x15
T x15
cnot bell148 x15
H bell148
measure bell148
cz bell148 0
T* x15
cnot x14 x15
H x15
T 0
cnot bell134 0
T* 0
cnot bell134 0
H bell134
measure bell134
cz bell134 x14
H 0
T* 0
cnot bell142 0
T 0
cnot bell144 0
T* 0
cnot bell142 0
H bell142
measure bell142
cz bell142 x13
T 0
cnot bell144 0
H bell144
measure bell144
cz bell144 x3
cnot bell104 x14
T x14
cnot bell104 x14
H bell104
measure bell104
cz bell104 x4
H x14
T x14
cnot x13 x14
T* x14
H bell150
cnot bell150 bell151
cnot x3 bell151
measure bell151
cnot bell151 bell150
cnot bell150 x14
T x14
cnot x13 x14
T* x14
cnot bell150 x14
H x14
cnot bell150 x13
H 6
T 6
cnot x12 6
T* 6
H bell152
cnot bell152 bell153
cnot x2 bell153
measure bell153
cnot bell153 bell152
cnot bell152 6
T 6
cnot x12 6
T* 6
cnot bell152 6
H 6
T 5
H bell154
cnot bell154 bell155
cnot 6 bell155
measure bell155
cnot bell155 bell154
cnot bell154 5
T* 5
H bell156
cnot bell156 bell157
cnot x13 bell157
measure bell157
cnot bell157 bell156
cnot bell156 5
T 5
cnot bell154 5
T* 5
cnot bell156 5
H 5
T 4
cnot 5 4
T* 4
H bell158
cnot bell158 bell159
cnot x14 bell159
measure bell159
cnot bell159 bell158
cnot bell158 4
T 4
cnot 5 4
T* 4
cnot bell158 4
H 4
T 3
cnot 4 3
T* 3
H bell160
cnot bell160 bell161
cnot x15 bell161
measure bell161
cnot bell161 bell160
cnot bell160 3
T 3
cnot 4 3
T* 3
cnot bell160 3
H 3
T 2
cnot 3 2
T* 2
H bell162
cnot bell162 bell163
cnot x16 bell163
measure bell163
cnot bell163 bell162
cnot bell162 2
T 2
cnot 3 2
T* 2
cnot bell162 2
H 2
T 1
H bell164
cnot bell164 bell165
cnot 2 bell165
measure bell165
cnot bell165 bell164
cnot bell164 1
T* 1
H bell166
cnot bell166 bell167
cnot x17 bell167
measure bell167
cnot bell167 bell166
cnot bell166 1
T 1
cnot bell164 1
T* 1
cnot bell166 1
H 1
T 0
cnot 1 0
T* 0
H bell168
cnot bell168 bell169
cnot x18 bell169
measure bell169
cnot bell169 bell168
cnot bell168 0
T 0
cnot 1 0
T* 0
cnot bell168 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot bell168 0
T* 0
cnot 1 0
T 0
cnot bell168 0
H 1
T* 1
cnot bell164 1
T 1
cnot bell166 1
T* 1
cnot bell164 1
H bell164
measure bell164
cz bell164 2
T 1
cnot bell166 1
H 2
T* 2
cnot 3 2
T 2
cnot bell162 2
T* 2
cnot 3 2
T 2
cnot bell162 2
H bell162
measure bell162
cz bell162 x16
H 3
T* 3
cnot 4 3
T 3
cnot bell160 3
T* 3
cnot 4 3
T 3
cnot bell160 3
H 4
T* 4
cnot 5 4
T 4
cnot bell158 4
T* 4
cnot 5 4
T 4
cnot bell158 4
H 5
T* 5
cnot bell154 5
T 5
cnot bell156 5
T* 5
cnot bell154 5
H bell154
measure bell154
cz bell154 6
T 5
cnot bell156 5
H 6
T* 6
cnot x12 6
T 6
cnot bell152 6
T* 6
cnot x12 6
T 6
cnot bell152 6
H bell152
measure bell152
cz bell152 x2
T 5
H bell170
cnot bell170 bell171
cnot x12 bell171
measure bell171
cnot bell171 bell170
cnot bell170 5
T* 5
H bell172
cnot bell172 bell173
cnot x2 bell173
measure bell173
cnot bell173 bell172
cnot bell172 5
T 5
cnot bell170 5
T* 5
cnot bell172 5
H 5
T 4
cnot 5 4
T* 4
cnot bell156 4
T 4
cnot 5 4
T* 4
cnot bell156 4
H 4
T 3
cnot 4 3
T* 3
cnot bell158 3
T 3
cnot 4 3
T* 3
cnot bell158 3
H 3
T 2
cnot 3 2
T* 2
cnot bell160 2
T 2
cnot 3 2
T* 2
cnot bell160 2
H 2
T 1
H bell174
cnot bell174 bell175
cnot 2 bell175
measure bell175
cnot bell175 bell174
cnot bell174 1
T* 1
H bell176
cnot bell176 bell177
cnot x16 bell177
measure bell177
cnot bell177 bell176
cnot bell176 1
T 1
cnot bell174 1
T* 1
cnot bell176 1
H 1
T 0
cnot 1 0
T* 0
cnot bell166 0
T 0
cnot 1 0
T* 0
cnot bell166 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot bell168 x19
T x19
cnot 0 x19
T* x19
cnot bell168 x19
H x19
T 0
cnot bell168 0
T* 0
cnot bell168 0
H bell168
measure bell168
cz bell168 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell166 0
T* 0
cnot 1 0
T 0
cnot bell166 0
H 1
T* 1
cnot bell174 1
T 1
cnot bell176 1
T* 1
cnot bell174 1
H bell174
measure bell174
cz bell174 2
T 1
cnot bell176 1
H 2
T* 2
cnot 3 2
T 2
cnot bell160 2
T* 2
cnot 3 2
T 2
cnot bell160 2
H bell160
measure bell160
cz bell160 x15
H 3
T* 3
cnot 4 3
T 3
cnot bell158 3
T* 3
cnot 4 3
T 3
cnot bell158 3
H 4
T* 4
cnot 5 4
T 4
cnot bell156 4
T* 4
cnot 5 4
T 4
cnot bell156 4
H 5
T* 5
cnot bell170 5
T 5
cnot bell172 5
T* 5
cnot bell170 5
T 5
cnot bell172 5
T 4
cnot bell170 4
T* 4
cnot bell172 4
T 4
cnot bell170 4
T* 4
cnot bell172 4
H 4
T 3
cnot 4 3
T* 3
cnot bell156 3
T 3
cnot 4 3
T* 3
cnot bell156 3
H 3
T 2
cnot 3 2
T* 2
cnot bell158 2
T 2
cnot 3 2
T* 2
cnot bell158 2
H 2
T 1
H bell178
cnot bell178 bell179
cnot 2 bell179
measure bell179
cnot bell179 bell178
cnot bell178 1
T* 1
H bell180
cnot bell180 bell181
cnot x15 bell181
measure bell181
cnot bell181 bell180
cnot bell180 1
T 1
cnot bell178 1
T* 1
cnot bell180 1
H 1
T 0
cnot 1 0
T* 0
cnot bell176 0
T 0
cnot 1 0
T* 0
cnot bell176 0
H 0
T x18
H x18
T x18
H bell182
cnot bell182 bell183
cnot 0 bell183
measure bell183
cnot bell183 bell182
cnot bell182 x18
T* x18
cnot x17 x18
T x18
cnot bell182 x18
H bell182
measure bell182
cz bell182 0
T* x18
cnot x17 x18
H x18
T 0
cnot bell166 0
T* 0
cnot bell166 0
H bell166
measure bell166
cz bell166 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell176 0
T* 0
cnot 1 0
T 0
cnot bell176 0
H bell176
measure bell176
cz bell176 x16
H 1
T* 1
cnot bell178 1
T 1
cnot bell180 1
T* 1
cnot bell178 1
H bell178
measure bell178
cz bell178 2
T 1
cnot bell180 1
H 2
T* 2
cnot 3 2
T 2
cnot bell158 2
T* 2
cnot 3 2
T 2
cnot bell158 2
H bell158
measure bell158
cz bell158 x14
H 3
T* 3
cnot 4 3
T 3
cnot bell156 3
T* 3
cnot 4 3
T 3
cnot bell156 3
H 4
T* 4
cnot bell170 4
T 4
cnot bell172 4
T* 4
cnot bell170 4
T 4
cnot bell172 4
T 3
cnot bell170 3
T* 3
cnot bell172 3
T 3
cnot bell170 3
T* 3
cnot bell172 3
H 3
T 2
cnot 3 2
T* 2
cnot bell156 2
T 2
cnot 3 2
T* 2
cnot bell156 2
H 2
T 1
H bell184
cnot bell184 bell185
cnot 2 bell185
measure bell185
cnot bell185 bell184
cnot bell184 1
T* 1
H bell186
cnot bell186 bell187
cnot x14 bell187
measure bell187
cnot bell187 bell186
cnot bell186 1
T 1
cnot bell184 1
T* 1
cnot bell186 1
H 1
T 0
cnot 1 0
T* 0
cnot bell180 0
T 0
cnot 1 0
T* 0
cnot bell180 0
H 0
T x17
H x17
T x17
H bell188
cnot bell188 bell189
cnot 0 bell189
measure bell189
cnot bell189 bell188
cnot bell188 x17
T* x17
H bell190
cnot bell190 bell191
cnot x16 bell191
measure bell191
cnot bell191 bell190
cnot bell190 x17
T x17
cnot bell188 x17
H bell188
measure bell188
cz bell188 0
T* x17
cnot bell190 x17
H bell190
measure bell190
cz bell190 x16
H x17
T 0
H bell192
cnot bell192 bell193
cnot x16 bell193
measure bell193
cnot bell193 bell192
cnot bell192 0
T* 0
cnot bell192 0
H bell192
measure bell192
cz bell192 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell180 0
T* 0
cnot 1 0
T 0
cnot bell180 0
H 1
T* 1
cnot bell184 1
T 1
cnot bell186 1
T* 1
cnot bell184 1
H bell184
measure bell184
cz bell184 2
T 1
cnot bell186 1
H 2
T* 2
cnot 3 2
T 2
cnot bell156 2
T* 2
cnot 3 2
T 2
cnot bell156 2
H bell156
measure bell156
cz bell156 x13
H 3
T* 3
cnot bell170 3
T 3
cnot bell172 3
T* 3
cnot bell170 3
T 3
cnot bell172 3
T 2
cnot bell170 2
T* 2
cnot bell172 2
T 2
cnot bell170 2
T* 2
cnot bell172 2
H 2
T 1
H bell194
cnot bell194 bell195
cnot 2 bell195
measure bell195
cnot bell195 bell194
cnot bell194 1
T* 1
H bell196
cnot bell196 bell197
cnot x13 bell197
measure bell197
cnot bell197 bell196
cnot bell196 1
T 1
cnot bell194 1
T* 1
cnot bell196 1
H 1
T 0
cnot 1 0
T* 0
cnot bell186 0
T 0
cnot 1 0
T* 0
cnot bell186 0
H 0
T x16
H x16
T x16
H bell198
cnot bell198 bell199
cnot 0 bell199
measure bell199
cnot bell199 bell198
cnot bell198 x16
T* x16
cnot x15 x16
T x16
cnot bell198 x16
H bell198
measure bell198
cz bell198 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell180 0
T* 0
cnot bell180 0
H bell180
measure bell180
cz bell180 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell186 0
T* 0
cnot 1 0
T 0
cnot bell186 0
H 1
T* 1
cnot bell194 1
T 1
cnot bell196 1
T* 1
cnot bell194 1
H bell194
measure bell194
cz bell194 2
T 1
cnot bell196 1
H 2
T* 2
cnot bell170 2
T 2
cnot bell172 2
T* 2
cnot bell170 2
H bell170
measure bell170
cz bell170 x12
T 2
cnot bell172 2
H bell172
measure bell172
cz bell172 x2
T 1
H bell200
cnot bell200 bell201
cnot x12 bell201
measure bell201
cnot bell201 bell200
cnot bell200 1
T* 1
H bell202
cnot bell202 bell203
cnot x2 bell203
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
cnot bell196 0
T 0
cnot 1 0
T* 0
cnot bell196 0
H 0
T x15
H x15
T x15
H bell204
cnot bell204 bell205
cnot 0 bell205
measure bell205
cnot bell205 bell204
cnot bell204 x15
T* x15
cnot x14 x15
T x15
cnot bell204 x15
H bell204
measure bell204
cz bell204 0
T* x15
cnot x14 x15
H x15
T 0
cnot bell186 0
T* 0
cnot bell186 0
H bell186
measure bell186
cz bell186 x14
H 0
T* 0
cnot 1 0
T 0
cnot bell196 0
T* 0
cnot 1 0
T 0
cnot bell196 0
H 1
T* 1
cnot bell200 1
T 1
cnot bell202 1
T* 1
cnot bell200 1
T 1
cnot bell202 1
T 0
cnot bell200 0
T* 0
cnot bell202 0
T 0
cnot bell200 0
T* 0
cnot bell202 0
H 0
T x14
H x14
T x14
H bell206
cnot bell206 bell207
cnot 0 bell207
measure bell207
cnot bell207 bell206
cnot bell206 x14
T* x14
cnot x13 x14
T x14
cnot bell206 x14
H bell206
measure bell206
cz bell206 0
T* x14
cnot x13 x14
H x14
T 0
cnot bell196 0
T* 0
cnot bell196 0
H bell196
measure bell196
cz bell196 x13
H 0
T* 0
cnot bell200 0
T 0
cnot bell202 0
T* 0
cnot bell200 0
H bell200
measure bell200
cz bell200 x12
T 0
cnot bell202 0
H bell202
measure bell202
cz bell202 x2
cnot bell150 x13
T x13
cnot bell150 x13
H bell150
measure bell150
cz bell150 x3
H x13
T x13
H bell208
cnot bell208 bell209
cnot x12 bell209
measure bell209
cnot bell209 bell208
cnot bell208 x13
T* x13
H bell210
cnot bell210 bell211
cnot x2 bell211
measure bell211
cnot bell211 bell210
cnot bell210 x13
T x13
cnot bell208 x13
H bell208
measure bell208
cz bell208 x12
T* x13
cnot bell210 x13
H bell210
measure bell210
cz bell210 x2
H x13
H bell212
cnot bell212 bell213
cnot x2 bell213
measure bell213
cnot bell213 bell212
cnot bell212 x12
H 7
T 7
H bell214
cnot bell214 bell215
cnot x1 bell215
measure bell215
cnot bell215 bell214
cnot bell214 7
T* 7
H bell216
cnot bell216 bell217
cnot x11 bell217
measure bell217
cnot bell217 bell216
cnot bell216 7
T 7
cnot bell214 7
T* 7
cnot bell216 7
H 7
T 6
cnot 7 6
T* 6
cnot x12 6
T 6
cnot 7 6
T* 6
cnot x12 6
H 6
T 5
H bell218
cnot bell218 bell219
cnot 6 bell219
measure bell219
cnot bell219 bell218
cnot bell218 5
T* 5
H bell220
cnot bell220 bell221
cnot x13 bell221
measure bell221
cnot bell221 bell220
cnot bell220 5
T 5
cnot bell218 5
T* 5
cnot bell220 5
H 5
T 4
cnot 5 4
T* 4
H bell222
cnot bell222 bell223
cnot x14 bell223
measure bell223
cnot bell223 bell222
cnot bell222 4
T 4
cnot 5 4
T* 4
cnot bell222 4
H 4
T 3
cnot 4 3
T* 3
H bell224
cnot bell224 bell225
cnot x15 bell225
measure bell225
cnot bell225 bell224
cnot bell224 3
T 3
cnot 4 3
T* 3
cnot bell224 3
H 3
T 2
cnot 3 2
T* 2
H bell226
cnot bell226 bell227
cnot x16 bell227
measure bell227
cnot bell227 bell226
cnot bell226 2
T 2
cnot 3 2
T* 2
cnot bell226 2
H 2
T 1
H bell228
cnot bell228 bell229
cnot 2 bell229
measure bell229
cnot bell229 bell228
cnot bell228 1
T* 1
H bell230
cnot bell230 bell231
cnot x17 bell231
measure bell231
cnot bell231 bell230
cnot bell230 1
T 1
cnot bell228 1
T* 1
cnot bell230 1
H 1
T 0
cnot 1 0
T* 0
H bell232
cnot bell232 bell233
cnot x18 bell233
measure bell233
cnot bell233 bell232
cnot bell232 0
T 0
cnot 1 0
T* 0
cnot bell232 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
H x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot bell232 0
T* 0
cnot 1 0
T 0
cnot bell232 0
H 1
T* 1
cnot bell228 1
T 1
cnot bell230 1
T* 1
cnot bell228 1
H bell228
measure bell228
cz bell228 2
T 1
cnot bell230 1
H 2
T* 2
cnot 3 2
T 2
cnot bell226 2
T* 2
cnot 3 2
T 2
cnot bell226 2
H bell226
measure bell226
cz bell226 x16
H 3
T* 3
cnot 4 3
T 3
cnot bell224 3
T* 3
cnot 4 3
T 3
cnot bell224 3
H 4
T* 4
cnot 5 4
T 4
cnot bell222 4
T* 4
cnot 5 4
T 4
cnot bell222 4
H 5
T* 5
cnot bell218 5
T 5
cnot bell220 5
T* 5
cnot bell218 5
H bell218
measure bell218
cz bell218 6
T 5
cnot bell220 5
H 6
T* 6
cnot 7 6
T 6
cnot x12 6
T* 6
cnot 7 6
T 6
cnot x12 6
H 7
T* 7
cnot bell214 7
T 7
cnot bell216 7
T* 7
cnot bell214 7
T 7
cnot bell216 7
H 7
T 6
cnot bell214 6
T* 6
cnot bell216 6
T 6
cnot bell214 6
T* 6
cnot bell216 6
H 6
T 5
H bell234
cnot bell234 bell235
cnot 6 bell235
measure bell235
cnot bell235 bell234
cnot bell234 5
T* 5
H bell236
cnot bell236 bell237
cnot x12 bell237
measure bell237
cnot bell237 bell236
cnot bell236 5
T 5
cnot bell234 5
T* 5
cnot bell236 5
H 5
T 4
cnot 5 4
T* 4
cnot bell220 4
T 4
cnot 5 4
T* 4
cnot bell220 4
H 4
T 3
cnot 4 3
T* 3
cnot bell222 3
T 3
cnot 4 3
T* 3
cnot bell222 3
H 3
T 2
cnot 3 2
T* 2
cnot bell224 2
T 2
cnot 3 2
T* 2
cnot bell224 2
H 2
T 1
H bell238
cnot bell238 bell239
cnot 2 bell239
measure bell239
cnot bell239 bell238
cnot bell238 1
T* 1
H bell240
cnot bell240 bell241
cnot x16 bell241
measure bell241
cnot bell241 bell240
cnot bell240 1
T 1
cnot bell238 1
T* 1
cnot bell240 1
H 1
T 0
cnot 1 0
T* 0
cnot bell230 0
T 0
cnot 1 0
T* 0
cnot bell230 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot bell232 x19
T x19
cnot 0 x19
T* x19
cnot bell232 x19
H x19
T 0
cnot bell232 0
T* 0
cnot bell232 0
H bell232
measure bell232
cz bell232 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell230 0
T* 0
cnot 1 0
T 0
cnot bell230 0
H 1
T* 1
cnot bell238 1
T 1
cnot bell240 1
T* 1
cnot bell238 1
H bell238
measure bell238
cz bell238 2
T 1
cnot bell240 1
H 2
T* 2
cnot 3 2
T 2
cnot bell224 2
T* 2
cnot 3 2
T 2
cnot bell224 2
H bell224
measure bell224
cz bell224 x15
H 3
T* 3
cnot 4 3
T 3
cnot bell222 3
T* 3
cnot 4 3
T 3
cnot bell222 3
H 4
T* 4
cnot 5 4
T 4
cnot bell220 4
T* 4
cnot 5 4
T 4
cnot bell220 4
H 5
T* 5
cnot bell234 5
T 5
cnot bell236 5
T* 5
cnot bell234 5
H bell234
measure bell234
cz bell234 6
T 5
cnot bell236 5
H 6
T* 6
cnot bell214 6
T 6
cnot bell216 6
T* 6
cnot bell214 6
H bell214
measure bell214
cz bell214 x1
T 6
cnot bell216 6
H bell216
measure bell216
cz bell216 x11
H 6
T 5
H bell242
cnot bell242 bell243
cnot x1 bell243
measure bell243
cnot bell243 bell242
cnot bell242 5
T* 5
H bell244
cnot bell244 bell245
cnot x11 bell245
measure bell245
cnot bell245 bell244
cnot bell244 5
T 5
cnot bell242 5
T* 5
cnot bell244 5
H 5
T 4
cnot 5 4
T* 4
cnot bell236 4
T 4
cnot 5 4
T* 4
cnot bell236 4
H 4
T 3
cnot 4 3
T* 3
cnot bell220 3
T 3
cnot 4 3
T* 3
cnot bell220 3
H 3
T 2
cnot 3 2
T* 2
cnot bell222 2
T 2
cnot 3 2
T* 2
cnot bell222 2
H 2
T 1
H bell246
cnot bell246 bell247
cnot 2 bell247
measure bell247
cnot bell247 bell246
cnot bell246 1
T* 1
H bell248
cnot bell248 bell249
cnot x15 bell249
measure bell249
cnot bell249 bell248
cnot bell248 1
T 1
cnot bell246 1
T* 1
cnot bell248 1
H 1
T 0
cnot 1 0
T* 0
cnot bell240 0
T 0
cnot 1 0
T* 0
cnot bell240 0
H 0
T x18
H x18
T x18
H bell250
cnot bell250 bell251
cnot 0 bell251
measure bell251
cnot bell251 bell250
cnot bell250 x18
T* x18
cnot x17 x18
T x18
cnot bell250 x18
H bell250
measure bell250
cz bell250 0
T* x18
cnot x17 x18
H x18
T 0
cnot bell230 0
T* 0
cnot bell230 0
H bell230
measure bell230
cz bell230 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell240 0
T* 0
cnot 1 0
T 0
cnot bell240 0
H bell240
measure bell240
cz bell240 x16
H 1
T* 1
cnot bell246 1
T 1
cnot bell248 1
T* 1
cnot bell246 1
H bell246
measure bell246
cz bell246 2
T 1
cnot bell248 1
H 2
T* 2
cnot 3 2
T 2
cnot bell222 2
T* 2
cnot 3 2
T 2
cnot bell222 2
H bell222
measure bell222
cz bell222 x14
H 3
T* 3
cnot 4 3
T 3
cnot bell220 3
T* 3
cnot 4 3
T 3
cnot bell220 3
H 4
T* 4
cnot 5 4
T 4
cnot bell236 4
T* 4
cnot 5 4
T 4
cnot bell236 4
H 5
T* 5
cnot bell242 5
T 5
cnot bell244 5
T* 5
cnot bell242 5
T 5
cnot bell244 5
H 5
T 4
cnot bell242 4
T* 4
cnot bell244 4
T 4
cnot bell242 4
T* 4
cnot bell244 4
H 4
T 3
cnot 4 3
T* 3
cnot bell236 3
T 3
cnot 4 3
T* 3
cnot bell236 3
H 3
T 2
cnot 3 2
T* 2
cnot bell220 2
T 2
cnot 3 2
T* 2
cnot bell220 2
H 2
T 1
H bell252
cnot bell252 bell253
cnot 2 bell253
measure bell253
cnot bell253 bell252
cnot bell252 1
T* 1
H bell254
cnot bell254 bell255
cnot x14 bell255
measure bell255
cnot bell255 bell254
cnot bell254 1
T 1
cnot bell252 1
T* 1
cnot bell254 1
H 1
T 0
cnot 1 0
T* 0
cnot bell248 0
T 0
cnot 1 0
T* 0
cnot bell248 0
H 0
T x17
H x17
T x17
H bell256
cnot bell256 bell257
cnot 0 bell257
measure bell257
cnot bell257 bell256
cnot bell256 x17
T* x17
H bell258
cnot bell258 bell259
cnot x16 bell259
measure bell259
cnot bell259 bell258
cnot bell258 x17
T x17
cnot bell256 x17
H bell256
measure bell256
cz bell256 0
T* x17
cnot bell258 x17
H bell258
measure bell258
cz bell258 x16
H x17
T 0
H bell260
cnot bell260 bell261
cnot x16 bell261
measure bell261
cnot bell261 bell260
cnot bell260 0
T* 0
cnot bell260 0
H bell260
measure bell260
cz bell260 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell248 0
T* 0
cnot 1 0
T 0
cnot bell248 0
H 1
T* 1
cnot bell252 1
T 1
cnot bell254 1
T* 1
cnot bell252 1
H bell252
measure bell252
cz bell252 2
T 1
cnot bell254 1
H 2
T* 2
cnot 3 2
T 2
cnot bell220 2
T* 2
cnot 3 2
T 2
cnot bell220 2
H bell220
measure bell220
cz bell220 x13
H 3
T* 3
cnot 4 3
T 3
cnot bell236 3
T* 3
cnot 4 3
T 3
cnot bell236 3
H 4
T* 4
cnot bell242 4
T 4
cnot bell244 4
T* 4
cnot bell242 4
T 4
cnot bell244 4
H 4
T 3
cnot bell242 3
T* 3
cnot bell244 3
T 3
cnot bell242 3
T* 3
cnot bell244 3
H 3
T 2
cnot 3 2
T* 2
cnot bell236 2
T 2
cnot 3 2
T* 2
cnot bell236 2
H 2
T 1
H bell262
cnot bell262 bell263
cnot 2 bell263
measure bell263
cnot bell263 bell262
cnot bell262 1
T* 1
H bell264
cnot bell264 bell265
cnot x13 bell265
measure bell265
cnot bell265 bell264
cnot bell264 1
T 1
cnot bell262 1
T* 1
cnot bell264 1
H 1
T 0
cnot 1 0
T* 0
cnot bell254 0
T 0
cnot 1 0
T* 0
cnot bell254 0
H 0
T x16
H x16
T x16
H bell266
cnot bell266 bell267
cnot 0 bell267
measure bell267
cnot bell267 bell266
cnot bell266 x16
T* x16
cnot x15 x16
T x16
cnot bell266 x16
H bell266
measure bell266
cz bell266 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell248 0
T* 0
cnot bell248 0
H bell248
measure bell248
cz bell248 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell254 0
T* 0
cnot 1 0
T 0
cnot bell254 0
H 1
T* 1
cnot bell262 1
T 1
cnot bell264 1
T* 1
cnot bell262 1
H bell262
measure bell262
cz bell262 2
T 1
cnot bell264 1
H 2
T* 2
cnot 3 2
T 2
cnot bell236 2
T* 2
cnot 3 2
T 2
cnot bell236 2
H bell236
measure bell236
cz bell236 x12
H 3
T* 3
cnot bell242 3
T 3
cnot bell244 3
T* 3
cnot bell242 3
T 3
cnot bell244 3
H 3
T 2
cnot bell242 2
T* 2
cnot bell244 2
T 2
cnot bell242 2
T* 2
cnot bell244 2
H 2
T 1
H bell268
cnot bell268 bell269
cnot 2 bell269
measure bell269
cnot bell269 bell268
cnot bell268 1
T* 1
H bell270
cnot bell270 bell271
cnot x12 bell271
measure bell271
cnot bell271 bell270
cnot bell270 1
T 1
cnot bell268 1
T* 1
cnot bell270 1
H 1
T 0
cnot 1 0
T* 0
cnot bell264 0
T 0
cnot 1 0
T* 0
cnot bell264 0
H 0
T x15
H x15
T x15
H bell272
cnot bell272 bell273
cnot 0 bell273
measure bell273
cnot bell273 bell272
cnot bell272 x15
T* x15
cnot x14 x15
T x15
cnot bell272 x15
H bell272
measure bell272
cz bell272 0
T* x15
cnot x14 x15
H x15
T 0
cnot bell254 0
T* 0
cnot bell254 0
H bell254
measure bell254
cz bell254 x14
H 0
T* 0
cnot 1 0
T 0
cnot bell264 0
T* 0
cnot 1 0
T 0
cnot bell264 0
H 1
T* 1
cnot bell268 1
T 1
cnot bell270 1
T* 1
cnot bell268 1
H bell268
measure bell268
cz bell268 2
T 1
cnot bell270 1
H 2
T* 2
cnot bell242 2
T 2
cnot bell244 2
T* 2
cnot bell242 2
H bell242
measure bell242
cz bell242 x1
T 2
cnot bell244 2
H bell244
measure bell244
cz bell244 x11
H 2
T 1
H bell274
cnot bell274 bell275
cnot x1 bell275
measure bell275
cnot bell275 bell274
cnot bell274 1
T* 1
H bell276
cnot bell276 bell277
cnot x11 bell277
measure bell277
cnot bell277 bell276
cnot bell276 1
T 1
cnot bell274 1
T* 1
cnot bell276 1
H 1
T 0
cnot 1 0
T* 0
cnot bell270 0
T 0
cnot 1 0
T* 0
cnot bell270 0
H 0
T x14
H x14
T x14
H bell278
cnot bell278 bell279
cnot 0 bell279
measure bell279
cnot bell279 bell278
cnot bell278 x14
T* x14
cnot x13 x14
T x14
cnot bell278 x14
H bell278
measure bell278
cz bell278 0
T* x14
cnot x13 x14
H x14
T 0
cnot bell264 0
T* 0
cnot bell264 0
H bell264
measure bell264
cz bell264 x13
H 0
T* 0
cnot 1 0
T 0
cnot bell270 0
T* 0
cnot 1 0
T 0
cnot bell270 0
H bell270
measure bell270
cz bell270 x12
H 1
T* 1
cnot bell274 1
T 1
cnot bell276 1
T* 1
cnot bell274 1
T 1
cnot bell276 1
H 1
T 0
cnot bell274 0
T* 0
cnot bell276 0
T 0
cnot bell274 0
T* 0
cnot bell276 0
H 0
T x13
H x13
T x13
H bell280
cnot bell280 bell281
cnot 0 bell281
measure bell281
cnot bell281 bell280
cnot bell280 x13
T* x13
H bell282
cnot bell282 bell283
cnot x12 bell283
measure bell283
cnot bell283 bell282
cnot bell282 x13
T x13
cnot bell280 x13
H bell280
measure bell280
cz bell280 0
T* x13
cnot bell282 x13
H bell282
measure bell282
cz bell282 x12
H x13
T 0
H bell284
cnot bell284 bell285
cnot x12 bell285
measure bell285
cnot bell285 bell284
cnot bell284 0
T* 0
cnot bell284 0
H bell284
measure bell284
cz bell284 x12
H 0
T* 0
cnot bell274 0
T 0
cnot bell276 0
T* 0
cnot bell274 0
H bell274
measure bell274
cz bell274 x1
T 0
cnot bell276 0
H bell276
measure bell276
cz bell276 x11
H 0
cnot bell212 x12
T x12
cnot bell212 x12
H bell212
measure bell212
cz bell212 x2
H x12
T x12
H bell286
cnot bell286 bell287
cnot x1 bell287
measure bell287
cnot bell287 bell286
cnot bell286 x12
T* x12
H bell288
cnot bell288 bell289
cnot x11 bell289
measure bell289
cnot bell289 bell288
cnot bell288 x12
T x12
cnot bell286 x12
H bell286
measure bell286
cz bell286 x1
T* x12
cnot bell288 x12
H bell288
measure bell288
cz bell288 x11
H x12
T x1
T x11
cnot x1 x11
T* x11
T x2
T x3
T x4
T x5
T x6
T x7
T x8
T x9
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
END
