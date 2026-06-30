# Hyperedge cut (ebits): 66

# Actual ebits used (Synthesis): 128
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^16_mult.qc):
#   Qubits: 48
#   H: 62
#   T: 1792
#   cnot: 1581
#   Depth: 415
#   T depth: 197
# Result (452.446ms):
#   Qubits: 304
#   H: 318
#   S: 8
#   T: 1040
#   Z: 12
#   cnot: 2075
#   cz: 128
#   measure: 256
#   reset: 256
#   swap: 1
#   Depth: 1556
#   T depth: 585


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
.o c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
BEGIN 
H c0
H c1
H c2
H c3
H c4
H c5
H c6
H c7
H c8
H c9
H c10
H c11
H c12
H c13
H c14
T* c0
H bell0
cnot bell0 bell1
cnot a15 bell1
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
T* c0
H bell4
cnot bell4 bell5
cnot a6 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
cnot bell2 c0
T* c0
H bell6
cnot bell6 bell7
cnot b10 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
T c0
cnot bell4 c0
T* c0
H bell8
cnot bell8 bell9
cnot a5 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
cnot bell6 c0
T* c0
H bell10
cnot bell10 bell11
cnot b11 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
T c0
cnot bell8 c0
T* c0
H bell12
cnot bell12 bell13
cnot a4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
cnot bell10 c0
T* c0
H bell14
cnot bell14 bell15
cnot b12 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
T c0
cnot bell12 c0
T* c0
H bell16
cnot bell16 bell17
cnot a3 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
cnot bell14 c0
T* c0
H bell18
cnot bell18 bell19
cnot b13 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c0
T c0
cnot bell16 c0
T* c0
H bell20
cnot bell20 bell21
cnot a2 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c0
cnot bell18 c0
T* c0
H bell22
cnot bell22 bell23
cnot b14 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c0
T c0
cnot bell20 c0
T* c0
H bell24
cnot bell24 bell25
cnot a1 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c0
cnot bell22 c0
T* c0
H bell26
cnot bell26 bell27
cnot b15 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c0
T c0
cnot bell24 c0
T* c0
H bell28
cnot bell28 bell29
cnot a14 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c0
cnot bell26 c0
T* c0
H bell30
cnot bell30 bell31
cnot b2 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c0
T c0
cnot bell28 c0
T* c0
H bell32
cnot bell32 bell33
cnot a13 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c0
cnot bell30 c0
T* c0
H bell34
cnot bell34 bell35
cnot b3 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c0
T c0
cnot bell32 c0
T* c0
H bell36
cnot bell36 bell37
cnot a12 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c0
cnot bell34 c0
T* c0
H bell38
cnot bell38 bell39
cnot b4 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c0
T c0
cnot bell36 c0
T* c0
H bell40
cnot bell40 bell41
cnot a11 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c0
cnot bell38 c0
T* c0
H bell42
cnot bell42 bell43
cnot b5 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c0
T c0
cnot bell40 c0
T* c0
H bell44
cnot bell44 bell45
cnot a10 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c0
cnot bell42 c0
T* c0
H bell46
cnot bell46 bell47
cnot b6 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c0
T c0
cnot bell44 c0
T* c0
H bell48
cnot bell48 bell49
cnot a9 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c0
cnot bell46 c0
T* c0
H bell50
cnot bell50 bell51
cnot b7 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c0
T c0
cnot bell48 c0
T* c0
H bell52
cnot bell52 bell53
cnot a8 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c0
cnot bell50 c0
T* c0
H bell54
cnot bell54 bell55
cnot b8 bell55
measure bell55
cnot bell55 bell54
cnot bell54 c0
T c0
cnot bell52 c0
T* c0
H bell56
cnot bell56 bell57
cnot a7 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c0
cnot bell54 c0
T* c0
H bell58
cnot bell58 bell59
cnot b9 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c0
T c0
cnot bell56 c0
T* c0
cnot bell58 c0
H c0
S* c1
cnot bell56 c1
T* c1
cnot bell6 c1
T c1
cnot bell56 c1
T* c1
cnot bell4 c1
cnot bell6 c1
T* c1
cnot bell10 c1
T c1
cnot bell4 c1
T* c1
cnot bell8 c1
cnot bell10 c1
T* c1
cnot bell14 c1
T c1
cnot bell8 c1
T* c1
cnot bell12 c1
cnot bell14 c1
T* c1
cnot bell18 c1
T c1
cnot bell12 c1
T* c1
cnot bell16 c1
cnot bell18 c1
T* c1
cnot bell22 c1
T c1
cnot bell16 c1
T* c1
cnot bell20 c1
cnot bell22 c1
T* c1
cnot bell26 c1
T c1
cnot bell20 c1
T* c1
cnot bell0 c1
cnot bell26 c1
T* c1
cnot bell30 c1
T c1
cnot bell0 c1
T* c1
cnot bell28 c1
cnot bell30 c1
T* c1
cnot bell34 c1
T c1
cnot bell28 c1
T* c1
cnot bell32 c1
cnot bell34 c1
T* c1
cnot bell38 c1
T c1
cnot bell32 c1
T* c1
cnot bell36 c1
cnot bell38 c1
T* c1
cnot bell42 c1
T c1
cnot bell36 c1
T* c1
cnot bell40 c1
cnot bell42 c1
T* c1
cnot bell46 c1
T c1
cnot bell40 c1
T* c1
cnot bell44 c1
cnot bell46 c1
T* c1
cnot bell50 c1
T c1
cnot bell44 c1
T* c1
cnot bell48 c1
cnot bell50 c1
T* c1
cnot bell54 c1
T c1
cnot bell48 c1
T* c1
cnot bell52 c1
cnot bell54 c1
T* c1
cnot bell58 c1
T c1
cnot bell52 c1
T* c1
cnot bell58 c1
H c1
T c2
Z c2
cnot bell52 c2
T* c2
cnot bell6 c2
T c2
cnot bell52 c2
T* c2
cnot bell56 c2
cnot bell6 c2
T* c2
cnot bell10 c2
T c2
cnot bell56 c2
T* c2
cnot bell4 c2
cnot bell10 c2
T* c2
cnot bell14 c2
T c2
cnot bell4 c2
T* c2
cnot bell8 c2
cnot bell14 c2
T* c2
cnot bell18 c2
T c2
cnot bell8 c2
T* c2
cnot bell12 c2
cnot bell18 c2
T* c2
cnot bell22 c2
T c2
cnot bell12 c2
T* c2
cnot bell16 c2
cnot bell22 c2
T* c2
cnot bell26 c2
T c2
cnot bell16 c2
T* c2
cnot bell0 c2
cnot bell26 c2
T* c2
cnot bell34 c2
T c2
cnot bell0 c2
T* c2
cnot bell28 c2
cnot bell34 c2
T* c2
cnot bell38 c2
T c2
cnot bell28 c2
T* c2
cnot bell32 c2
cnot bell38 c2
T* c2
cnot bell42 c2
T c2
cnot bell32 c2
T* c2
cnot bell36 c2
cnot bell42 c2
T* c2
cnot bell46 c2
T c2
cnot bell36 c2
T* c2
cnot bell40 c2
cnot bell46 c2
T* c2
cnot bell50 c2
T c2
cnot bell40 c2
T* c2
cnot bell44 c2
cnot bell50 c2
T* c2
cnot bell54 c2
T c2
cnot bell44 c2
T* c2
cnot bell48 c2
cnot bell54 c2
T* c2
cnot bell58 c2
T c2
cnot bell48 c2
T* c2
cnot bell58 c2
H c2
Z c3
cnot bell48 c3
T* c3
cnot bell6 c3
T c3
cnot bell48 c3
T* c3
cnot bell52 c3
cnot bell6 c3
T* c3
cnot bell10 c3
T c3
cnot bell52 c3
T* c3
cnot bell56 c3
cnot bell10 c3
T* c3
cnot bell14 c3
T c3
cnot bell56 c3
T* c3
cnot bell4 c3
cnot bell14 c3
T* c3
cnot bell18 c3
T c3
cnot bell4 c3
T* c3
cnot bell8 c3
cnot bell18 c3
T* c3
cnot bell22 c3
T c3
cnot bell8 c3
T* c3
cnot bell12 c3
cnot bell22 c3
T* c3
cnot bell26 c3
T c3
cnot bell12 c3
T* c3
cnot bell0 c3
cnot bell26 c3
T* c3
cnot bell38 c3
T c3
cnot bell0 c3
T* c3
cnot bell28 c3
cnot bell38 c3
T* c3
cnot bell42 c3
T c3
cnot bell28 c3
T* c3
cnot bell32 c3
cnot bell42 c3
T* c3
cnot bell46 c3
T c3
cnot bell32 c3
T* c3
cnot bell36 c3
cnot bell46 c3
T* c3
cnot bell50 c3
T c3
cnot bell36 c3
T* c3
cnot bell40 c3
cnot bell50 c3
T* c3
cnot bell54 c3
T c3
cnot bell40 c3
T* c3
cnot bell44 c3
cnot bell54 c3
T* c3
cnot bell58 c3
T c3
cnot bell44 c3
T* c3
cnot bell58 c3
H c3
T* c4
Z c4
cnot bell44 c4
T* c4
cnot bell6 c4
T c4
cnot bell44 c4
T* c4
cnot bell48 c4
cnot bell6 c4
T* c4
cnot bell10 c4
T c4
cnot bell48 c4
T* c4
cnot bell52 c4
cnot bell10 c4
T* c4
cnot bell14 c4
T c4
cnot bell52 c4
T* c4
cnot bell56 c4
cnot bell14 c4
T* c4
cnot bell18 c4
T c4
cnot bell56 c4
T* c4
cnot bell4 c4
cnot bell18 c4
T* c4
cnot bell22 c4
T c4
cnot bell4 c4
T* c4
cnot bell8 c4
cnot bell22 c4
T* c4
cnot bell26 c4
T c4
cnot bell8 c4
T* c4
cnot bell0 c4
cnot bell26 c4
T* c4
cnot bell42 c4
T c4
cnot bell0 c4
T* c4
cnot bell28 c4
cnot bell42 c4
T* c4
cnot bell46 c4
T c4
cnot bell28 c4
T* c4
cnot bell32 c4
cnot bell46 c4
T* c4
cnot bell50 c4
T c4
cnot bell32 c4
T* c4
cnot bell36 c4
cnot bell50 c4
T* c4
cnot bell54 c4
T c4
cnot bell36 c4
T* c4
cnot bell40 c4
cnot bell54 c4
T* c4
cnot bell58 c4
T c4
cnot bell40 c4
T* c4
cnot bell58 c4
H c4
S c5
cnot bell40 c5
T* c5
cnot bell6 c5
T c5
cnot bell40 c5
T* c5
cnot bell44 c5
cnot bell6 c5
T* c5
cnot bell10 c5
T c5
cnot bell44 c5
T* c5
cnot bell48 c5
cnot bell10 c5
T* c5
cnot bell14 c5
T c5
cnot bell48 c5
T* c5
cnot bell52 c5
cnot bell14 c5
T* c5
cnot bell18 c5
T c5
cnot bell52 c5
T* c5
cnot bell56 c5
cnot bell18 c5
T* c5
cnot bell22 c5
T c5
cnot bell56 c5
T* c5
cnot bell4 c5
cnot bell22 c5
T* c5
cnot bell26 c5
T c5
cnot bell4 c5
T* c5
cnot bell0 c5
cnot bell26 c5
T* c5
cnot bell46 c5
T c5
cnot bell0 c5
T* c5
cnot bell28 c5
cnot bell46 c5
T* c5
cnot bell50 c5
T c5
cnot bell28 c5
T* c5
cnot bell32 c5
cnot bell50 c5
T* c5
cnot bell54 c5
T c5
cnot bell32 c5
T* c5
cnot bell36 c5
cnot bell54 c5
T* c5
cnot bell58 c5
T c5
cnot bell36 c5
T* c5
cnot bell58 c5
H c5
T c6
cnot bell36 c6
T* c6
cnot bell6 c6
T c6
cnot bell36 c6
T* c6
cnot bell40 c6
cnot bell6 c6
T* c6
cnot bell10 c6
T c6
cnot bell40 c6
T* c6
cnot bell44 c6
cnot bell10 c6
T* c6
cnot bell14 c6
T c6
cnot bell44 c6
T* c6
cnot bell48 c6
cnot bell14 c6
T* c6
cnot bell18 c6
T c6
cnot bell48 c6
T* c6
cnot bell52 c6
cnot bell18 c6
T* c6
cnot bell22 c6
T c6
cnot bell52 c6
T* c6
cnot bell56 c6
cnot bell22 c6
T* c6
cnot bell26 c6
T c6
cnot bell56 c6
T* c6
cnot bell0 c6
cnot bell26 c6
T* c6
cnot bell50 c6
T c6
cnot bell0 c6
T* c6
cnot bell28 c6
cnot bell50 c6
T* c6
cnot bell54 c6
T c6
cnot bell28 c6
T* c6
cnot bell32 c6
cnot bell54 c6
T* c6
cnot bell58 c6
T c6
cnot bell32 c6
T* c6
cnot bell58 c6
H c6
cnot bell32 c7
T* c7
cnot bell6 c7
T c7
cnot bell32 c7
T* c7
cnot bell36 c7
cnot bell6 c7
T* c7
cnot bell10 c7
T c7
cnot bell36 c7
T* c7
cnot bell40 c7
cnot bell10 c7
T* c7
cnot bell14 c7
T c7
cnot bell40 c7
T* c7
cnot bell44 c7
cnot bell14 c7
T* c7
cnot bell18 c7
T c7
cnot bell44 c7
T* c7
cnot bell48 c7
cnot bell18 c7
T* c7
cnot bell22 c7
T c7
cnot bell48 c7
T* c7
cnot bell52 c7
cnot bell22 c7
T* c7
cnot bell26 c7
T c7
cnot bell52 c7
T* c7
cnot bell0 c7
cnot bell26 c7
T* c7
cnot bell54 c7
T c7
cnot bell0 c7
T* c7
cnot bell28 c7
cnot bell54 c7
T* c7
cnot bell58 c7
T c7
cnot bell28 c7
T* c7
cnot bell58 c7
H c7
T* c8
cnot bell28 c8
T* c8
cnot bell6 c8
T c8
cnot bell28 c8
H bell28
measure bell28
cz bell28 a14
T* c8
cnot bell32 c8
cnot bell6 c8
T* c8
cnot bell10 c8
T c8
cnot bell32 c8
H bell32
measure bell32
cz bell32 a13
T* c8
cnot bell36 c8
cnot bell10 c8
T* c8
cnot bell14 c8
T c8
cnot bell36 c8
H bell36
measure bell36
cz bell36 a12
T* c8
cnot bell40 c8
cnot bell14 c8
H bell14
measure bell14
cz bell14 b12
T* c8
cnot bell18 c8
T c8
cnot bell40 c8
T* c8
cnot bell44 c8
cnot bell18 c8
H bell18
measure bell18
cz bell18 b13
T* c8
cnot bell22 c8
T c8
cnot bell44 c8
T* c8
cnot bell48 c8
cnot bell22 c8
H bell22
measure bell22
cz bell22 b14
T* c8
cnot bell26 c8
T c8
cnot bell48 c8
H bell48
measure bell48
cz bell48 a9
T* c8
cnot bell0 c8
cnot bell26 c8
H bell26
measure bell26
cz bell26 b15
T* c8
cnot bell58 c8
T c8
cnot bell0 c8
H bell0
measure bell0
cz bell0 a15
T* c8
cnot bell58 c8
H bell58
measure bell58
cz bell58 b9
H c8
S* c9
H bell60
cnot bell60 bell61
cnot a15 bell61
measure bell61
cnot bell61 bell60
cnot bell60 c9
T* c9
cnot b10 c9
T c9
cnot bell60 c9
T* c9
H bell62
cnot bell62 bell63
cnot a14 bell63
measure bell63
cnot bell63 bell62
cnot bell62 c9
cnot b10 c9
T* c9
cnot b11 c9
T c9
cnot bell62 c9
T* c9
H bell64
cnot bell64 bell65
cnot a13 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c9
cnot b11 c9
T* c9
H bell66
cnot bell66 bell67
cnot b12 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c9
T c9
cnot bell64 c9
T* c9
H bell68
cnot bell68 bell69
cnot a12 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c9
cnot bell66 c9
T* c9
H bell70
cnot bell70 bell71
cnot b13 bell71
measure bell71
cnot bell71 bell70
cnot bell70 c9
T c9
cnot bell68 c9
T* c9
cnot a11 c9
cnot bell70 c9
T* c9
H bell72
cnot bell72 bell73
cnot b14 bell73
measure bell73
cnot bell73 bell72
cnot bell72 c9
T c9
cnot a11 c9
T* c9
cnot a10 c9
cnot bell72 c9
T* c9
H bell74
cnot bell74 bell75
cnot b15 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c9
T c9
cnot a10 c9
T* c9
cnot bell74 c9
H c9
T c10
Z c10
cnot bell60 c10
T* c10
cnot b11 c10
T c10
cnot bell60 c10
T* c10
cnot bell62 c10
cnot b11 c10
T* c10
cnot bell66 c10
T c10
cnot bell62 c10
T* c10
cnot bell64 c10
cnot bell66 c10
T* c10
cnot bell70 c10
T c10
cnot bell64 c10
T* c10
cnot bell68 c10
cnot bell70 c10
T* c10
cnot bell72 c10
T c10
cnot bell68 c10
T* c10
cnot a11 c10
cnot bell72 c10
T* c10
cnot bell74 c10
T c10
cnot a11 c10
T* c10
cnot bell74 c10
H c10
Z c11
cnot bell60 c11
T* c11
cnot bell66 c11
T c11
cnot bell60 c11
T* c11
cnot bell62 c11
cnot bell66 c11
T* c11
cnot bell70 c11
T c11
cnot bell62 c11
T* c11
cnot bell64 c11
cnot bell70 c11
T* c11
cnot bell72 c11
T c11
cnot bell64 c11
T* c11
cnot bell68 c11
cnot bell72 c11
T* c11
cnot bell74 c11
T c11
cnot bell68 c11
T* c11
cnot bell74 c11
H c11
T* c12
Z c12
cnot bell60 c12
T* c12
cnot bell70 c12
T c12
cnot bell60 c12
H bell60
measure bell60
cz bell60 a15
T* c12
cnot bell62 c12
cnot bell70 c12
H bell70
measure bell70
cz bell70 b13
T* c12
cnot bell72 c12
T c12
cnot bell62 c12
H bell62
measure bell62
cz bell62 a14
T* c12
cnot bell64 c12
cnot bell72 c12
H bell72
measure bell72
cz bell72 b14
T* c12
cnot bell74 c12
T c12
cnot bell64 c12
H bell64
measure bell64
cz bell64 a13
T* c12
cnot bell74 c12
H bell74
measure bell74
cz bell74 b15
H c12
S c13
H bell76
cnot bell76 bell77
cnot a15 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c13
T* c13
H bell78
cnot bell78 bell79
cnot b14 bell79
measure bell79
cnot bell79 bell78
cnot bell78 c13
T c13
cnot bell76 c13
T* c13
H bell80
cnot bell80 bell81
cnot a14 bell81
measure bell81
cnot bell81 bell80
cnot bell80 c13
cnot bell78 c13
T* c13
H bell82
cnot bell82 bell83
cnot b15 bell83
measure bell83
cnot bell83 bell82
cnot bell82 c13
T c13
cnot bell80 c13
T* c13
cnot bell82 c13
H c13
T c14
cnot bell76 c14
T* c14
cnot bell82 c14
T c14
cnot bell76 c14
T* c14
cnot bell82 c14
H c14
H bell84
cnot bell84 bell85
cnot c11 bell85
measure bell85
cnot bell85 bell84
cnot bell84 c0
H bell84
measure bell84
cz bell84 c11
cnot c13 c0
cnot c14 c0
H bell86
cnot bell86 bell87
cnot c12 bell87
measure bell87
cnot bell87 bell86
cnot bell86 c1
H bell86
measure bell86
cz bell86 c12
cnot c14 c1
H bell88
cnot bell88 bell89
cnot c5 bell89
measure bell89
cnot bell89 bell88
cnot bell88 c10
H bell90
cnot bell90 bell91
cnot c6 bell91
measure bell91
cnot bell91 bell90
cnot bell90 c11
H bell90
measure bell90
cz bell90 c6
H bell92
cnot bell92 bell93
cnot c7 bell93
measure bell93
cnot bell93 bell92
cnot bell92 c10
cnot c9 c11
H bell94
cnot bell94 bell95
cnot c8 bell95
measure bell95
cnot bell95 bell94
cnot bell94 c10
cnot bell94 c11
cnot c2 c13
cnot c3 c14
cnot bell88 c12
H bell88
measure bell88
cz bell88 c5
cnot bell94 c12
H bell94
measure bell94
cz bell94 c8
cnot c9 c12
cnot c5 c3
cnot c6 c3
cnot c7 c2
H bell96
cnot bell96 bell97
cnot c9 bell97
measure bell97
cnot bell97 bell96
cnot bell96 c2
cnot bell96 c3
H bell96
measure bell96
cz bell96 c9
cnot bell92 c9
H bell92
measure bell92
cz bell92 c7
cnot c6 c8
cnot c5 c8
cnot c5 c7
cnot c4 c7
cnot c4 c6
H bell98
cnot bell98 bell99
cnot c6 bell99
measure bell99
cnot bell99 bell98
cnot bell98 c9
H bell98
measure bell98
cz bell98 c6
cnot c3 c5
cnot c8 c2
cnot c2 c5
cnot c8 c15
swap c15 c8
cnot c2 c7
cnot c2 c4
cnot c3 c14
cnot c14 c5
cnot c14 c3
cnot c2 c13
cnot c13 c5
cnot c13 c15
H bell100
cnot bell100 bell101
cnot c12 bell101
measure bell101
cnot bell101 bell100
cnot bell100 c15
cnot bell100 c14
H bell100
measure bell100
cz bell100 c12
cnot c3 c8
cnot c13 c7
cnot c3 c6
cnot c13 c4
cnot c13 c2
H bell102
cnot bell102 bell103
cnot c11 bell103
measure bell103
cnot bell103 bell102
cnot bell102 c13
H bell104
cnot bell104 bell105
cnot c10 bell105
measure bell105
cnot bell105 bell104
cnot bell104 c13
cnot c1 c6
cnot c1 c4
cnot c1 c3
cnot bell104 c15
H bell104
measure bell104
cz bell104 c10
cnot bell102 c14
H bell102
measure bell102
cz bell102 c11
cnot c10 c12
cnot c0 c5
cnot c0 c3
cnot c0 c2
H c0
H c1
H c2
H c3
H c4
H c5
H c6
H c7
H c8
H c9
H c10
H c11
H c12
H c13
H c14
H c15
T c0
H bell106
cnot bell106 bell107
cnot a0 bell107
measure bell107
cnot bell107 bell106
cnot bell106 c0
T* c0
H bell108
cnot bell108 bell109
cnot b0 bell109
measure bell109
cnot bell109 bell108
cnot bell108 c0
T c0
cnot bell106 c0
T* c0
cnot bell108 c0
H c0
S c1
cnot bell24 c1
T* c1
cnot bell108 c1
T c1
cnot bell24 c1
T* c1
cnot bell106 c1
cnot bell108 c1
T* c1
cnot bell2 c1
T c1
cnot bell106 c1
T* c1
cnot bell2 c1
H c1
T* c2
Z c2
cnot bell20 c2
T* c2
cnot bell108 c2
T c2
cnot bell20 c2
T* c2
cnot bell24 c2
cnot bell108 c2
T* c2
cnot bell2 c2
T c2
cnot bell24 c2
T* c2
cnot bell106 c2
cnot bell2 c2
T* c2
cnot bell30 c2
T c2
cnot bell106 c2
T* c2
cnot bell30 c2
H c2
Z c3
cnot bell16 c3
T* c3
cnot bell108 c3
T c3
cnot bell16 c3
T* c3
cnot bell20 c3
cnot bell108 c3
T* c3
cnot bell2 c3
T c3
cnot bell20 c3
T* c3
cnot bell24 c3
cnot bell2 c3
T* c3
cnot bell30 c3
T c3
cnot bell24 c3
T* c3
cnot bell106 c3
cnot bell30 c3
T* c3
cnot bell34 c3
T c3
cnot bell106 c3
T* c3
cnot bell34 c3
H c3
T c4
Z c4
cnot bell12 c4
T* c4
cnot bell108 c4
T c4
cnot bell12 c4
T* c4
cnot bell16 c4
cnot bell108 c4
T* c4
cnot bell2 c4
T c4
cnot bell16 c4
T* c4
cnot bell20 c4
cnot bell2 c4
T* c4
cnot bell30 c4
T c4
cnot bell20 c4
T* c4
cnot bell24 c4
cnot bell30 c4
T* c4
cnot bell34 c4
T c4
cnot bell24 c4
T* c4
cnot bell106 c4
cnot bell34 c4
T* c4
cnot bell38 c4
T c4
cnot bell106 c4
T* c4
cnot bell38 c4
H c4
S* c5
cnot bell8 c5
T* c5
cnot bell108 c5
T c5
cnot bell8 c5
T* c5
cnot bell12 c5
cnot bell108 c5
T* c5
cnot bell2 c5
T c5
cnot bell12 c5
T* c5
cnot bell16 c5
cnot bell2 c5
T* c5
cnot bell30 c5
T c5
cnot bell16 c5
T* c5
cnot bell20 c5
cnot bell30 c5
T* c5
cnot bell34 c5
T c5
cnot bell20 c5
T* c5
cnot bell24 c5
cnot bell34 c5
T* c5
cnot bell38 c5
T c5
cnot bell24 c5
T* c5
cnot bell106 c5
cnot bell38 c5
T* c5
cnot bell42 c5
T c5
cnot bell106 c5
T* c5
cnot bell42 c5
H c5
T* c6
cnot bell4 c6
T* c6
cnot bell108 c6
T c6
cnot bell4 c6
T* c6
cnot bell8 c6
cnot bell108 c6
T* c6
cnot bell2 c6
T c6
cnot bell8 c6
T* c6
cnot bell12 c6
cnot bell2 c6
T* c6
cnot bell30 c6
T c6
cnot bell12 c6
T* c6
cnot bell16 c6
cnot bell30 c6
T* c6
cnot bell34 c6
T c6
cnot bell16 c6
T* c6
cnot bell20 c6
cnot bell34 c6
T* c6
cnot bell38 c6
T c6
cnot bell20 c6
T* c6
cnot bell24 c6
cnot bell38 c6
T* c6
cnot bell42 c6
T c6
cnot bell24 c6
T* c6
cnot bell106 c6
cnot bell42 c6
T* c6
cnot bell46 c6
T c6
cnot bell106 c6
T* c6
cnot bell46 c6
H c6
cnot bell56 c7
T* c7
cnot bell108 c7
T c7
cnot bell56 c7
T* c7
cnot bell4 c7
cnot bell108 c7
T* c7
cnot bell2 c7
T c7
cnot bell4 c7
T* c7
cnot bell8 c7
cnot bell2 c7
T* c7
cnot bell30 c7
T c7
cnot bell8 c7
T* c7
cnot bell12 c7
cnot bell30 c7
T* c7
cnot bell34 c7
T c7
cnot bell12 c7
T* c7
cnot bell16 c7
cnot bell34 c7
T* c7
cnot bell38 c7
T c7
cnot bell16 c7
T* c7
cnot bell20 c7
cnot bell38 c7
T* c7
cnot bell42 c7
T c7
cnot bell20 c7
T* c7
cnot bell24 c7
cnot bell42 c7
T* c7
cnot bell46 c7
T c7
cnot bell24 c7
T* c7
cnot bell106 c7
cnot bell46 c7
T* c7
cnot bell50 c7
T c7
cnot bell106 c7
T* c7
cnot bell50 c7
H c7
T c8
cnot bell52 c8
T* c8
cnot bell108 c8
T c8
cnot bell52 c8
H bell52
measure bell52
cz bell52 a8
T* c8
cnot bell56 c8
cnot bell108 c8
T* c8
cnot bell2 c8
T c8
cnot bell56 c8
H bell56
measure bell56
cz bell56 a7
T* c8
cnot bell4 c8
cnot bell2 c8
T* c8
cnot bell30 c8
T c8
cnot bell4 c8
H bell4
measure bell4
cz bell4 a6
T* c8
cnot bell8 c8
cnot bell30 c8
H bell30
measure bell30
cz bell30 b2
T* c8
cnot bell34 c8
T c8
cnot bell8 c8
H bell8
measure bell8
cz bell8 a5
T* c8
cnot bell12 c8
cnot bell34 c8
H bell34
measure bell34
cz bell34 b3
T* c8
cnot bell38 c8
T c8
cnot bell12 c8
H bell12
measure bell12
cz bell12 a4
T* c8
cnot bell16 c8
cnot bell38 c8
H bell38
measure bell38
cz bell38 b4
T* c8
cnot bell42 c8
T c8
cnot bell16 c8
H bell16
measure bell16
cz bell16 a3
T* c8
cnot bell20 c8
cnot bell42 c8
H bell42
measure bell42
cz bell42 b5
T* c8
cnot bell46 c8
T c8
cnot bell20 c8
H bell20
measure bell20
cz bell20 a2
T* c8
cnot bell24 c8
cnot bell46 c8
H bell46
measure bell46
cz bell46 b6
T* c8
cnot bell50 c8
T c8
cnot bell24 c8
T* c8
cnot bell106 c8
cnot bell50 c8
H bell50
measure bell50
cz bell50 b7
T* c8
cnot bell54 c8
T c8
cnot bell106 c8
T* c8
cnot bell54 c8
H bell54
measure bell54
cz bell54 b8
H c8
S c9
H bell110
cnot bell110 bell111
cnot a9 bell111
measure bell111
cnot bell111 bell110
cnot bell110 c9
T* c9
cnot b0 c9
T c9
cnot bell110 c9
T* c9
H bell112
cnot bell112 bell113
cnot a8 bell113
measure bell113
cnot bell113 bell112
cnot bell112 c9
cnot b0 c9
T* c9
cnot b1 c9
T c9
cnot bell112 c9
T* c9
H bell114
cnot bell114 bell115
cnot a7 bell115
measure bell115
cnot bell115 bell114
cnot bell114 c9
cnot b1 c9
T* c9
H bell116
cnot bell116 bell117
cnot b2 bell117
measure bell117
cnot bell117 bell116
cnot bell116 c9
T c9
cnot bell114 c9
T* c9
H bell118
cnot bell118 bell119
cnot a6 bell119
measure bell119
cnot bell119 bell118
cnot bell118 c9
cnot bell116 c9
T* c9
H bell120
cnot bell120 bell121
cnot b3 bell121
measure bell121
cnot bell121 bell120
cnot bell120 c9
T c9
cnot bell118 c9
T* c9
H bell122
cnot bell122 bell123
cnot a5 bell123
measure bell123
cnot bell123 bell122
cnot bell122 c9
cnot bell120 c9
T* c9
H bell124
cnot bell124 bell125
cnot b4 bell125
measure bell125
cnot bell125 bell124
cnot bell124 c9
T c9
cnot bell122 c9
T* c9
H bell126
cnot bell126 bell127
cnot a4 bell127
measure bell127
cnot bell127 bell126
cnot bell126 c9
cnot bell124 c9
T* c9
H bell128
cnot bell128 bell129
cnot b5 bell129
measure bell129
cnot bell129 bell128
cnot bell128 c9
T c9
cnot bell126 c9
T* c9
H bell130
cnot bell130 bell131
cnot a3 bell131
measure bell131
cnot bell131 bell130
cnot bell130 c9
cnot bell128 c9
T* c9
H bell132
cnot bell132 bell133
cnot b6 bell133
measure bell133
cnot bell133 bell132
cnot bell132 c9
T c9
cnot bell130 c9
T* c9
H bell134
cnot bell134 bell135
cnot a2 bell135
measure bell135
cnot bell135 bell134
cnot bell134 c9
cnot bell132 c9
T* c9
H bell136
cnot bell136 bell137
cnot b7 bell137
measure bell137
cnot bell137 bell136
cnot bell136 c9
T c9
cnot bell134 c9
T* c9
cnot a1 c9
cnot bell136 c9
T* c9
H bell138
cnot bell138 bell139
cnot b8 bell139
measure bell139
cnot bell139 bell138
cnot bell138 c9
T c9
cnot a1 c9
T* c9
cnot a0 c9
cnot bell138 c9
T* c9
H bell140
cnot bell140 bell141
cnot b9 bell141
measure bell141
cnot bell141 bell140
cnot bell140 c9
T c9
cnot a0 c9
T* c9
cnot bell140 c9
H c9
T* c10
Z c10
cnot a10 c10
T* c10
cnot b0 c10
T c10
cnot a10 c10
T* c10
cnot bell110 c10
cnot b0 c10
T* c10
cnot b1 c10
T c10
cnot bell110 c10
T* c10
cnot a0 c10
cnot b1 c10
T* c10
cnot b10 c10
T c10
cnot a0 c10
T* c10
cnot bell112 c10
cnot b10 c10
T* c10
cnot bell116 c10
T c10
cnot bell112 c10
T* c10
cnot bell114 c10
cnot bell116 c10
T* c10
cnot bell120 c10
T c10
cnot bell114 c10
T* c10
cnot bell118 c10
cnot bell120 c10
T* c10
cnot bell124 c10
T c10
cnot bell118 c10
T* c10
cnot bell122 c10
cnot bell124 c10
T* c10
cnot bell128 c10
T c10
cnot bell122 c10
T* c10
cnot bell126 c10
cnot bell128 c10
T* c10
cnot bell132 c10
T c10
cnot bell126 c10
T* c10
cnot bell130 c10
cnot bell132 c10
T* c10
cnot bell136 c10
T c10
cnot bell130 c10
T* c10
cnot bell134 c10
cnot bell136 c10
T* c10
cnot bell138 c10
T c10
cnot bell134 c10
T* c10
cnot a1 c10
cnot bell138 c10
T* c10
cnot bell140 c10
T c10
cnot a1 c10
T* c10
cnot bell140 c10
H c10
Z c11
cnot a11 c11
T* c11
cnot b0 c11
T c11
cnot a11 c11
T* c11
cnot a10 c11
cnot b0 c11
T* c11
cnot b1 c11
T c11
cnot a10 c11
T* c11
cnot a1 c11
cnot b1 c11
T* c11
cnot b10 c11
T c11
cnot a1 c11
T* c11
cnot a0 c11
cnot b10 c11
T* c11
cnot b11 c11
T c11
cnot a0 c11
T* c11
cnot bell110 c11
cnot b11 c11
T* c11
cnot bell116 c11
T c11
cnot bell110 c11
T* c11
cnot bell112 c11
cnot bell116 c11
T* c11
cnot bell120 c11
T c11
cnot bell112 c11
T* c11
cnot bell114 c11
cnot bell120 c11
T* c11
cnot bell124 c11
T c11
cnot bell114 c11
T* c11
cnot bell118 c11
cnot bell124 c11
T* c11
cnot bell128 c11
T c11
cnot bell118 c11
T* c11
cnot bell122 c11
cnot bell128 c11
T* c11
cnot bell132 c11
T c11
cnot bell122 c11
T* c11
cnot bell126 c11
cnot bell132 c11
T* c11
cnot bell136 c11
T c11
cnot bell126 c11
T* c11
cnot bell130 c11
cnot bell136 c11
T* c11
cnot bell138 c11
T c11
cnot bell130 c11
T* c11
cnot bell134 c11
cnot bell138 c11
T* c11
cnot bell140 c11
T c11
cnot bell134 c11
T* c11
cnot bell140 c11
H c11
T c12
Z c12
cnot bell68 c12
T* c12
cnot b0 c12
T c12
cnot bell68 c12
H bell68
measure bell68
cz bell68 a12
T* c12
cnot a11 c12
cnot b0 c12
T* c12
cnot b1 c12
T c12
cnot a11 c12
T* c12
cnot bell134 c12
cnot b1 c12
T* c12
cnot b10 c12
T c12
cnot bell134 c12
H bell134
measure bell134
cz bell134 a2
T* c12
cnot a1 c12
cnot b10 c12
T* c12
cnot b11 c12
T c12
cnot a1 c12
T* c12
cnot a0 c12
cnot b11 c12
T* c12
cnot bell66 c12
T c12
cnot a0 c12
T* c12
cnot a10 c12
cnot bell66 c12
H bell66
measure bell66
cz bell66 b12
T* c12
cnot bell116 c12
T c12
cnot a10 c12
T* c12
cnot bell110 c12
cnot bell116 c12
H bell116
measure bell116
cz bell116 b2
T* c12
cnot bell120 c12
T c12
cnot bell110 c12
H bell110
measure bell110
cz bell110 a9
T* c12
cnot bell112 c12
cnot bell120 c12
H bell120
measure bell120
cz bell120 b3
T* c12
cnot bell124 c12
T c12
cnot bell112 c12
H bell112
measure bell112
cz bell112 a8
T* c12
cnot bell114 c12
cnot bell124 c12
H bell124
measure bell124
cz bell124 b4
T* c12
cnot bell128 c12
T c12
cnot bell114 c12
H bell114
measure bell114
cz bell114 a7
T* c12
cnot bell118 c12
cnot bell128 c12
H bell128
measure bell128
cz bell128 b5
T* c12
cnot bell132 c12
T c12
cnot bell118 c12
H bell118
measure bell118
cz bell118 a6
T* c12
cnot bell122 c12
cnot bell132 c12
H bell132
measure bell132
cz bell132 b6
T* c12
cnot bell136 c12
T c12
cnot bell122 c12
H bell122
measure bell122
cz bell122 a5
T* c12
cnot bell126 c12
cnot bell136 c12
H bell136
measure bell136
cz bell136 b7
T* c12
cnot bell138 c12
T c12
cnot bell126 c12
H bell126
measure bell126
cz bell126 a4
T* c12
cnot bell130 c12
cnot bell138 c12
H bell138
measure bell138
cz bell138 b8
T* c12
cnot bell140 c12
T c12
cnot bell130 c12
H bell130
measure bell130
cz bell130 a3
T* c12
cnot bell140 c12
H bell140
measure bell140
cz bell140 b9
H c12
S* c13
H bell142
cnot bell142 bell143
cnot a13 bell143
measure bell143
cnot bell143 bell142
cnot bell142 c13
T* c13
cnot bell108 c13
T c13
cnot bell142 c13
T* c13
H bell144
cnot bell144 bell145
cnot a12 bell145
measure bell145
cnot bell145 bell144
cnot bell144 c13
cnot bell108 c13
T* c13
cnot bell2 c13
T c13
cnot bell144 c13
T* c13
H bell146
cnot bell146 bell147
cnot a3 bell147
measure bell147
cnot bell147 bell146
cnot bell146 c13
cnot bell2 c13
T* c13
cnot bell6 c13
T c13
cnot bell146 c13
T* c13
H bell148
cnot bell148 bell149
cnot a2 bell149
measure bell149
cnot bell149 bell148
cnot bell148 c13
cnot bell6 c13
T* c13
cnot bell10 c13
T c13
cnot bell148 c13
T* c13
cnot bell24 c13
cnot bell10 c13
T* c13
H bell150
cnot bell150 bell151
cnot b12 bell151
measure bell151
cnot bell151 bell150
cnot bell150 c13
T c13
cnot bell24 c13
T* c13
cnot bell106 c13
cnot bell150 c13
T* c13
H bell152
cnot bell152 bell153
cnot b13 bell153
measure bell153
cnot bell153 bell152
cnot bell152 c13
T c13
cnot bell106 c13
T* c13
cnot bell40 c13
cnot bell152 c13
T* c13
H bell154
cnot bell154 bell155
cnot b2 bell155
measure bell155
cnot bell155 bell154
cnot bell154 c13
T c13
cnot bell40 c13
T* c13
cnot bell44 c13
cnot bell154 c13
T* c13
H bell156
cnot bell156 bell157
cnot b3 bell157
measure bell157
cnot bell157 bell156
cnot bell156 c13
T c13
cnot bell44 c13
T* c13
H bell158
cnot bell158 bell159
cnot a9 bell159
measure bell159
cnot bell159 bell158
cnot bell158 c13
cnot bell156 c13
T* c13
H bell160
cnot bell160 bell161
cnot b4 bell161
measure bell161
cnot bell161 bell160
cnot bell160 c13
T c13
cnot bell158 c13
T* c13
H bell162
cnot bell162 bell163
cnot a8 bell163
measure bell163
cnot bell163 bell162
cnot bell162 c13
cnot bell160 c13
T* c13
H bell164
cnot bell164 bell165
cnot b5 bell165
measure bell165
cnot bell165 bell164
cnot bell164 c13
T c13
cnot bell162 c13
T* c13
H bell166
cnot bell166 bell167
cnot a7 bell167
measure bell167
cnot bell167 bell166
cnot bell166 c13
cnot bell164 c13
T* c13
H bell168
cnot bell168 bell169
cnot b6 bell169
measure bell169
cnot bell169 bell168
cnot bell168 c13
T c13
cnot bell166 c13
T* c13
H bell170
cnot bell170 bell171
cnot a6 bell171
measure bell171
cnot bell171 bell170
cnot bell170 c13
cnot bell168 c13
T* c13
H bell172
cnot bell172 bell173
cnot b7 bell173
measure bell173
cnot bell173 bell172
cnot bell172 c13
T c13
cnot bell170 c13
T* c13
H bell174
cnot bell174 bell175
cnot a5 bell175
measure bell175
cnot bell175 bell174
cnot bell174 c13
cnot bell172 c13
T* c13
H bell176
cnot bell176 bell177
cnot b8 bell177
measure bell177
cnot bell177 bell176
cnot bell176 c13
T c13
cnot bell174 c13
T* c13
H bell178
cnot bell178 bell179
cnot a4 bell179
measure bell179
cnot bell179 bell178
cnot bell178 c13
cnot bell176 c13
T* c13
H bell180
cnot bell180 bell181
cnot b9 bell181
measure bell181
cnot bell181 bell180
cnot bell180 c13
T c13
cnot bell178 c13
T* c13
cnot bell180 c13
H c13
T* c14
cnot bell80 c14
T* c14
cnot bell108 c14
T c14
cnot bell80 c14
T* c14
cnot bell142 c14
cnot bell108 c14
T* c14
cnot bell2 c14
T c14
cnot bell142 c14
T* c14
cnot bell178 c14
cnot bell2 c14
T* c14
cnot bell6 c14
T c14
cnot bell178 c14
T* c14
cnot bell146 c14
cnot bell6 c14
T* c14
cnot bell10 c14
T c14
cnot bell146 c14
T* c14
cnot bell148 c14
cnot bell10 c14
T* c14
cnot bell150 c14
T c14
cnot bell148 c14
T* c14
cnot bell24 c14
cnot bell150 c14
T* c14
cnot bell152 c14
T c14
cnot bell24 c14
T* c14
cnot bell106 c14
cnot bell152 c14
T* c14
cnot bell78 c14
T c14
cnot bell106 c14
T* c14
cnot bell144 c14
cnot bell78 c14
T* c14
cnot bell154 c14
T c14
cnot bell144 c14
T* c14
cnot bell40 c14
cnot bell154 c14
T* c14
cnot bell156 c14
T c14
cnot bell40 c14
T* c14
cnot bell44 c14
cnot bell156 c14
T* c14
cnot bell160 c14
T c14
cnot bell44 c14
T* c14
cnot bell158 c14
cnot bell160 c14
T* c14
cnot bell164 c14
T c14
cnot bell158 c14
T* c14
cnot bell162 c14
cnot bell164 c14
T* c14
cnot bell168 c14
T c14
cnot bell162 c14
T* c14
cnot bell166 c14
cnot bell168 c14
T* c14
cnot bell172 c14
T c14
cnot bell166 c14
T* c14
cnot bell170 c14
cnot bell172 c14
T* c14
cnot bell176 c14
T c14
cnot bell170 c14
T* c14
cnot bell174 c14
cnot bell176 c14
T* c14
cnot bell180 c14
T c14
cnot bell174 c14
T* c14
cnot bell180 c14
H c14
cnot bell76 c15
T* c15
cnot bell108 c15
T c15
cnot bell76 c15
H bell76
measure bell76
cz bell76 a15
T* c15
cnot bell80 c15
cnot bell108 c15
H bell108
measure bell108
cz bell108 b0
T* c15
cnot bell2 c15
T c15
cnot bell80 c15
H bell80
measure bell80
cz bell80 a14
T* c15
cnot bell174 c15
cnot bell2 c15
H bell2
measure bell2
cz bell2 b1
T* c15
cnot bell6 c15
T c15
cnot bell174 c15
H bell174
measure bell174
cz bell174 a5
T* c15
cnot bell178 c15
cnot bell6 c15
H bell6
measure bell6
cz bell6 b10
T* c15
cnot bell10 c15
T c15
cnot bell178 c15
H bell178
measure bell178
cz bell178 a4
T* c15
cnot bell146 c15
cnot bell10 c15
H bell10
measure bell10
cz bell10 b11
T* c15
cnot bell150 c15
T c15
cnot bell146 c15
H bell146
measure bell146
cz bell146 a3
T* c15
cnot bell148 c15
cnot bell150 c15
H bell150
measure bell150
cz bell150 b12
T* c15
cnot bell152 c15
T c15
cnot bell148 c15
H bell148
measure bell148
cz bell148 a2
T* c15
cnot bell24 c15
cnot bell152 c15
H bell152
measure bell152
cz bell152 b13
T* c15
cnot bell78 c15
T c15
cnot bell24 c15
H bell24
measure bell24
cz bell24 a1
T* c15
cnot bell106 c15
cnot bell78 c15
H bell78
measure bell78
cz bell78 b14
T* c15
cnot bell82 c15
T c15
cnot bell106 c15
H bell106
measure bell106
cz bell106 a0
T* c15
cnot bell142 c15
cnot bell82 c15
H bell82
measure bell82
cz bell82 b15
T* c15
cnot bell154 c15
T c15
cnot bell142 c15
H bell142
measure bell142
cz bell142 a13
T* c15
cnot bell144 c15
cnot bell154 c15
H bell154
measure bell154
cz bell154 b2
T* c15
cnot bell156 c15
T c15
cnot bell144 c15
H bell144
measure bell144
cz bell144 a12
T* c15
cnot bell40 c15
cnot bell156 c15
H bell156
measure bell156
cz bell156 b3
T* c15
cnot bell160 c15
T c15
cnot bell40 c15
H bell40
measure bell40
cz bell40 a11
T* c15
cnot bell44 c15
cnot bell160 c15
H bell160
measure bell160
cz bell160 b4
T* c15
cnot bell164 c15
T c15
cnot bell44 c15
H bell44
measure bell44
cz bell44 a10
T* c15
cnot bell158 c15
cnot bell164 c15
H bell164
measure bell164
cz bell164 b5
T* c15
cnot bell168 c15
T c15
cnot bell158 c15
H bell158
measure bell158
cz bell158 a9
T* c15
cnot bell162 c15
cnot bell168 c15
H bell168
measure bell168
cz bell168 b6
T* c15
cnot bell172 c15
T c15
cnot bell162 c15
H bell162
measure bell162
cz bell162 a8
T* c15
cnot bell166 c15
cnot bell172 c15
H bell172
measure bell172
cz bell172 b7
T* c15
cnot bell176 c15
T c15
cnot bell166 c15
H bell166
measure bell166
cz bell166 a7
T* c15
cnot bell170 c15
cnot bell176 c15
H bell176
measure bell176
cz bell176 b8
T* c15
cnot bell180 c15
T c15
cnot bell170 c15
H bell170
measure bell170
cz bell170 a6
T* c15
cnot bell180 c15
H bell180
measure bell180
cz bell180 b9
H c15
cnot a0 b0
T* b0
cnot a1 b0
cnot a0 b0
T* b0
cnot a0 b1
T* b1
cnot a1 b1
cnot a0 b1
T* b1
cnot b0 a10
cnot a1 a10
T* a10
cnot b1 a10
cnot b0 a10
T* a10
cnot a0 b10
T* b10
cnot a1 b10
cnot a0 b10
T* b10
cnot b1 b10
cnot a10 b10
T* b10
cnot b0 a11
cnot a1 a11
T* a11
cnot b1 a11
cnot b0 a11
T* a11
cnot b10 a11
cnot a10 a11
T* a11
cnot a0 b11
T* b11
cnot a1 b11
cnot a0 b11
T* b11
cnot b1 b11
cnot a10 b11
T* b11
cnot b10 b11
cnot a11 b11
T* b11
H bell182
cnot bell182 bell183
cnot b0 bell183
measure bell183
cnot bell183 bell182
cnot bell182 a12
H bell184
cnot bell184 bell185
cnot a1 bell185
measure bell185
cnot bell185 bell184
cnot bell184 a12
T* a12
H bell186
cnot bell186 bell187
cnot b1 bell187
measure bell187
cnot bell187 bell186
cnot bell186 a12
cnot bell182 a12
T* a12
H bell188
cnot bell188 bell189
cnot b10 bell189
measure bell189
cnot bell189 bell188
cnot bell188 a12
H bell190
cnot bell190 bell191
cnot a10 bell191
measure bell191
cnot bell191 bell190
cnot bell190 a12
T* a12
H bell192
cnot bell192 bell193
cnot b11 bell193
measure bell193
cnot bell193 bell192
cnot bell192 a12
H bell194
cnot bell194 bell195
cnot a11 bell195
measure bell195
cnot bell195 bell194
cnot bell194 a12
T* a12
H bell196
cnot bell196 bell197
cnot a0 bell197
measure bell197
cnot bell197 bell196
cnot bell196 b12
T* b12
cnot bell184 b12
cnot bell196 b12
T* b12
cnot bell186 b12
cnot bell190 b12
T* b12
cnot bell188 b12
cnot bell194 b12
T* b12
cnot bell192 b12
cnot a12 b12
T* b12
cnot bell182 a13
cnot bell184 a13
T* a13
cnot bell186 a13
cnot bell182 a13
T* a13
cnot bell188 a13
cnot bell190 a13
T* a13
cnot bell192 a13
cnot bell194 a13
T* a13
cnot b12 a13
cnot a12 a13
T* a13
cnot bell196 b13
T* b13
cnot bell184 b13
cnot bell196 b13
T* b13
cnot bell186 b13
cnot bell190 b13
T* b13
cnot bell188 b13
cnot bell194 b13
T* b13
cnot bell192 b13
cnot a12 b13
T* b13
cnot b12 b13
cnot a13 b13
T* b13
cnot bell182 a14
cnot bell184 a14
T* a14
cnot bell186 a14
cnot bell182 a14
T* a14
cnot bell188 a14
cnot bell190 a14
T* a14
cnot bell192 a14
cnot bell194 a14
T* a14
cnot b12 a14
cnot a12 a14
T* a14
cnot b13 a14
cnot a13 a14
T* a14
cnot bell196 b14
T* b14
cnot bell184 b14
cnot bell196 b14
T* b14
cnot bell186 b14
cnot bell190 b14
T* b14
cnot bell188 b14
cnot bell194 b14
T* b14
cnot bell192 b14
cnot a12 b14
T* b14
cnot b12 b14
cnot a13 b14
T* b14
cnot b13 b14
cnot a14 b14
T* b14
cnot bell182 a15
cnot bell184 a15
T* a15
cnot bell186 a15
cnot bell182 a15
T* a15
cnot bell188 a15
cnot bell190 a15
T* a15
cnot bell192 a15
cnot bell194 a15
T* a15
cnot b12 a15
cnot a12 a15
T* a15
cnot b13 a15
cnot a13 a15
T* a15
cnot b14 a15
cnot a14 a15
T* a15
cnot bell196 b15
T* b15
cnot bell184 b15
cnot bell196 b15
T* b15
cnot bell186 b15
cnot bell190 b15
T* b15
cnot bell188 b15
cnot bell194 b15
T* b15
cnot bell192 b15
cnot a12 b15
T* b15
cnot b12 b15
cnot a13 b15
T* b15
cnot b13 b15
cnot a14 b15
T* b15
cnot b14 b15
cnot a15 b15
T* b15
cnot bell182 a2
cnot bell184 a2
T* a2
cnot bell186 a2
cnot bell182 a2
T* a2
cnot bell188 a2
cnot bell190 a2
T* a2
cnot bell192 a2
cnot bell194 a2
T* a2
cnot b12 a2
cnot a12 a2
T* a2
cnot b13 a2
cnot a13 a2
T* a2
cnot b14 a2
cnot a14 a2
T* a2
cnot b15 a2
cnot a15 a2
T* a2
cnot bell196 b2
T* b2
cnot bell184 b2
cnot bell196 b2
T* b2
cnot bell186 b2
cnot bell190 b2
T* b2
cnot bell188 b2
cnot bell194 b2
T* b2
cnot bell192 b2
cnot a12 b2
T* b2
cnot b12 b2
cnot a13 b2
T* b2
cnot b13 b2
cnot a14 b2
T* b2
cnot b14 b2
cnot a15 b2
T* b2
cnot b15 b2
cnot a2 b2
T* b2
cnot bell182 a3
cnot bell184 a3
T* a3
cnot bell186 a3
cnot bell182 a3
H bell182
measure bell182
cz bell182 b0
T* a3
cnot bell188 a3
cnot bell190 a3
T* a3
cnot bell192 a3
cnot bell194 a3
T* a3
cnot b12 a3
cnot a12 a3
T* a3
cnot b13 a3
cnot a13 a3
T* a3
cnot b14 a3
cnot a14 a3
T* a3
cnot b15 a3
cnot a15 a3
T* a3
cnot b2 a3
cnot a2 a3
T* a3
cnot bell196 b3
T* b3
cnot bell184 b3
H bell184
measure bell184
cz bell184 a1
cnot bell196 b3
H bell196
measure bell196
cz bell196 a0
T* b3
cnot bell186 b3
H bell186
measure bell186
cz bell186 b1
cnot bell190 b3
H bell190
measure bell190
cz bell190 a10
T* b3
cnot bell188 b3
H bell188
measure bell188
cz bell188 b10
cnot bell194 b3
H bell194
measure bell194
cz bell194 a11
T* b3
cnot bell192 b3
H bell192
measure bell192
cz bell192 b11
cnot a12 b3
T* b3
cnot b12 b3
cnot a13 b3
T* b3
cnot b13 b3
cnot a14 b3
T* b3
cnot b14 b3
cnot a15 b3
T* b3
cnot b15 b3
cnot a2 b3
T* b3
cnot b2 b3
cnot a3 b3
T* b3
H bell198
cnot bell198 bell199
cnot b0 bell199
measure bell199
cnot bell199 bell198
cnot bell198 a4
H bell200
cnot bell200 bell201
cnot a1 bell201
measure bell201
cnot bell201 bell200
cnot bell200 a4
T* a4
H bell202
cnot bell202 bell203
cnot b1 bell203
measure bell203
cnot bell203 bell202
cnot bell202 a4
cnot bell198 a4
T* a4
H bell204
cnot bell204 bell205
cnot b10 bell205
measure bell205
cnot bell205 bell204
cnot bell204 a4
H bell206
cnot bell206 bell207
cnot a10 bell207
measure bell207
cnot bell207 bell206
cnot bell206 a4
T* a4
H bell208
cnot bell208 bell209
cnot b11 bell209
measure bell209
cnot bell209 bell208
cnot bell208 a4
H bell210
cnot bell210 bell211
cnot a11 bell211
measure bell211
cnot bell211 bell210
cnot bell210 a4
T* a4
H bell212
cnot bell212 bell213
cnot b12 bell213
measure bell213
cnot bell213 bell212
cnot bell212 a4
H bell214
cnot bell214 bell215
cnot a12 bell215
measure bell215
cnot bell215 bell214
cnot bell214 a4
T* a4
H bell216
cnot bell216 bell217
cnot b13 bell217
measure bell217
cnot bell217 bell216
cnot bell216 a4
H bell218
cnot bell218 bell219
cnot a13 bell219
measure bell219
cnot bell219 bell218
cnot bell218 a4
T* a4
H bell220
cnot bell220 bell221
cnot b14 bell221
measure bell221
cnot bell221 bell220
cnot bell220 a4
H bell222
cnot bell222 bell223
cnot a14 bell223
measure bell223
cnot bell223 bell222
cnot bell222 a4
T* a4
H bell224
cnot bell224 bell225
cnot b15 bell225
measure bell225
cnot bell225 bell224
cnot bell224 a4
H bell226
cnot bell226 bell227
cnot a15 bell227
measure bell227
cnot bell227 bell226
cnot bell226 a4
T* a4
H bell228
cnot bell228 bell229
cnot b2 bell229
measure bell229
cnot bell229 bell228
cnot bell228 a4
H bell230
cnot bell230 bell231
cnot a2 bell231
measure bell231
cnot bell231 bell230
cnot bell230 a4
T* a4
H bell232
cnot bell232 bell233
cnot b3 bell233
measure bell233
cnot bell233 bell232
cnot bell232 a4
H bell234
cnot bell234 bell235
cnot a3 bell235
measure bell235
cnot bell235 bell234
cnot bell234 a4
T* a4
H bell236
cnot bell236 bell237
cnot a0 bell237
measure bell237
cnot bell237 bell236
cnot bell236 b4
T* b4
cnot bell200 b4
cnot bell236 b4
T* b4
cnot bell202 b4
cnot bell206 b4
T* b4
cnot bell204 b4
cnot bell210 b4
T* b4
cnot bell208 b4
cnot bell214 b4
T* b4
cnot bell212 b4
cnot bell218 b4
T* b4
cnot bell216 b4
cnot bell222 b4
T* b4
cnot bell220 b4
cnot bell226 b4
T* b4
cnot bell224 b4
cnot bell230 b4
T* b4
cnot bell228 b4
cnot bell234 b4
T* b4
cnot bell232 b4
cnot a4 b4
T* b4
cnot bell198 a5
cnot bell200 a5
T* a5
cnot bell202 a5
cnot bell198 a5
T* a5
cnot bell204 a5
cnot bell206 a5
T* a5
cnot bell208 a5
cnot bell210 a5
T* a5
cnot bell212 a5
cnot bell214 a5
T* a5
cnot bell216 a5
cnot bell218 a5
T* a5
cnot bell220 a5
cnot bell222 a5
T* a5
cnot bell224 a5
cnot bell226 a5
T* a5
cnot bell228 a5
cnot bell230 a5
T* a5
cnot bell232 a5
cnot bell234 a5
T* a5
cnot b4 a5
cnot a4 a5
T* a5
cnot bell236 b5
T* b5
cnot bell200 b5
cnot bell236 b5
T* b5
cnot bell202 b5
cnot bell206 b5
T* b5
cnot bell204 b5
cnot bell210 b5
T* b5
cnot bell208 b5
cnot bell214 b5
T* b5
cnot bell212 b5
cnot bell218 b5
T* b5
cnot bell216 b5
cnot bell222 b5
T* b5
cnot bell220 b5
cnot bell226 b5
T* b5
cnot bell224 b5
cnot bell230 b5
T* b5
cnot bell228 b5
cnot bell234 b5
T* b5
cnot bell232 b5
cnot a4 b5
T* b5
cnot b4 b5
cnot a5 b5
T* b5
cnot bell198 a6
cnot bell200 a6
T* a6
cnot bell202 a6
cnot bell198 a6
T* a6
cnot bell204 a6
cnot bell206 a6
T* a6
cnot bell208 a6
cnot bell210 a6
T* a6
cnot bell212 a6
cnot bell214 a6
T* a6
cnot bell216 a6
cnot bell218 a6
T* a6
cnot bell220 a6
cnot bell222 a6
T* a6
cnot bell224 a6
cnot bell226 a6
T* a6
cnot bell228 a6
cnot bell230 a6
T* a6
cnot bell232 a6
cnot bell234 a6
T* a6
cnot b4 a6
cnot a4 a6
T* a6
cnot b5 a6
cnot a5 a6
T* a6
cnot bell236 b6
T* b6
cnot bell200 b6
cnot bell236 b6
T* b6
cnot bell202 b6
cnot bell206 b6
T* b6
cnot bell204 b6
cnot bell210 b6
T* b6
cnot bell208 b6
cnot bell214 b6
T* b6
cnot bell212 b6
cnot bell218 b6
T* b6
cnot bell216 b6
cnot bell222 b6
T* b6
cnot bell220 b6
cnot bell226 b6
T* b6
cnot bell224 b6
cnot bell230 b6
T* b6
cnot bell228 b6
cnot bell234 b6
T* b6
cnot bell232 b6
cnot a4 b6
T* b6
cnot b4 b6
cnot a5 b6
T* b6
cnot b5 b6
cnot a6 b6
T* b6
cnot bell198 a7
cnot bell200 a7
T* a7
cnot bell202 a7
cnot bell198 a7
T* a7
cnot bell204 a7
cnot bell206 a7
T* a7
cnot bell208 a7
cnot bell210 a7
T* a7
cnot bell212 a7
cnot bell214 a7
T* a7
cnot bell216 a7
cnot bell218 a7
T* a7
cnot bell220 a7
cnot bell222 a7
T* a7
cnot bell224 a7
cnot bell226 a7
T* a7
cnot bell228 a7
cnot bell230 a7
T* a7
cnot bell232 a7
cnot bell234 a7
T* a7
cnot b4 a7
cnot a4 a7
T* a7
cnot b5 a7
cnot a5 a7
T* a7
cnot b6 a7
cnot a6 a7
T* a7
cnot bell236 b7
T* b7
cnot bell200 b7
cnot bell236 b7
T* b7
cnot bell202 b7
cnot bell206 b7
T* b7
cnot bell204 b7
cnot bell210 b7
T* b7
cnot bell208 b7
cnot bell214 b7
T* b7
cnot bell212 b7
cnot bell218 b7
T* b7
cnot bell216 b7
cnot bell222 b7
T* b7
cnot bell220 b7
cnot bell226 b7
T* b7
cnot bell224 b7
cnot bell230 b7
T* b7
cnot bell228 b7
cnot bell234 b7
T* b7
cnot bell232 b7
cnot a4 b7
T* b7
cnot b4 b7
cnot a5 b7
T* b7
cnot b5 b7
cnot a6 b7
T* b7
cnot b6 b7
cnot a7 b7
T* b7
cnot bell198 a8
cnot bell200 a8
T* a8
cnot bell202 a8
cnot bell198 a8
T* a8
cnot bell204 a8
cnot bell206 a8
T* a8
cnot bell208 a8
cnot bell210 a8
T* a8
cnot bell212 a8
cnot bell214 a8
T* a8
cnot bell216 a8
cnot bell218 a8
T* a8
cnot bell220 a8
cnot bell222 a8
T* a8
cnot bell224 a8
cnot bell226 a8
T* a8
cnot bell228 a8
cnot bell230 a8
T* a8
cnot bell232 a8
cnot bell234 a8
T* a8
cnot b4 a8
cnot a4 a8
T* a8
cnot b5 a8
cnot a5 a8
T* a8
cnot b6 a8
cnot a6 a8
T* a8
cnot b7 a8
cnot a7 a8
T* a8
cnot bell236 b8
T* b8
cnot bell200 b8
cnot bell236 b8
T* b8
cnot bell202 b8
cnot bell206 b8
T* b8
cnot bell204 b8
cnot bell210 b8
T* b8
cnot bell208 b8
cnot bell214 b8
T* b8
cnot bell212 b8
cnot bell218 b8
T* b8
cnot bell216 b8
cnot bell222 b8
T* b8
cnot bell220 b8
cnot bell226 b8
T* b8
cnot bell224 b8
cnot bell230 b8
T* b8
cnot bell228 b8
cnot bell234 b8
T* b8
cnot bell232 b8
cnot a4 b8
T* b8
cnot b4 b8
cnot a5 b8
T* b8
cnot b5 b8
cnot a6 b8
T* b8
cnot b6 b8
cnot a7 b8
T* b8
cnot b7 b8
cnot a8 b8
T* b8
cnot bell198 a9
cnot bell200 a9
T* a9
cnot bell202 a9
cnot bell198 a9
H bell198
measure bell198
cz bell198 b0
T* a9
cnot bell204 a9
cnot bell206 a9
T* a9
cnot bell208 a9
cnot bell210 a9
T* a9
cnot bell212 a9
cnot bell214 a9
T* a9
cnot bell216 a9
cnot bell218 a9
T* a9
cnot bell220 a9
cnot bell222 a9
T* a9
cnot bell224 a9
cnot bell226 a9
T* a9
cnot bell228 a9
cnot bell230 a9
T* a9
cnot bell232 a9
cnot bell234 a9
T* a9
cnot b4 a9
cnot a4 a9
T* a9
cnot b5 a9
cnot a5 a9
T* a9
cnot b6 a9
cnot a6 a9
T* a9
cnot b7 a9
cnot a7 a9
T* a9
cnot b8 a9
cnot a8 a9
T* a9
cnot bell236 b9
T* b9
cnot bell200 b9
H bell200
measure bell200
cz bell200 a1
cnot bell236 b9
H bell236
measure bell236
cz bell236 a0
T* b9
cnot bell202 b9
H bell202
measure bell202
cz bell202 b1
cnot bell206 b9
H bell206
measure bell206
cz bell206 a10
T* b9
cnot bell204 b9
H bell204
measure bell204
cz bell204 b10
cnot bell210 b9
H bell210
measure bell210
cz bell210 a11
T* b9
cnot bell208 b9
H bell208
measure bell208
cz bell208 b11
cnot bell214 b9
H bell214
measure bell214
cz bell214 a12
T* b9
cnot bell212 b9
H bell212
measure bell212
cz bell212 b12
cnot bell218 b9
H bell218
measure bell218
cz bell218 a13
T* b9
cnot bell216 b9
H bell216
measure bell216
cz bell216 b13
cnot bell222 b9
H bell222
measure bell222
cz bell222 a14
T* b9
cnot bell220 b9
H bell220
measure bell220
cz bell220 b14
cnot bell226 b9
H bell226
measure bell226
cz bell226 a15
T* b9
cnot bell224 b9
H bell224
measure bell224
cz bell224 b15
cnot bell230 b9
H bell230
measure bell230
cz bell230 a2
T* b9
cnot bell228 b9
H bell228
measure bell228
cz bell228 b2
cnot bell234 b9
H bell234
measure bell234
cz bell234 a3
T* b9
cnot bell232 b9
cnot a4 b9
T* b9
cnot b4 b9
cnot a5 b9
T* b9
cnot b5 b9
cnot a6 b9
T* b9
cnot b6 b9
cnot a7 b9
T* b9
cnot b7 b9
cnot a8 b9
T* b9
cnot b8 b9
cnot a9 b9
T* b9
cnot b1 a10
cnot b10 a11
H bell238
cnot bell238 bell239
cnot b11 bell239
measure bell239
cnot bell239 bell238
cnot bell238 a12
H bell238
measure bell238
cz bell238 b11
cnot b12 a13
cnot b13 a14
cnot b14 a15
cnot b15 a2
cnot b2 a3
cnot bell232 a4
H bell232
measure bell232
cz bell232 b3
cnot b4 a5
cnot b5 a6
cnot b6 a7
cnot b7 a8
cnot b8 a9
cnot a9 b9
cnot a7 a8
cnot a6 a8
cnot a6 a7
cnot a8 b9
cnot a8 b8
cnot a7 b7
cnot a6 b6
cnot a8 a9
cnot a4 a5
H bell240
cnot bell240 bell241
cnot a3 bell241
measure bell241
cnot bell241 bell240
cnot bell240 a5
cnot bell240 a4
H bell240
measure bell240
cz bell240 a3
cnot a5 b9
cnot a5 b8
cnot a5 b7
cnot a5 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a5 a9
cnot a5 a8
cnot a5 a7
cnot a5 a6
cnot a15 a2
cnot a14 a2
cnot a14 a15
H bell242
cnot bell242 bell243
cnot a2 bell243
measure bell243
cnot bell243 bell242
cnot bell242 b9
cnot bell242 b8
cnot bell242 b7
cnot bell242 b6
cnot bell242 b5
cnot bell242 b4
cnot a2 b3
cnot a2 b2
cnot a15 b15
cnot a14 b14
cnot bell242 a9
cnot bell242 a8
cnot bell242 a7
cnot bell242 a6
cnot bell242 a5
cnot bell242 a4
H bell242
measure bell242
cz bell242 a2
cnot a2 a3
cnot a12 a13
H bell244
cnot bell244 bell245
cnot a11 bell245
measure bell245
cnot bell245 bell244
cnot bell244 a13
cnot bell244 a12
H bell244
measure bell244
cz bell244 a11
H bell246
cnot bell246 bell247
cnot a13 bell247
measure bell247
cnot bell247 bell246
cnot bell246 b9
cnot bell246 b8
cnot bell246 b7
cnot bell246 b6
cnot bell246 b5
cnot bell246 b4
cnot a13 b3
cnot a13 b2
cnot a13 b15
cnot a13 b14
cnot a13 b13
cnot a12 b12
cnot a11 b11
cnot bell246 a9
cnot bell246 a8
cnot bell246 a7
cnot bell246 a6
cnot bell246 a5
cnot bell246 a4
H bell246
measure bell246
cz bell246 a13
cnot a13 a3
cnot a13 a2
cnot a13 a15
cnot a13 a14
cnot a1 a10
H bell248
cnot bell248 bell249
cnot a10 bell249
measure bell249
cnot bell249 bell248
cnot bell248 b9
cnot bell248 b8
cnot bell248 b7
cnot bell248 b6
cnot bell248 b5
cnot bell248 b4
H bell248
measure bell248
cz bell248 a10
H bell250
cnot bell250 bell251
cnot a10 bell251
measure bell251
cnot bell251 bell250
cnot bell250 b3
cnot bell250 b2
cnot bell250 b15
cnot bell250 b14
cnot bell250 b13
cnot bell250 b12
H bell250
measure bell250
cz bell250 a10
cnot a10 b11
cnot a10 b10
cnot a1 b1
cnot a1 b0
H bell252
cnot bell252 bell253
cnot a10 bell253
measure bell253
cnot bell253 bell252
cnot bell252 a9
cnot bell252 a8
cnot bell252 a7
cnot bell252 a6
cnot bell252 a5
cnot bell252 a4
H bell252
measure bell252
cz bell252 a10
H bell254
cnot bell254 bell255
cnot a10 bell255
measure bell255
cnot bell255 bell254
cnot bell254 a3
cnot bell254 a2
cnot bell254 a15
cnot bell254 a14
cnot bell254 a13
cnot bell254 a12
H bell254
measure bell254
cz bell254 a10
cnot a10 a11
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
END
