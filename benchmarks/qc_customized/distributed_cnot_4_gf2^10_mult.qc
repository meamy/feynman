# Hyperedge cut (ebits): 35

# Actual ebits used (Synthesis): 89
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^10_mult.qc):
#   Qubits: 30
#   H: 38
#   T: 700
#   cnot: 609
#   Depth: 246
#   T depth: 119
# Result (110.615ms):
#   Qubits: 208
#   H: 216
#   S: 25
#   T: 410
#   Z: 6
#   cnot: 915
#   cz: 89
#   measure: 178
#   reset: 178
#   Depth: 365
#   T depth: 109


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c9
.o a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
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
T c0
H bell0
cnot bell0 bell1
cnot a9 bell1
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
cnot a8 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
cnot bell2 c0
T* c0
H bell6
cnot bell6 bell7
cnot b2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
T c0
cnot bell4 c0
T* c0
H bell8
cnot bell8 bell9
cnot a7 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
cnot bell6 c0
T* c0
H bell10
cnot bell10 bell11
cnot b3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
T c0
cnot bell8 c0
T* c0
H bell12
cnot bell12 bell13
cnot a6 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
cnot bell10 c0
T* c0
H bell14
cnot bell14 bell15
cnot b4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
T c0
cnot bell12 c0
T* c0
H bell16
cnot bell16 bell17
cnot a5 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
cnot bell14 c0
T* c0
H bell18
cnot bell18 bell19
cnot b5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c0
T c0
cnot bell16 c0
T* c0
H bell20
cnot bell20 bell21
cnot a4 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c0
cnot bell18 c0
T* c0
H bell22
cnot bell22 bell23
cnot b6 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c0
T c0
cnot bell20 c0
T* c0
H bell24
cnot bell24 bell25
cnot a3 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c0
cnot bell22 c0
T* c0
H bell26
cnot bell26 bell27
cnot b7 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c0
T c0
cnot bell24 c0
T* c0
H bell28
cnot bell28 bell29
cnot a2 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c0
cnot bell26 c0
T* c0
H bell30
cnot bell30 bell31
cnot b8 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c0
T c0
cnot bell28 c0
T* c0
H bell32
cnot bell32 bell33
cnot a1 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c0
cnot bell30 c0
T* c0
H bell34
cnot bell34 bell35
cnot b9 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c0
T c0
cnot bell32 c0
T* c0
cnot bell34 c0
H c0
cnot bell0 c1
T* c1
cnot bell6 c1
T c1
cnot bell0 c1
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
cnot bell24 c1
cnot bell26 c1
T* c1
cnot bell30 c1
T c1
cnot bell24 c1
T* c1
cnot bell28 c1
cnot bell30 c1
T* c1
cnot bell34 c1
T c1
cnot bell28 c1
T* c1
cnot bell34 c1
H c1
T* c2
cnot bell0 c2
T* c2
cnot bell10 c2
T c2
cnot bell0 c2
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
cnot bell20 c2
cnot bell26 c2
T* c2
cnot bell30 c2
T c2
cnot bell20 c2
T* c2
cnot bell24 c2
cnot bell30 c2
T* c2
cnot bell34 c2
T c2
cnot bell24 c2
T* c2
cnot bell34 c2
H c2
S* c3
cnot bell0 c3
T* c3
cnot bell14 c3
T c3
cnot bell0 c3
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
cnot bell16 c3
cnot bell26 c3
T* c3
cnot bell30 c3
T c3
cnot bell16 c3
T* c3
cnot bell20 c3
cnot bell30 c3
T* c3
cnot bell34 c3
T c3
cnot bell20 c3
T* c3
cnot bell34 c3
H c3
T c4
Z c4
cnot bell0 c4
T* c4
cnot bell18 c4
T c4
cnot bell0 c4
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
cnot bell12 c4
cnot bell26 c4
T* c4
cnot bell30 c4
T c4
cnot bell12 c4
T* c4
cnot bell16 c4
cnot bell30 c4
T* c4
cnot bell34 c4
T c4
cnot bell16 c4
T* c4
cnot bell34 c4
H c4
Z c5
cnot bell0 c5
T* c5
cnot bell22 c5
T c5
cnot bell0 c5
H bell0
measure bell0
cz bell0 a9
T* c5
cnot bell4 c5
cnot bell22 c5
H bell22
measure bell22
cz bell22 b6
T* c5
cnot bell26 c5
T c5
cnot bell4 c5
H bell4
measure bell4
cz bell4 a8
T* c5
cnot bell8 c5
cnot bell26 c5
H bell26
measure bell26
cz bell26 b7
T* c5
cnot bell30 c5
T c5
cnot bell8 c5
H bell8
measure bell8
cz bell8 a7
T* c5
cnot bell12 c5
cnot bell30 c5
H bell30
measure bell30
cz bell30 b8
T* c5
cnot bell34 c5
T c5
cnot bell12 c5
H bell12
measure bell12
cz bell12 a6
T* c5
cnot bell34 c5
H bell34
measure bell34
cz bell34 b9
H c5
T* c6
Z c6
H bell36
cnot bell36 bell37
cnot a9 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c6
T* c6
H bell38
cnot bell38 bell39
cnot b7 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c6
T c6
cnot bell36 c6
H bell36
measure bell36
cz bell36 a9
T* c6
H bell40
cnot bell40 bell41
cnot a8 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c6
cnot bell38 c6
H bell38
measure bell38
cz bell38 b7
T* c6
H bell42
cnot bell42 bell43
cnot b8 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c6
T c6
cnot bell40 c6
H bell40
measure bell40
cz bell40 a8
T* c6
H bell44
cnot bell44 bell45
cnot a7 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c6
cnot bell42 c6
H bell42
measure bell42
cz bell42 b8
T* c6
H bell46
cnot bell46 bell47
cnot b9 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c6
T c6
cnot bell44 c6
H bell44
measure bell44
cz bell44 a7
T* c6
cnot bell46 c6
H bell46
measure bell46
cz bell46 b9
H c6
S c7
H bell48
cnot bell48 bell49
cnot a9 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c7
T* c7
H bell50
cnot bell50 bell51
cnot b8 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c7
T c7
cnot bell48 c7
T* c7
H bell52
cnot bell52 bell53
cnot a8 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c7
cnot bell50 c7
T* c7
H bell54
cnot bell54 bell55
cnot b9 bell55
measure bell55
cnot bell55 bell54
cnot bell54 c7
T c7
cnot bell52 c7
T* c7
cnot bell54 c7
H c7
T c8
cnot bell48 c8
T* c8
cnot bell54 c8
T c8
cnot bell48 c8
H bell48
measure bell48
cz bell48 a9
T* c8
cnot bell54 c8
H bell54
measure bell54
cz bell54 b9
H c8
cnot c7 c0
cnot c8 c1
cnot c6 c9
cnot c5 c8
cnot c4 c7
H bell56
cnot bell56 bell57
cnot c3 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c6
H bell56
measure bell56
cz bell56 c3
cnot c2 c5
cnot c1 c4
cnot c0 c3
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
T c0
H bell58
cnot bell58 bell59
cnot a0 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c0
T* c0
H bell60
cnot bell60 bell61
cnot b0 bell61
measure bell61
cnot bell61 bell60
cnot bell60 c0
T c0
cnot bell58 c0
T* c0
cnot bell60 c0
H c0
S c1
cnot bell32 c1
T* c1
cnot bell60 c1
T c1
cnot bell32 c1
T* c1
cnot bell58 c1
cnot bell60 c1
T* c1
cnot bell2 c1
T c1
cnot bell58 c1
T* c1
cnot bell2 c1
H c1
T* c2
Z c2
cnot bell28 c2
T* c2
cnot bell60 c2
T c2
cnot bell28 c2
T* c2
cnot bell32 c2
cnot bell60 c2
T* c2
cnot bell2 c2
T c2
cnot bell32 c2
T* c2
cnot bell58 c2
cnot bell2 c2
T* c2
cnot bell6 c2
T c2
cnot bell58 c2
T* c2
cnot bell6 c2
H c2
Z c3
cnot bell24 c3
T* c3
cnot bell60 c3
T c3
cnot bell24 c3
T* c3
cnot bell28 c3
cnot bell60 c3
T* c3
cnot bell2 c3
T c3
cnot bell28 c3
T* c3
cnot bell32 c3
cnot bell2 c3
T* c3
cnot bell6 c3
T c3
cnot bell32 c3
T* c3
cnot bell58 c3
cnot bell6 c3
T* c3
cnot bell10 c3
T c3
cnot bell58 c3
T* c3
cnot bell10 c3
H c3
T c4
Z c4
cnot bell20 c4
T* c4
cnot bell60 c4
T c4
cnot bell20 c4
T* c4
cnot bell24 c4
cnot bell60 c4
T* c4
cnot bell2 c4
T c4
cnot bell24 c4
T* c4
cnot bell28 c4
cnot bell2 c4
T* c4
cnot bell6 c4
T c4
cnot bell28 c4
T* c4
cnot bell32 c4
cnot bell6 c4
T* c4
cnot bell10 c4
T c4
cnot bell32 c4
T* c4
cnot bell58 c4
cnot bell10 c4
T* c4
cnot bell14 c4
T c4
cnot bell58 c4
T* c4
cnot bell14 c4
H c4
S* c5
cnot bell16 c5
T* c5
cnot bell60 c5
T c5
cnot bell16 c5
H bell16
measure bell16
cz bell16 a5
T* c5
cnot bell20 c5
cnot bell60 c5
T* c5
cnot bell2 c5
T c5
cnot bell20 c5
H bell20
measure bell20
cz bell20 a4
T* c5
cnot bell24 c5
cnot bell2 c5
T* c5
cnot bell6 c5
T c5
cnot bell24 c5
H bell24
measure bell24
cz bell24 a3
T* c5
cnot bell28 c5
cnot bell6 c5
H bell6
measure bell6
cz bell6 b2
T* c5
cnot bell10 c5
T c5
cnot bell28 c5
H bell28
measure bell28
cz bell28 a2
T* c5
cnot bell32 c5
cnot bell10 c5
H bell10
measure bell10
cz bell10 b3
T* c5
cnot bell14 c5
T c5
cnot bell32 c5
T* c5
cnot bell58 c5
cnot bell14 c5
H bell14
measure bell14
cz bell14 b4
T* c5
cnot bell18 c5
T c5
cnot bell58 c5
T* c5
cnot bell18 c5
H bell18
measure bell18
cz bell18 b5
H c5
T* c6
H bell62
cnot bell62 bell63
cnot a6 bell63
measure bell63
cnot bell63 bell62
cnot bell62 c6
T* c6
cnot b0 c6
T c6
cnot bell62 c6
H bell62
measure bell62
cz bell62 a6
T* c6
H bell64
cnot bell64 bell65
cnot a5 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c6
cnot b0 c6
T* c6
cnot b1 c6
T c6
cnot bell64 c6
H bell64
measure bell64
cz bell64 a5
T* c6
H bell66
cnot bell66 bell67
cnot a4 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c6
cnot b1 c6
T* c6
H bell68
cnot bell68 bell69
cnot b2 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c6
T c6
cnot bell66 c6
H bell66
measure bell66
cz bell66 a4
T* c6
H bell70
cnot bell70 bell71
cnot a3 bell71
measure bell71
cnot bell71 bell70
cnot bell70 c6
cnot bell68 c6
H bell68
measure bell68
cz bell68 b2
T* c6
H bell72
cnot bell72 bell73
cnot b3 bell73
measure bell73
cnot bell73 bell72
cnot bell72 c6
T c6
cnot bell70 c6
H bell70
measure bell70
cz bell70 a3
T* c6
H bell74
cnot bell74 bell75
cnot a2 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c6
cnot bell72 c6
H bell72
measure bell72
cz bell72 b3
T* c6
H bell76
cnot bell76 bell77
cnot b4 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c6
T c6
cnot bell74 c6
H bell74
measure bell74
cz bell74 a2
T* c6
cnot a1 c6
cnot bell76 c6
H bell76
measure bell76
cz bell76 b4
T* c6
H bell78
cnot bell78 bell79
cnot b5 bell79
measure bell79
cnot bell79 bell78
cnot bell78 c6
T c6
cnot a1 c6
T* c6
cnot a0 c6
cnot bell78 c6
H bell78
measure bell78
cz bell78 b5
T* c6
H bell80
cnot bell80 bell81
cnot b6 bell81
measure bell81
cnot bell81 bell80
cnot bell80 c6
T c6
cnot a0 c6
T* c6
cnot bell80 c6
H bell80
measure bell80
cz bell80 b6
H c6
H bell82
cnot bell82 bell83
cnot a7 bell83
measure bell83
cnot bell83 bell82
cnot bell82 c7
T* c7
cnot bell60 c7
T c7
cnot bell82 c7
T* c7
H bell84
cnot bell84 bell85
cnot a6 bell85
measure bell85
cnot bell85 bell84
cnot bell84 c7
cnot bell60 c7
T* c7
cnot bell2 c7
T c7
cnot bell84 c7
T* c7
H bell86
cnot bell86 bell87
cnot a5 bell87
measure bell87
cnot bell87 bell86
cnot bell86 c7
cnot bell2 c7
T* c7
H bell88
cnot bell88 bell89
cnot b2 bell89
measure bell89
cnot bell89 bell88
cnot bell88 c7
T c7
cnot bell86 c7
T* c7
H bell90
cnot bell90 bell91
cnot a4 bell91
measure bell91
cnot bell91 bell90
cnot bell90 c7
cnot bell88 c7
T* c7
H bell92
cnot bell92 bell93
cnot b3 bell93
measure bell93
cnot bell93 bell92
cnot bell92 c7
T c7
cnot bell90 c7
T* c7
H bell94
cnot bell94 bell95
cnot a3 bell95
measure bell95
cnot bell95 bell94
cnot bell94 c7
cnot bell92 c7
T* c7
H bell96
cnot bell96 bell97
cnot b4 bell97
measure bell97
cnot bell97 bell96
cnot bell96 c7
T c7
cnot bell94 c7
T* c7
H bell98
cnot bell98 bell99
cnot a2 bell99
measure bell99
cnot bell99 bell98
cnot bell98 c7
cnot bell96 c7
T* c7
H bell100
cnot bell100 bell101
cnot b5 bell101
measure bell101
cnot bell101 bell100
cnot bell100 c7
T c7
cnot bell98 c7
T* c7
cnot bell32 c7
cnot bell100 c7
T* c7
H bell102
cnot bell102 bell103
cnot b6 bell103
measure bell103
cnot bell103 bell102
cnot bell102 c7
T c7
cnot bell32 c7
T* c7
cnot bell58 c7
cnot bell102 c7
T* c7
H bell104
cnot bell104 bell105
cnot b7 bell105
measure bell105
cnot bell105 bell104
cnot bell104 c7
T c7
cnot bell58 c7
T* c7
cnot bell104 c7
H c7
T c8
cnot bell52 c8
T* c8
cnot bell60 c8
T c8
cnot bell52 c8
H bell52
measure bell52
cz bell52 a8
T* c8
cnot bell82 c8
cnot bell60 c8
H bell60
measure bell60
cz bell60 b0
T* c8
cnot bell2 c8
T c8
cnot bell82 c8
H bell82
measure bell82
cz bell82 a7
T* c8
cnot bell84 c8
cnot bell2 c8
H bell2
measure bell2
cz bell2 b1
T* c8
cnot bell88 c8
T c8
cnot bell84 c8
H bell84
measure bell84
cz bell84 a6
T* c8
cnot bell86 c8
cnot bell88 c8
H bell88
measure bell88
cz bell88 b2
T* c8
cnot bell92 c8
T c8
cnot bell86 c8
H bell86
measure bell86
cz bell86 a5
T* c8
cnot bell90 c8
cnot bell92 c8
H bell92
measure bell92
cz bell92 b3
T* c8
cnot bell96 c8
T c8
cnot bell90 c8
H bell90
measure bell90
cz bell90 a4
T* c8
cnot bell94 c8
cnot bell96 c8
H bell96
measure bell96
cz bell96 b4
T* c8
cnot bell100 c8
T c8
cnot bell94 c8
H bell94
measure bell94
cz bell94 a3
T* c8
cnot bell98 c8
cnot bell100 c8
H bell100
measure bell100
cz bell100 b5
T* c8
cnot bell102 c8
T c8
cnot bell98 c8
H bell98
measure bell98
cz bell98 a2
T* c8
cnot bell32 c8
cnot bell102 c8
H bell102
measure bell102
cz bell102 b6
T* c8
cnot bell104 c8
T c8
cnot bell32 c8
H bell32
measure bell32
cz bell32 a1
T* c8
cnot bell58 c8
cnot bell104 c8
H bell104
measure bell104
cz bell104 b7
T* c8
cnot bell50 c8
T c8
cnot bell58 c8
H bell58
measure bell58
cz bell58 a0
T* c8
cnot bell50 c8
H bell50
measure bell50
cz bell50 b8
H c8
S c9
H bell106
cnot bell106 bell107
cnot a9 bell107
measure bell107
cnot bell107 bell106
cnot bell106 c9
T* c9
cnot b0 c9
T c9
cnot bell106 c9
H bell106
measure bell106
cz bell106 a9
T* c9
H bell108
cnot bell108 bell109
cnot a8 bell109
measure bell109
cnot bell109 bell108
cnot bell108 c9
cnot b0 c9
T* c9
cnot b1 c9
T c9
cnot bell108 c9
H bell108
measure bell108
cz bell108 a8
T* c9
H bell110
cnot bell110 bell111
cnot a7 bell111
measure bell111
cnot bell111 bell110
cnot bell110 c9
cnot b1 c9
T* c9
H bell112
cnot bell112 bell113
cnot b2 bell113
measure bell113
cnot bell113 bell112
cnot bell112 c9
T c9
cnot bell110 c9
H bell110
measure bell110
cz bell110 a7
T* c9
H bell114
cnot bell114 bell115
cnot a6 bell115
measure bell115
cnot bell115 bell114
cnot bell114 c9
cnot bell112 c9
H bell112
measure bell112
cz bell112 b2
T* c9
H bell116
cnot bell116 bell117
cnot b3 bell117
measure bell117
cnot bell117 bell116
cnot bell116 c9
T c9
cnot bell114 c9
H bell114
measure bell114
cz bell114 a6
T* c9
H bell118
cnot bell118 bell119
cnot a5 bell119
measure bell119
cnot bell119 bell118
cnot bell118 c9
cnot bell116 c9
H bell116
measure bell116
cz bell116 b3
T* c9
H bell120
cnot bell120 bell121
cnot b4 bell121
measure bell121
cnot bell121 bell120
cnot bell120 c9
T c9
cnot bell118 c9
H bell118
measure bell118
cz bell118 a5
T* c9
H bell122
cnot bell122 bell123
cnot a4 bell123
measure bell123
cnot bell123 bell122
cnot bell122 c9
cnot bell120 c9
H bell120
measure bell120
cz bell120 b4
T* c9
H bell124
cnot bell124 bell125
cnot b5 bell125
measure bell125
cnot bell125 bell124
cnot bell124 c9
T c9
cnot bell122 c9
H bell122
measure bell122
cz bell122 a4
T* c9
H bell126
cnot bell126 bell127
cnot a3 bell127
measure bell127
cnot bell127 bell126
cnot bell126 c9
cnot bell124 c9
H bell124
measure bell124
cz bell124 b5
T* c9
H bell128
cnot bell128 bell129
cnot b6 bell129
measure bell129
cnot bell129 bell128
cnot bell128 c9
T c9
cnot bell126 c9
H bell126
measure bell126
cz bell126 a3
T* c9
H bell130
cnot bell130 bell131
cnot a2 bell131
measure bell131
cnot bell131 bell130
cnot bell130 c9
cnot bell128 c9
H bell128
measure bell128
cz bell128 b6
T* c9
H bell132
cnot bell132 bell133
cnot b7 bell133
measure bell133
cnot bell133 bell132
cnot bell132 c9
T c9
cnot bell130 c9
H bell130
measure bell130
cz bell130 a2
T* c9
cnot a1 c9
cnot bell132 c9
H bell132
measure bell132
cz bell132 b7
T* c9
H bell134
cnot bell134 bell135
cnot b8 bell135
measure bell135
cnot bell135 bell134
cnot bell134 c9
T c9
cnot a1 c9
T* c9
cnot a0 c9
cnot bell134 c9
H bell134
measure bell134
cz bell134 b8
T* c9
H bell136
cnot bell136 bell137
cnot b9 bell137
measure bell137
cnot bell137 bell136
cnot bell136 c9
T c9
cnot a0 c9
T* c9
cnot bell136 c9
H bell136
measure bell136
cz bell136 b9
H c9
S a0
S a1
S b0
cnot a0 b0
T* b0
cnot a1 b0
cnot a0 b0
T* b0
S b1
cnot a0 b1
T* b1
cnot a1 b1
cnot a0 b1
T* b1
S a2
H bell138
cnot bell138 bell139
cnot b0 bell139
measure bell139
cnot bell139 bell138
cnot bell138 a2
H bell140
cnot bell140 bell141
cnot a1 bell141
measure bell141
cnot bell141 bell140
cnot bell140 a2
T* a2
H bell142
cnot bell142 bell143
cnot b1 bell143
measure bell143
cnot bell143 bell142
cnot bell142 a2
cnot bell138 a2
T* a2
S b2
H bell144
cnot bell144 bell145
cnot a0 bell145
measure bell145
cnot bell145 bell144
cnot bell144 b2
T* b2
cnot bell140 b2
cnot bell144 b2
T* b2
cnot bell142 b2
cnot a2 b2
T* b2
S a3
cnot bell138 a3
cnot bell140 a3
T* a3
cnot bell142 a3
cnot bell138 a3
T* a3
cnot b2 a3
cnot a2 a3
T* a3
S b3
cnot bell144 b3
T* b3
cnot bell140 b3
cnot bell144 b3
T* b3
cnot bell142 b3
cnot a2 b3
T* b3
cnot b2 b3
cnot a3 b3
T* b3
S a4
cnot bell138 a4
cnot bell140 a4
T* a4
cnot bell142 a4
cnot bell138 a4
T* a4
cnot b2 a4
cnot a2 a4
T* a4
cnot b3 a4
cnot a3 a4
T* a4
S b4
cnot bell144 b4
T* b4
cnot bell140 b4
cnot bell144 b4
T* b4
cnot bell142 b4
cnot a2 b4
T* b4
cnot b2 b4
cnot a3 b4
T* b4
cnot b3 b4
cnot a4 b4
T* b4
S a5
cnot bell138 a5
cnot bell140 a5
T* a5
cnot bell142 a5
cnot bell138 a5
H bell138
measure bell138
cz bell138 b0
T* a5
cnot b2 a5
cnot a2 a5
T* a5
cnot b3 a5
cnot a3 a5
T* a5
cnot b4 a5
cnot a4 a5
T* a5
S b5
cnot bell144 b5
T* b5
cnot bell140 b5
H bell140
measure bell140
cz bell140 a1
cnot bell144 b5
H bell144
measure bell144
cz bell144 a0
T* b5
cnot bell142 b5
H bell142
measure bell142
cz bell142 b1
cnot a2 b5
T* b5
cnot b2 b5
cnot a3 b5
T* b5
cnot b3 b5
cnot a4 b5
T* b5
cnot b4 b5
cnot a5 b5
T* b5
S a6
H bell146
cnot bell146 bell147
cnot b0 bell147
measure bell147
cnot bell147 bell146
cnot bell146 a6
H bell148
cnot bell148 bell149
cnot a1 bell149
measure bell149
cnot bell149 bell148
cnot bell148 a6
T* a6
H bell150
cnot bell150 bell151
cnot b1 bell151
measure bell151
cnot bell151 bell150
cnot bell150 a6
cnot bell146 a6
T* a6
H bell152
cnot bell152 bell153
cnot b2 bell153
measure bell153
cnot bell153 bell152
cnot bell152 a6
H bell154
cnot bell154 bell155
cnot a2 bell155
measure bell155
cnot bell155 bell154
cnot bell154 a6
T* a6
H bell156
cnot bell156 bell157
cnot b3 bell157
measure bell157
cnot bell157 bell156
cnot bell156 a6
H bell158
cnot bell158 bell159
cnot a3 bell159
measure bell159
cnot bell159 bell158
cnot bell158 a6
T* a6
H bell160
cnot bell160 bell161
cnot b4 bell161
measure bell161
cnot bell161 bell160
cnot bell160 a6
H bell162
cnot bell162 bell163
cnot a4 bell163
measure bell163
cnot bell163 bell162
cnot bell162 a6
T* a6
H bell164
cnot bell164 bell165
cnot b5 bell165
measure bell165
cnot bell165 bell164
cnot bell164 a6
H bell166
cnot bell166 bell167
cnot a5 bell167
measure bell167
cnot bell167 bell166
cnot bell166 a6
T* a6
S b6
H bell168
cnot bell168 bell169
cnot a0 bell169
measure bell169
cnot bell169 bell168
cnot bell168 b6
T* b6
cnot bell148 b6
cnot bell168 b6
T* b6
cnot bell150 b6
cnot bell154 b6
T* b6
cnot bell152 b6
cnot bell158 b6
T* b6
cnot bell156 b6
cnot bell162 b6
T* b6
cnot bell160 b6
cnot bell166 b6
T* b6
cnot bell164 b6
cnot a6 b6
T* b6
S a7
cnot bell146 a7
cnot bell148 a7
T* a7
cnot bell150 a7
cnot bell146 a7
T* a7
cnot bell152 a7
cnot bell154 a7
T* a7
cnot bell156 a7
cnot bell158 a7
T* a7
cnot bell160 a7
cnot bell162 a7
T* a7
cnot bell164 a7
cnot bell166 a7
T* a7
cnot b6 a7
cnot a6 a7
T* a7
S b7
cnot bell168 b7
T* b7
cnot bell148 b7
cnot bell168 b7
T* b7
cnot bell150 b7
cnot bell154 b7
T* b7
cnot bell152 b7
cnot bell158 b7
T* b7
cnot bell156 b7
cnot bell162 b7
T* b7
cnot bell160 b7
cnot bell166 b7
T* b7
cnot bell164 b7
cnot a6 b7
T* b7
cnot b6 b7
cnot a7 b7
T* b7
S a8
cnot bell146 a8
cnot bell148 a8
T* a8
cnot bell150 a8
cnot bell146 a8
T* a8
cnot bell152 a8
cnot bell154 a8
T* a8
cnot bell156 a8
cnot bell158 a8
T* a8
cnot bell160 a8
cnot bell162 a8
T* a8
cnot bell164 a8
cnot bell166 a8
T* a8
cnot b6 a8
cnot a6 a8
T* a8
cnot b7 a8
cnot a7 a8
T* a8
S b8
cnot bell168 b8
T* b8
cnot bell148 b8
cnot bell168 b8
T* b8
cnot bell150 b8
cnot bell154 b8
T* b8
cnot bell152 b8
cnot bell158 b8
T* b8
cnot bell156 b8
cnot bell162 b8
T* b8
cnot bell160 b8
cnot bell166 b8
T* b8
cnot bell164 b8
cnot a6 b8
T* b8
cnot b6 b8
cnot a7 b8
T* b8
cnot b7 b8
cnot a8 b8
T* b8
S a9
cnot bell146 a9
cnot bell148 a9
T* a9
cnot bell150 a9
cnot bell146 a9
H bell146
measure bell146
cz bell146 b0
T* a9
cnot bell152 a9
cnot bell154 a9
T* a9
cnot bell156 a9
cnot bell158 a9
T* a9
cnot bell160 a9
cnot bell162 a9
T* a9
cnot bell164 a9
cnot bell166 a9
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
S b9
cnot bell168 b9
T* b9
cnot bell148 b9
H bell148
measure bell148
cz bell148 a1
cnot bell168 b9
H bell168
measure bell168
cz bell168 a0
T* b9
cnot bell150 b9
H bell150
measure bell150
cz bell150 b1
cnot bell154 b9
H bell154
measure bell154
cz bell154 a2
T* b9
cnot bell152 b9
H bell152
measure bell152
cz bell152 b2
cnot bell158 b9
H bell158
measure bell158
cz bell158 a3
T* b9
cnot bell156 b9
H bell156
measure bell156
cz bell156 b3
cnot bell162 b9
H bell162
measure bell162
cz bell162 a4
T* b9
cnot bell160 b9
H bell160
measure bell160
cz bell160 b4
cnot bell166 b9
H bell166
measure bell166
cz bell166 a5
T* b9
cnot bell164 b9
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
H bell170
cnot bell170 bell171
cnot b1 bell171
measure bell171
cnot bell171 bell170
cnot bell170 a2
H bell170
measure bell170
cz bell170 b1
cnot b2 a3
cnot b3 a4
cnot b4 a5
cnot bell164 a6
H bell164
measure bell164
cz bell164 b5
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
cnot a3 a5
cnot a3 a4
H bell172
cnot bell172 bell173
cnot a5 bell173
measure bell173
cnot bell173 bell172
cnot bell172 b9
cnot bell172 b8
cnot bell172 b7
cnot bell172 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot bell172 a9
cnot bell172 a8
cnot bell172 a7
cnot bell172 a6
H bell172
measure bell172
cz bell172 a5
H bell174
cnot bell174 bell175
cnot a1 bell175
measure bell175
cnot bell175 bell174
cnot bell174 a2
H bell174
measure bell174
cz bell174 a1
H bell176
cnot bell176 bell177
cnot a2 bell177
measure bell177
cnot bell177 bell176
cnot bell176 b9
cnot bell176 b8
cnot bell176 b7
cnot bell176 b6
cnot a2 b5
cnot a2 b4
cnot a2 b3
cnot a2 b2
cnot a1 b1
cnot a1 b0
cnot bell176 a9
cnot bell176 a8
cnot bell176 a7
cnot bell176 a6
H bell176
measure bell176
cz bell176 a2
cnot a2 a5
cnot a2 a4
cnot a2 a3
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
