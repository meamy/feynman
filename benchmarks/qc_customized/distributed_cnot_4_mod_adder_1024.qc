# Hyperedge cut (ebits): 74

# Actual ebits used (Synthesis): 90
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_adder_1024.qc):
#   Qubits: 28
#   H: 570
#   T: 1995
#   cnot: 1720
#   Depth: 2218
#   T depth: 981
# Result (842.166ms):
#   Qubits: 208
#   H: 510
#   T: 1259
#   cnot: 1518
#   cz: 90
#   measure: 180
#   reset: 185
#   swap: 8
#   Depth: 2422
#   T depth: 863


# Result Circuit
.v x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 0 1 2 3 4 5 6 7 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
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
cnot x18 0
T* 0
H bell4
cnot bell4 bell5
cnot x8 bell5
measure bell5
cnot bell5 bell4
cnot bell4 0
T 0
cnot x18 0
T* 0
cnot bell4 0
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
cnot x18 0
T 0
cnot bell4 0
T* 0
cnot x18 0
T 0
cnot bell4 0
cnot bell2 x19
T x19
cnot bell2 x19
H bell2
measure bell2
cz bell2 x9
H x19
T x19
cnot x18 x19
T* x19
cnot bell4 x19
T x19
cnot x18 x19
T* x19
cnot bell4 x19
H x19
cnot bell4 x18
H 1
T 1
H bell6
cnot bell6 bell7
cnot x17 bell7
measure bell7
cnot bell7 bell6
cnot bell6 1
T* 1
H bell8
cnot bell8 bell9
cnot x7 bell9
measure bell9
cnot bell9 bell8
cnot bell8 1
T 1
cnot bell6 1
T* 1
cnot bell8 1
swap 2 6
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
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
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot bell6 1
T 1
cnot bell8 1
T* 1
cnot bell6 1
T 1
cnot bell8 1
T 0
cnot bell6 0
T* 0
cnot bell8 0
T 0
cnot bell6 0
T* 0
cnot bell8 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
swap 2 7
H 0
T* 0
cnot bell6 0
T 0
cnot bell8 0
T* 0
cnot bell6 0
T 0
cnot bell8 0
swap 2 6
cnot bell4 x18
T x18
cnot bell4 x18
H bell4
measure bell4
cz bell4 x8
H x18
T x18
cnot bell6 x18
T* x18
cnot bell8 x18
T x18
cnot bell6 x18
H bell6
measure bell6
cz bell6 x17
T* x18
cnot bell8 x18
H bell8
measure bell8
cz bell8 x7
H x18
cnot x7 x17
H 2
T 2
H bell10
cnot bell10 bell11
cnot x16 bell11
measure bell11
cnot bell11 bell10
cnot bell10 2
T* 2
H bell12
cnot bell12 bell13
cnot x6 bell13
measure bell13
cnot bell13 bell12
cnot bell12 2
T 2
cnot bell10 2
T* 2
cnot bell12 2
H 2
T 1
cnot 2 1
T* 1
H bell14
cnot bell14 bell15
cnot x17 bell15
measure bell15
cnot bell15 bell14
cnot bell14 1
T 1
cnot 2 1
T* 1
cnot bell14 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
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
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot bell14 1
T* 1
cnot 2 1
T 1
cnot bell14 1
H 2
T* 2
cnot bell10 2
T 2
cnot bell12 2
T* 2
cnot bell10 2
T 2
cnot bell12 2
T 1
cnot bell10 1
T* 1
cnot bell12 1
T 1
cnot bell10 1
T* 1
cnot bell12 1
swap 3 5
H 1
T 0
cnot 1 0
T* 0
cnot bell14 0
T 0
cnot 1 0
T* 0
cnot bell14 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot bell14 0
T* 0
cnot 1 0
T 0
cnot bell14 0
H 1
T* 1
cnot bell10 1
T 1
cnot bell12 1
T* 1
cnot bell10 1
T 1
cnot bell12 1
T 0
cnot bell10 0
T* 0
cnot bell12 0
T 0
cnot bell10 0
T* 0
cnot bell12 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot bell14 x18
T x18
cnot 0 x18
T* x18
cnot bell14 x18
H x18
T 0
cnot bell14 0
T* 0
cnot bell14 0
H bell14
measure bell14
cz bell14 x17
swap 3 6
H 0
T* 0
cnot bell10 0
T 0
cnot bell12 0
T* 0
cnot bell10 0
H bell10
measure bell10
cz bell10 x16
T 0
cnot bell12 0
H bell12
measure bell12
cz bell12 x6
swap 3 5
cnot x7 x17
T x17
cnot x7 x17
H x17
T x17
cnot x16 x17
T* x17
cnot x6 x17
T x17
cnot x16 x17
T* x17
cnot x6 x17
H x17
cnot x6 x16
H 3
T 3
H bell16
cnot bell16 bell17
cnot x15 bell17
measure bell17
cnot bell17 bell16
cnot bell16 3
T* 3
H bell18
cnot bell18 bell19
cnot x5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 3
T 3
cnot bell16 3
T* 3
cnot bell18 3
H 3
T 2
cnot 3 2
T* 2
H bell20
cnot bell20 bell21
cnot x16 bell21
measure bell21
cnot bell21 bell20
cnot bell20 2
T 2
cnot 3 2
T* 2
cnot bell20 2
H 2
T 1
cnot 2 1
T* 1
H bell22
cnot bell22 bell23
cnot x17 bell23
measure bell23
cnot bell23 bell22
cnot bell22 1
T 1
cnot 2 1
T* 1
cnot bell22 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
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
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot bell22 1
T* 1
cnot 2 1
T 1
cnot bell22 1
H 2
T* 2
cnot 3 2
T 2
cnot bell20 2
T* 2
cnot 3 2
T 2
cnot bell20 2
H 3
T* 3
cnot bell16 3
T 3
cnot bell18 3
T* 3
cnot bell16 3
T 3
cnot bell18 3
T 2
cnot bell16 2
T* 2
cnot bell18 2
T 2
cnot bell16 2
T* 2
cnot bell18 2
H 2
T 1
cnot 2 1
T* 1
cnot bell20 1
T 1
cnot 2 1
T* 1
cnot bell20 1
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
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
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
cnot 2 1
T 1
cnot bell20 1
T* 1
cnot 2 1
T 1
cnot bell20 1
H 2
T* 2
cnot bell16 2
T 2
cnot bell18 2
T* 2
cnot bell16 2
T 2
cnot bell18 2
T 1
cnot bell16 1
T* 1
cnot bell18 1
T 1
cnot bell16 1
T* 1
cnot bell18 1
H 1
T 0
cnot 1 0
T* 0
cnot bell20 0
T 0
cnot 1 0
T* 0
cnot bell20 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot bell22 x18
T x18
cnot 0 x18
T* x18
cnot bell22 x18
H x18
T 0
cnot bell22 0
T* 0
cnot bell22 0
H bell22
measure bell22
cz bell22 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell20 0
T* 0
cnot 1 0
T 0
cnot bell20 0
H 1
T* 1
cnot bell16 1
T 1
cnot bell18 1
T* 1
cnot bell16 1
T 1
cnot bell18 1
T 0
cnot bell16 0
T* 0
cnot bell18 0
T 0
cnot bell16 0
T* 0
cnot bell18 0
H 0
T x17
H x17
T x17
H bell24
cnot bell24 bell25
cnot 0 bell25
measure bell25
cnot bell25 bell24
cnot bell24 x17
T* x17
cnot x16 x17
T x17
cnot bell24 x17
H bell24
measure bell24
cz bell24 0
T* x17
cnot x16 x17
H x17
T 0
cnot bell20 0
T* 0
cnot bell20 0
H bell20
measure bell20
cz bell20 x16
swap 4 5
H 0
T* 0
cnot bell16 0
T 0
cnot bell18 0
T* 0
cnot bell16 0
H bell16
measure bell16
cz bell16 x15
T 0
cnot bell18 0
H bell18
measure bell18
cz bell18 x5
cnot x6 x16
T x16
cnot x6 x16
H x16
T x16
cnot x15 x16
T* x16
cnot x5 x16
T x16
cnot x15 x16
T* x16
cnot x5 x16
H x16
cnot x5 x15
H 4
T 4
cnot x14 4
T* 4
H bell26
cnot bell26 bell27
cnot x4 bell27
measure bell27
cnot bell27 bell26
cnot bell26 4
T 4
cnot x14 4
T* 4
cnot bell26 4
H 4
T 3
H bell28
cnot bell28 bell29
cnot 4 bell29
measure bell29
cnot bell29 bell28
cnot bell28 3
T* 3
H bell30
cnot bell30 bell31
cnot x15 bell31
measure bell31
cnot bell31 bell30
cnot bell30 3
T 3
cnot bell28 3
T* 3
cnot bell30 3
H 3
T 2
cnot 3 2
T* 2
H bell32
cnot bell32 bell33
cnot x16 bell33
measure bell33
cnot bell33 bell32
cnot bell32 2
T 2
cnot 3 2
T* 2
cnot bell32 2
H 2
T 1
cnot 2 1
T* 1
H bell34
cnot bell34 bell35
cnot x17 bell35
measure bell35
cnot bell35 bell34
cnot bell34 1
T 1
cnot 2 1
T* 1
cnot bell34 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
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
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot bell34 1
T* 1
cnot 2 1
T 1
cnot bell34 1
H 2
T* 2
cnot 3 2
T 2
cnot bell32 2
T* 2
cnot 3 2
T 2
cnot bell32 2
H 3
T* 3
cnot bell28 3
T 3
cnot bell30 3
T* 3
cnot bell28 3
H bell28
measure bell28
cz bell28 4
T 3
cnot bell30 3
H 4
T* 4
cnot x14 4
T 4
cnot bell26 4
T* 4
cnot x14 4
T 4
cnot bell26 4
H bell26
measure bell26
cz bell26 x4
T 3
H bell36
cnot bell36 bell37
cnot x14 bell37
measure bell37
cnot bell37 bell36
cnot bell36 3
T* 3
H bell38
cnot bell38 bell39
cnot x4 bell39
measure bell39
cnot bell39 bell38
cnot bell38 3
T 3
cnot bell36 3
T* 3
cnot bell38 3
H 3
T 2
cnot 3 2
T* 2
cnot bell30 2
T 2
cnot 3 2
T* 2
cnot bell30 2
H 2
T 1
cnot 2 1
T* 1
cnot bell32 1
T 1
cnot 2 1
T* 1
cnot bell32 1
H 1
T 0
cnot 1 0
T* 0
cnot bell34 0
T 0
cnot 1 0
T* 0
cnot bell34 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot bell34 0
T* 0
cnot 1 0
T 0
cnot bell34 0
H 1
T* 1
cnot 2 1
T 1
cnot bell32 1
T* 1
cnot 2 1
T 1
cnot bell32 1
H 2
T* 2
cnot 3 2
T 2
cnot bell30 2
T* 2
cnot 3 2
T 2
cnot bell30 2
H 3
T* 3
cnot bell36 3
T 3
cnot bell38 3
T* 3
cnot bell36 3
T 3
cnot bell38 3
T 2
cnot bell36 2
T* 2
cnot bell38 2
T 2
cnot bell36 2
T* 2
cnot bell38 2
H 2
T 1
cnot 2 1
T* 1
cnot bell30 1
T 1
cnot 2 1
T* 1
cnot bell30 1
H 1
T 0
cnot 1 0
T* 0
cnot bell32 0
T 0
cnot 1 0
T* 0
cnot bell32 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot bell34 x18
T x18
cnot 0 x18
T* x18
cnot bell34 x18
H x18
T 0
cnot bell34 0
T* 0
cnot bell34 0
H bell34
measure bell34
cz bell34 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell32 0
T* 0
cnot 1 0
T 0
cnot bell32 0
H 1
T* 1
cnot 2 1
T 1
cnot bell30 1
T* 1
cnot 2 1
T 1
cnot bell30 1
H 2
T* 2
cnot bell36 2
T 2
cnot bell38 2
T* 2
cnot bell36 2
T 2
cnot bell38 2
T 1
cnot bell36 1
T* 1
cnot bell38 1
T 1
cnot bell36 1
T* 1
cnot bell38 1
H 1
T 0
cnot 1 0
T* 0
cnot bell30 0
T 0
cnot 1 0
T* 0
cnot bell30 0
H 0
T x17
H x17
T x17
H bell40
cnot bell40 bell41
cnot 0 bell41
measure bell41
cnot bell41 bell40
cnot bell40 x17
T* x17
cnot x16 x17
T x17
cnot bell40 x17
H bell40
measure bell40
cz bell40 0
T* x17
cnot x16 x17
H x17
T 0
cnot bell32 0
T* 0
cnot bell32 0
H bell32
measure bell32
cz bell32 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell30 0
T* 0
cnot 1 0
T 0
cnot bell30 0
H 1
T* 1
cnot bell36 1
T 1
cnot bell38 1
T* 1
cnot bell36 1
T 1
cnot bell38 1
T 0
cnot bell36 0
T* 0
cnot bell38 0
T 0
cnot bell36 0
T* 0
cnot bell38 0
H 0
T x16
H x16
T x16
H bell42
cnot bell42 bell43
cnot 0 bell43
measure bell43
cnot bell43 bell42
cnot bell42 x16
T* x16
cnot x15 x16
T x16
cnot bell42 x16
H bell42
measure bell42
cz bell42 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell30 0
T* 0
cnot bell30 0
H bell30
measure bell30
cz bell30 x15
H 0
T* 0
cnot bell36 0
T 0
cnot bell38 0
T* 0
cnot bell36 0
H bell36
measure bell36
cz bell36 x14
T 0
cnot bell38 0
H bell38
measure bell38
cz bell38 x4
cnot x5 x15
T x15
cnot x5 x15
H x15
T x15
H bell44
cnot bell44 bell45
cnot x14 bell45
measure bell45
cnot bell45 bell44
cnot bell44 x15
T* x15
H bell46
cnot bell46 bell47
cnot x4 bell47
measure bell47
cnot bell47 bell46
cnot bell46 x15
T x15
cnot bell44 x15
H bell44
measure bell44
cz bell44 x14
T* x15
cnot bell46 x15
H bell46
measure bell46
cz bell46 x4
H x15
H bell48
cnot bell48 bell49
cnot x4 bell49
measure bell49
cnot bell49 bell48
cnot bell48 x14
H 5
T 5
cnot x13 5
T* 5
H bell50
cnot bell50 bell51
cnot x3 bell51
measure bell51
cnot bell51 bell50
cnot bell50 5
T 5
cnot x13 5
T* 5
cnot bell50 5
H 5
T 4
cnot 5 4
T* 4
cnot x14 4
T 4
cnot 5 4
T* 4
cnot x14 4
H 4
T 3
H bell52
cnot bell52 bell53
cnot 4 bell53
measure bell53
cnot bell53 bell52
cnot bell52 3
T* 3
H bell54
cnot bell54 bell55
cnot x15 bell55
measure bell55
cnot bell55 bell54
cnot bell54 3
T 3
cnot bell52 3
T* 3
cnot bell54 3
H 3
T 2
cnot 3 2
T* 2
H bell56
cnot bell56 bell57
cnot x16 bell57
measure bell57
cnot bell57 bell56
cnot bell56 2
T 2
cnot 3 2
T* 2
cnot bell56 2
H 2
T 1
cnot 2 1
T* 1
H bell58
cnot bell58 bell59
cnot x17 bell59
measure bell59
cnot bell59 bell58
cnot bell58 1
T 1
cnot 2 1
T* 1
cnot bell58 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
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
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot bell58 1
T* 1
cnot 2 1
T 1
cnot bell58 1
H 2
T* 2
cnot 3 2
T 2
cnot bell56 2
T* 2
cnot 3 2
T 2
cnot bell56 2
H 3
T* 3
cnot bell52 3
T 3
cnot bell54 3
T* 3
cnot bell52 3
H bell52
measure bell52
cz bell52 4
T 3
cnot bell54 3
H 4
T* 4
cnot 5 4
T 4
cnot x14 4
T* 4
cnot 5 4
T 4
cnot x14 4
H 5
T* 5
cnot x13 5
T 5
cnot bell50 5
T* 5
cnot x13 5
T 5
cnot bell50 5
T 4
cnot x13 4
T* 4
cnot bell50 4
T 4
cnot x13 4
T* 4
cnot bell50 4
H 4
T 3
H bell60
cnot bell60 bell61
cnot 4 bell61
measure bell61
cnot bell61 bell60
cnot bell60 3
T* 3
H bell62
cnot bell62 bell63
cnot x14 bell63
measure bell63
cnot bell63 bell62
cnot bell62 3
T 3
cnot bell60 3
T* 3
cnot bell62 3
H 3
T 2
cnot 3 2
T* 2
cnot bell54 2
T 2
cnot 3 2
T* 2
cnot bell54 2
H 2
T 1
cnot 2 1
T* 1
cnot bell56 1
T 1
cnot 2 1
T* 1
cnot bell56 1
H 1
T 0
cnot 1 0
T* 0
cnot bell58 0
T 0
cnot 1 0
T* 0
cnot bell58 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot bell58 0
T* 0
cnot 1 0
T 0
cnot bell58 0
H 1
T* 1
cnot 2 1
T 1
cnot bell56 1
T* 1
cnot 2 1
T 1
cnot bell56 1
H 2
T* 2
cnot 3 2
T 2
cnot bell54 2
T* 2
cnot 3 2
T 2
cnot bell54 2
H 3
T* 3
cnot bell60 3
T 3
cnot bell62 3
T* 3
cnot bell60 3
H bell60
measure bell60
cz bell60 4
T 3
cnot bell62 3
H 4
T* 4
cnot x13 4
T 4
cnot bell50 4
T* 4
cnot x13 4
T 4
cnot bell50 4
H bell50
measure bell50
cz bell50 x3
T 3
H bell64
cnot bell64 bell65
cnot x13 bell65
measure bell65
cnot bell65 bell64
cnot bell64 3
T* 3
H bell66
cnot bell66 bell67
cnot x3 bell67
measure bell67
cnot bell67 bell66
cnot bell66 3
T 3
cnot bell64 3
T* 3
cnot bell66 3
H 3
T 2
cnot 3 2
T* 2
cnot bell62 2
T 2
cnot 3 2
T* 2
cnot bell62 2
H 2
T 1
cnot 2 1
T* 1
cnot bell54 1
T 1
cnot 2 1
T* 1
cnot bell54 1
H 1
T 0
cnot 1 0
T* 0
cnot bell56 0
T 0
cnot 1 0
T* 0
cnot bell56 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot bell58 x18
T x18
cnot 0 x18
T* x18
cnot bell58 x18
H x18
T 0
cnot bell58 0
T* 0
cnot bell58 0
H bell58
measure bell58
cz bell58 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell56 0
T* 0
cnot 1 0
T 0
cnot bell56 0
H 1
T* 1
cnot 2 1
T 1
cnot bell54 1
T* 1
cnot 2 1
T 1
cnot bell54 1
H 2
T* 2
cnot 3 2
T 2
cnot bell62 2
T* 2
cnot 3 2
T 2
cnot bell62 2
H 3
T* 3
cnot bell64 3
T 3
cnot bell66 3
T* 3
cnot bell64 3
T 3
cnot bell66 3
T 2
cnot bell64 2
T* 2
cnot bell66 2
T 2
cnot bell64 2
T* 2
cnot bell66 2
H 2
T 1
cnot 2 1
T* 1
cnot bell62 1
T 1
cnot 2 1
T* 1
cnot bell62 1
H 1
T 0
cnot 1 0
T* 0
cnot bell54 0
T 0
cnot 1 0
T* 0
cnot bell54 0
H 0
T x17
H x17
T x17
H bell68
cnot bell68 bell69
cnot 0 bell69
measure bell69
cnot bell69 bell68
cnot bell68 x17
T* x17
cnot x16 x17
T x17
cnot bell68 x17
H bell68
measure bell68
cz bell68 0
T* x17
cnot x16 x17
H x17
T 0
cnot bell56 0
T* 0
cnot bell56 0
H bell56
measure bell56
cz bell56 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell54 0
T* 0
cnot 1 0
T 0
cnot bell54 0
H 1
T* 1
cnot 2 1
T 1
cnot bell62 1
T* 1
cnot 2 1
T 1
cnot bell62 1
H 2
T* 2
cnot bell64 2
T 2
cnot bell66 2
T* 2
cnot bell64 2
T 2
cnot bell66 2
T 1
cnot bell64 1
T* 1
cnot bell66 1
T 1
cnot bell64 1
T* 1
cnot bell66 1
H 1
T 0
cnot 1 0
T* 0
cnot bell62 0
T 0
cnot 1 0
T* 0
cnot bell62 0
H 0
T x16
H x16
T x16
H bell70
cnot bell70 bell71
cnot 0 bell71
measure bell71
cnot bell71 bell70
cnot bell70 x16
T* x16
cnot x15 x16
T x16
cnot bell70 x16
H bell70
measure bell70
cz bell70 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell54 0
T* 0
cnot bell54 0
H bell54
measure bell54
cz bell54 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell62 0
T* 0
cnot 1 0
T 0
cnot bell62 0
H bell62
measure bell62
cz bell62 x14
H 1
T* 1
cnot bell64 1
T 1
cnot bell66 1
T* 1
cnot bell64 1
T 1
cnot bell66 1
T 0
cnot bell64 0
T* 0
cnot bell66 0
T 0
cnot bell64 0
T* 0
cnot bell66 0
H 0
T x15
H x15
T x15
H bell72
cnot bell72 bell73
cnot 0 bell73
measure bell73
cnot bell73 bell72
cnot bell72 x15
T* x15
H bell74
cnot bell74 bell75
cnot x14 bell75
measure bell75
cnot bell75 bell74
cnot bell74 x15
T x15
cnot bell72 x15
H bell72
measure bell72
cz bell72 0
T* x15
cnot bell74 x15
H bell74
measure bell74
cz bell74 x14
H x15
T 0
H bell76
cnot bell76 bell77
cnot x14 bell77
measure bell77
cnot bell77 bell76
cnot bell76 0
T* 0
cnot bell76 0
H bell76
measure bell76
cz bell76 x14
H 0
T* 0
cnot bell64 0
T 0
cnot bell66 0
T* 0
cnot bell64 0
H bell64
measure bell64
cz bell64 x13
T 0
cnot bell66 0
H bell66
measure bell66
cz bell66 x3
cnot bell48 x14
T x14
cnot bell48 x14
H bell48
measure bell48
cz bell48 x4
H x14
T x14
cnot x13 x14
T* x14
H bell78
cnot bell78 bell79
cnot x3 bell79
measure bell79
cnot bell79 bell78
cnot bell78 x14
T x14
cnot x13 x14
T* x14
cnot bell78 x14
H x14
cnot bell78 x13
H 6
T 6
cnot x12 6
T* 6
cnot x2 6
T 6
cnot x12 6
T* 6
cnot x2 6
H 6
T 5
cnot 6 5
T* 5
cnot x13 5
T 5
cnot 6 5
T* 5
cnot x13 5
H 5
T 4
cnot 5 4
T* 4
cnot x14 4
T 4
cnot 5 4
T* 4
cnot x14 4
H 4
T 3
H bell80
cnot bell80 bell81
cnot 4 bell81
measure bell81
cnot bell81 bell80
cnot bell80 3
T* 3
H bell82
cnot bell82 bell83
cnot x15 bell83
measure bell83
cnot bell83 bell82
cnot bell82 3
T 3
cnot bell80 3
T* 3
cnot bell82 3
H 3
T 2
cnot 3 2
T* 2
H bell84
cnot bell84 bell85
cnot x16 bell85
measure bell85
cnot bell85 bell84
cnot bell84 2
T 2
cnot 3 2
T* 2
cnot bell84 2
H 2
T 1
cnot 2 1
T* 1
H bell86
cnot bell86 bell87
cnot x17 bell87
measure bell87
cnot bell87 bell86
cnot bell86 1
T 1
cnot 2 1
T* 1
cnot bell86 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
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
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot bell86 1
T* 1
cnot 2 1
T 1
cnot bell86 1
H 2
T* 2
cnot 3 2
T 2
cnot bell84 2
T* 2
cnot 3 2
T 2
cnot bell84 2
H 3
T* 3
cnot bell80 3
T 3
cnot bell82 3
T* 3
cnot bell80 3
H bell80
measure bell80
cz bell80 4
T 3
cnot bell82 3
H 4
T* 4
cnot 5 4
T 4
cnot x14 4
T* 4
cnot 5 4
T 4
cnot x14 4
H 5
T* 5
cnot 6 5
T 5
cnot x13 5
T* 5
cnot 6 5
T 5
cnot x13 5
H 6
T* 6
cnot x12 6
T 6
cnot x2 6
T* 6
cnot x12 6
T 6
cnot x2 6
T 5
cnot x12 5
T* 5
cnot x2 5
T 5
cnot x12 5
T* 5
cnot x2 5
H 5
T 4
cnot 5 4
T* 4
cnot x13 4
T 4
cnot 5 4
T* 4
cnot x13 4
H 4
T 3
H bell88
cnot bell88 bell89
cnot 4 bell89
measure bell89
cnot bell89 bell88
cnot bell88 3
T* 3
H bell90
cnot bell90 bell91
cnot x14 bell91
measure bell91
cnot bell91 bell90
cnot bell90 3
T 3
cnot bell88 3
T* 3
cnot bell90 3
H 3
T 2
cnot 3 2
T* 2
cnot bell82 2
T 2
cnot 3 2
T* 2
cnot bell82 2
H 2
T 1
cnot 2 1
T* 1
cnot bell84 1
T 1
cnot 2 1
T* 1
cnot bell84 1
H 1
T 0
cnot 1 0
T* 0
cnot bell86 0
T 0
cnot 1 0
T* 0
cnot bell86 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot bell86 0
T* 0
cnot 1 0
T 0
cnot bell86 0
H 1
T* 1
cnot 2 1
T 1
cnot bell84 1
T* 1
cnot 2 1
T 1
cnot bell84 1
H 2
T* 2
cnot 3 2
T 2
cnot bell82 2
T* 2
cnot 3 2
T 2
cnot bell82 2
H 3
T* 3
cnot bell88 3
T 3
cnot bell90 3
T* 3
cnot bell88 3
H bell88
measure bell88
cz bell88 4
T 3
cnot bell90 3
H 4
T* 4
cnot 5 4
T 4
cnot x13 4
T* 4
cnot 5 4
T 4
cnot x13 4
H 5
T* 5
cnot x12 5
T 5
cnot x2 5
T* 5
cnot x12 5
T 5
cnot x2 5
T 4
cnot x12 4
T* 4
cnot x2 4
T 4
cnot x12 4
T* 4
cnot x2 4
H 4
T 3
H bell92
cnot bell92 bell93
cnot 4 bell93
measure bell93
cnot bell93 bell92
cnot bell92 3
T* 3
H bell94
cnot bell94 bell95
cnot x13 bell95
measure bell95
cnot bell95 bell94
cnot bell94 3
T 3
cnot bell92 3
T* 3
cnot bell94 3
H 3
T 2
cnot 3 2
T* 2
cnot bell90 2
T 2
cnot 3 2
T* 2
cnot bell90 2
H 2
T 1
cnot 2 1
T* 1
cnot bell82 1
T 1
cnot 2 1
T* 1
cnot bell82 1
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
cnot 0 x18
T* x18
cnot bell86 x18
T x18
cnot 0 x18
T* x18
cnot bell86 x18
H x18
T 0
cnot bell86 0
T* 0
cnot bell86 0
H bell86
measure bell86
cz bell86 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell84 0
T* 0
cnot 1 0
T 0
cnot bell84 0
H 1
T* 1
cnot 2 1
T 1
cnot bell82 1
T* 1
cnot 2 1
T 1
cnot bell82 1
H 2
T* 2
cnot 3 2
T 2
cnot bell90 2
T* 2
cnot 3 2
T 2
cnot bell90 2
H 3
T* 3
cnot bell92 3
T 3
cnot bell94 3
T* 3
cnot bell92 3
H bell92
measure bell92
cz bell92 4
T 3
cnot bell94 3
H 4
T* 4
cnot x12 4
T 4
cnot x2 4
T* 4
cnot x12 4
T 4
cnot x2 4
T 3
H bell96
cnot bell96 bell97
cnot x12 bell97
measure bell97
cnot bell97 bell96
cnot bell96 3
T* 3
H bell98
cnot bell98 bell99
cnot x2 bell99
measure bell99
cnot bell99 bell98
cnot bell98 3
T 3
cnot bell96 3
T* 3
cnot bell98 3
H 3
T 2
cnot 3 2
T* 2
cnot bell94 2
T 2
cnot 3 2
T* 2
cnot bell94 2
H 2
T 1
cnot 2 1
T* 1
cnot bell90 1
T 1
cnot 2 1
T* 1
cnot bell90 1
H 1
T 0
cnot 1 0
T* 0
cnot bell82 0
T 0
cnot 1 0
T* 0
cnot bell82 0
H 0
T x17
H x17
T x17
H bell100
cnot bell100 bell101
cnot 0 bell101
measure bell101
cnot bell101 bell100
cnot bell100 x17
T* x17
cnot x16 x17
T x17
cnot bell100 x17
H bell100
measure bell100
cz bell100 0
T* x17
cnot x16 x17
H x17
T 0
cnot bell84 0
T* 0
cnot bell84 0
H bell84
measure bell84
cz bell84 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell82 0
T* 0
cnot 1 0
T 0
cnot bell82 0
H 1
T* 1
cnot 2 1
T 1
cnot bell90 1
T* 1
cnot 2 1
T 1
cnot bell90 1
H 2
T* 2
cnot 3 2
T 2
cnot bell94 2
T* 2
cnot 3 2
T 2
cnot bell94 2
H 3
T* 3
cnot bell96 3
T 3
cnot bell98 3
T* 3
cnot bell96 3
T 3
cnot bell98 3
T 2
cnot bell96 2
T* 2
cnot bell98 2
T 2
cnot bell96 2
T* 2
cnot bell98 2
H 2
T 1
cnot 2 1
T* 1
cnot bell94 1
T 1
cnot 2 1
T* 1
cnot bell94 1
H 1
T 0
cnot 1 0
T* 0
cnot bell90 0
T 0
cnot 1 0
T* 0
cnot bell90 0
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
cnot bell82 0
T* 0
cnot bell82 0
H bell82
measure bell82
cz bell82 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell90 0
T* 0
cnot 1 0
T 0
cnot bell90 0
H bell90
measure bell90
cz bell90 x14
H 1
T* 1
cnot 2 1
T 1
cnot bell94 1
T* 1
cnot 2 1
T 1
cnot bell94 1
H 2
T* 2
cnot bell96 2
T 2
cnot bell98 2
T* 2
cnot bell96 2
T 2
cnot bell98 2
T 1
cnot bell96 1
T* 1
cnot bell98 1
T 1
cnot bell96 1
T* 1
cnot bell98 1
H 1
T 0
cnot 1 0
T* 0
cnot bell94 0
T 0
cnot 1 0
T* 0
cnot bell94 0
H 0
T x15
H x15
T x15
H bell104
cnot bell104 bell105
cnot 0 bell105
measure bell105
cnot bell105 bell104
cnot bell104 x15
T* x15
H bell106
cnot bell106 bell107
cnot x14 bell107
measure bell107
cnot bell107 bell106
cnot bell106 x15
T x15
cnot bell104 x15
H bell104
measure bell104
cz bell104 0
T* x15
cnot bell106 x15
H bell106
measure bell106
cz bell106 x14
H x15
T 0
H bell108
cnot bell108 bell109
cnot x14 bell109
measure bell109
cnot bell109 bell108
cnot bell108 0
T* 0
cnot bell108 0
H bell108
measure bell108
cz bell108 x14
H 0
T* 0
cnot 1 0
T 0
cnot bell94 0
T* 0
cnot 1 0
T 0
cnot bell94 0
H 1
T* 1
cnot bell96 1
T 1
cnot bell98 1
T* 1
cnot bell96 1
T 1
cnot bell98 1
T 0
cnot bell96 0
T* 0
cnot bell98 0
T 0
cnot bell96 0
T* 0
cnot bell98 0
H 0
T x14
H x14
T x14
H bell110
cnot bell110 bell111
cnot 0 bell111
measure bell111
cnot bell111 bell110
cnot bell110 x14
T* x14
cnot x13 x14
T x14
cnot bell110 x14
H bell110
measure bell110
cz bell110 0
T* x14
cnot x13 x14
H x14
T 0
cnot bell94 0
T* 0
cnot bell94 0
H bell94
measure bell94
cz bell94 x13
H 0
T* 0
cnot bell96 0
T 0
cnot bell98 0
T* 0
cnot bell96 0
H bell96
measure bell96
cz bell96 x12
T 0
cnot bell98 0
H bell98
measure bell98
cz bell98 x2
cnot bell78 x13
H bell78
measure bell78
cz bell78 x3
T x13
H bell112
cnot bell112 bell113
cnot x13 bell113
measure bell113
cnot bell113 bell112
cnot x3 bell112
H bell114
cnot bell114 bell115
cnot bell112 bell115
measure bell115
cnot bell115 bell114
reset bell115
cnot x13 bell114
cnot bell114 x13
H bell114
measure bell114
cz bell114 x3
H bell112
measure bell112
cz bell112 x13
H x13
T x13
cnot x12 x13
T* x13
cnot x2 x13
T x13
cnot x12 x13
T* x13
cnot x2 x13
H x13
cnot x2 x12
H 7
T 7
cnot x1 7
T* 7
cnot x11 7
T 7
cnot x1 7
T* 7
cnot x11 7
H 7
T 6
H bell116
cnot bell116 bell117
cnot 7 bell117
measure bell117
cnot bell117 bell116
cnot bell116 6
T* 6
cnot x12 6
T 6
cnot bell116 6
T* 6
cnot x12 6
H 6
T 5
cnot 6 5
T* 5
cnot x13 5
T 5
cnot 6 5
T* 5
cnot x13 5
H 5
T 4
cnot 5 4
T* 4
cnot x14 4
T 4
cnot 5 4
T* 4
cnot x14 4
H 4
T 3
H bell118
cnot bell118 bell119
cnot 4 bell119
measure bell119
cnot bell119 bell118
cnot bell118 3
T* 3
H bell120
cnot bell120 bell121
cnot x15 bell121
measure bell121
cnot bell121 bell120
cnot bell120 3
T 3
cnot bell118 3
T* 3
cnot bell120 3
H 3
T 2
cnot 3 2
T* 2
H bell122
cnot bell122 bell123
cnot x16 bell123
measure bell123
cnot bell123 bell122
cnot bell122 2
T 2
cnot 3 2
T* 2
cnot bell122 2
H 2
T 1
cnot 2 1
T* 1
H bell124
cnot bell124 bell125
cnot x17 bell125
measure bell125
cnot bell125 bell124
cnot bell124 1
T 1
cnot 2 1
T* 1
cnot bell124 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
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
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot bell124 1
T* 1
cnot 2 1
T 1
cnot bell124 1
H 2
T* 2
cnot 3 2
T 2
cnot bell122 2
T* 2
cnot 3 2
T 2
cnot bell122 2
H 3
T* 3
cnot bell118 3
T 3
cnot bell120 3
T* 3
cnot bell118 3
H bell118
measure bell118
cz bell118 4
T 3
cnot bell120 3
H 4
T* 4
cnot 5 4
T 4
cnot x14 4
T* 4
cnot 5 4
T 4
cnot x14 4
H 5
T* 5
cnot 6 5
T 5
cnot x13 5
T* 5
cnot 6 5
T 5
cnot x13 5
H 6
T* 6
cnot bell116 6
T 6
cnot x12 6
T* 6
cnot bell116 6
H bell116
measure bell116
cz bell116 7
T 6
cnot x12 6
H 7
T* 7
cnot x1 7
T 7
cnot x11 7
T* 7
cnot x1 7
T 7
cnot x11 7
H 7
T 6
H bell126
cnot bell126 bell127
cnot x1 bell127
measure bell127
cnot bell127 bell126
cnot bell126 6
T* 6
H bell128
cnot bell128 bell129
cnot x11 bell129
measure bell129
cnot bell129 bell128
cnot bell128 6
T 6
cnot bell126 6
T* 6
cnot bell128 6
H 6
T 5
cnot 6 5
T* 5
cnot x12 5
T 5
cnot 6 5
T* 5
cnot x12 5
H 5
T 4
cnot 5 4
T* 4
cnot x13 4
T 4
cnot 5 4
T* 4
cnot x13 4
H 4
T 3
H bell130
cnot bell130 bell131
cnot 4 bell131
measure bell131
cnot bell131 bell130
cnot bell130 3
T* 3
H bell132
cnot bell132 bell133
cnot x14 bell133
measure bell133
cnot bell133 bell132
cnot bell132 3
T 3
cnot bell130 3
T* 3
cnot bell132 3
H 3
T 2
cnot 3 2
T* 2
cnot bell120 2
T 2
cnot 3 2
T* 2
cnot bell120 2
H 2
T 1
cnot 2 1
T* 1
cnot bell122 1
T 1
cnot 2 1
T* 1
cnot bell122 1
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
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot bell124 0
T* 0
cnot 1 0
T 0
cnot bell124 0
H 1
T* 1
cnot 2 1
T 1
cnot bell122 1
T* 1
cnot 2 1
T 1
cnot bell122 1
H 2
T* 2
cnot 3 2
T 2
cnot bell120 2
T* 2
cnot 3 2
T 2
cnot bell120 2
H 3
T* 3
cnot bell130 3
T 3
cnot bell132 3
T* 3
cnot bell130 3
H bell130
measure bell130
cz bell130 4
T 3
cnot bell132 3
H 4
T* 4
cnot 5 4
T 4
cnot x13 4
T* 4
cnot 5 4
T 4
cnot x13 4
H 5
T* 5
cnot 6 5
T 5
cnot x12 5
T* 5
cnot 6 5
T 5
cnot x12 5
H 6
T* 6
cnot bell126 6
T 6
cnot bell128 6
T* 6
cnot bell126 6
T 6
cnot bell128 6
H 6
T 5
cnot bell126 5
T* 5
cnot bell128 5
T 5
cnot bell126 5
T* 5
cnot bell128 5
H 5
T 4
cnot 5 4
T* 4
cnot x12 4
T 4
cnot 5 4
T* 4
cnot x12 4
H 4
T 3
H bell134
cnot bell134 bell135
cnot 4 bell135
measure bell135
cnot bell135 bell134
cnot bell134 3
T* 3
H bell136
cnot bell136 bell137
cnot x13 bell137
measure bell137
cnot bell137 bell136
cnot bell136 3
T 3
cnot bell134 3
T* 3
cnot bell136 3
H 3
T 2
cnot 3 2
T* 2
cnot bell132 2
T 2
cnot 3 2
T* 2
cnot bell132 2
H 2
T 1
cnot 2 1
T* 1
cnot bell120 1
T 1
cnot 2 1
T* 1
cnot bell120 1
H 1
T 0
cnot 1 0
T* 0
cnot bell122 0
T 0
cnot 1 0
T* 0
cnot bell122 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot bell124 x18
T x18
cnot 0 x18
T* x18
cnot bell124 x18
H x18
T 0
cnot bell124 0
T* 0
cnot bell124 0
H bell124
measure bell124
cz bell124 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell122 0
T* 0
cnot 1 0
T 0
cnot bell122 0
H 1
T* 1
cnot 2 1
T 1
cnot bell120 1
T* 1
cnot 2 1
T 1
cnot bell120 1
H 2
T* 2
cnot 3 2
T 2
cnot bell132 2
T* 2
cnot 3 2
T 2
cnot bell132 2
H 3
T* 3
cnot bell134 3
T 3
cnot bell136 3
T* 3
cnot bell134 3
H bell134
measure bell134
cz bell134 4
T 3
cnot bell136 3
H 4
T* 4
cnot 5 4
T 4
cnot x12 4
T* 4
cnot 5 4
T 4
cnot x12 4
H 5
T* 5
cnot bell126 5
T 5
cnot bell128 5
T* 5
cnot bell126 5
T 5
cnot bell128 5
H 5
T 4
cnot bell126 4
T* 4
cnot bell128 4
T 4
cnot bell126 4
T* 4
cnot bell128 4
H 4
T 3
H bell138
cnot bell138 bell139
cnot 4 bell139
measure bell139
cnot bell139 bell138
cnot bell138 3
T* 3
H bell140
cnot bell140 bell141
cnot x12 bell141
measure bell141
cnot bell141 bell140
cnot bell140 3
T 3
cnot bell138 3
T* 3
cnot bell140 3
H 3
T 2
cnot 3 2
T* 2
cnot bell136 2
T 2
cnot 3 2
T* 2
cnot bell136 2
H 2
T 1
cnot 2 1
T* 1
cnot bell132 1
T 1
cnot 2 1
T* 1
cnot bell132 1
H 1
T 0
cnot 1 0
T* 0
cnot bell120 0
T 0
cnot 1 0
T* 0
cnot bell120 0
H 0
T x17
H x17
T x17
H bell142
cnot bell142 bell143
cnot 0 bell143
measure bell143
cnot bell143 bell142
cnot bell142 x17
T* x17
cnot x16 x17
T x17
cnot bell142 x17
H bell142
measure bell142
cz bell142 0
T* x17
cnot x16 x17
H x17
T 0
cnot bell122 0
T* 0
cnot bell122 0
H bell122
measure bell122
cz bell122 x16
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
cnot 2 1
T 1
cnot bell132 1
T* 1
cnot 2 1
T 1
cnot bell132 1
H 2
T* 2
cnot 3 2
T 2
cnot bell136 2
T* 2
cnot 3 2
T 2
cnot bell136 2
H 3
T* 3
cnot bell138 3
T 3
cnot bell140 3
T* 3
cnot bell138 3
H bell138
measure bell138
cz bell138 4
T 3
cnot bell140 3
H 4
T* 4
cnot bell126 4
T 4
cnot bell128 4
T* 4
cnot bell126 4
H bell126
measure bell126
cz bell126 x1
T 4
cnot bell128 4
H bell128
measure bell128
cz bell128 x11
H 4
T 3
H bell144
cnot bell144 bell145
cnot x1 bell145
measure bell145
cnot bell145 bell144
cnot bell144 3
T* 3
H bell146
cnot bell146 bell147
cnot x11 bell147
measure bell147
cnot bell147 bell146
cnot bell146 3
T 3
cnot bell144 3
T* 3
cnot bell146 3
H 3
T 2
cnot 3 2
T* 2
cnot bell140 2
T 2
cnot 3 2
T* 2
cnot bell140 2
H 2
T 1
cnot 2 1
T* 1
cnot bell136 1
T 1
cnot 2 1
T* 1
cnot bell136 1
H 1
T 0
cnot 1 0
T* 0
cnot bell132 0
T 0
cnot 1 0
T* 0
cnot bell132 0
H 0
T x16
H x16
T x16
H bell148
cnot bell148 bell149
cnot 0 bell149
measure bell149
cnot bell149 bell148
cnot bell148 x16
T* x16
cnot x15 x16
T x16
cnot bell148 x16
H bell148
measure bell148
cz bell148 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell120 0
T* 0
cnot bell120 0
H bell120
measure bell120
cz bell120 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell132 0
T* 0
cnot 1 0
T 0
cnot bell132 0
H bell132
measure bell132
cz bell132 x14
H 1
T* 1
cnot 2 1
T 1
cnot bell136 1
T* 1
cnot 2 1
T 1
cnot bell136 1
H 2
T* 2
cnot 3 2
T 2
cnot bell140 2
T* 2
cnot 3 2
T 2
cnot bell140 2
H 3
T* 3
cnot bell144 3
T 3
cnot bell146 3
T* 3
cnot bell144 3
T 3
cnot bell146 3
H 3
T 2
cnot bell144 2
T* 2
cnot bell146 2
T 2
cnot bell144 2
T* 2
cnot bell146 2
H 2
T 1
cnot 2 1
T* 1
cnot bell140 1
T 1
cnot 2 1
T* 1
cnot bell140 1
H 1
T 0
cnot 1 0
T* 0
cnot bell136 0
T 0
cnot 1 0
T* 0
cnot bell136 0
H 0
T x15
H x15
T x15
H bell150
cnot bell150 bell151
cnot 0 bell151
measure bell151
cnot bell151 bell150
cnot bell150 x15
T* x15
H bell152
cnot bell152 bell153
cnot x14 bell153
measure bell153
cnot bell153 bell152
cnot bell152 x15
T x15
cnot bell150 x15
H bell150
measure bell150
cz bell150 0
T* x15
cnot bell152 x15
H bell152
measure bell152
cz bell152 x14
H x15
T 0
H bell154
cnot bell154 bell155
cnot x14 bell155
measure bell155
cnot bell155 bell154
cnot bell154 0
T* 0
cnot bell154 0
H bell154
measure bell154
cz bell154 x14
H 0
T* 0
cnot 1 0
T 0
cnot bell136 0
T* 0
cnot 1 0
T 0
cnot bell136 0
H 1
T* 1
cnot 2 1
T 1
cnot bell140 1
T* 1
cnot 2 1
T 1
cnot bell140 1
H 2
T* 2
cnot bell144 2
T 2
cnot bell146 2
T* 2
cnot bell144 2
T 2
cnot bell146 2
H 2
T 1
cnot bell144 1
T* 1
cnot bell146 1
T 1
cnot bell144 1
T* 1
cnot bell146 1
H 1
T 0
cnot 1 0
T* 0
cnot bell140 0
T 0
cnot 1 0
T* 0
cnot bell140 0
H 0
T x14
H x14
T x14
H bell156
cnot bell156 bell157
cnot 0 bell157
measure bell157
cnot bell157 bell156
cnot bell156 x14
T* x14
cnot x13 x14
T x14
cnot bell156 x14
H bell156
measure bell156
cz bell156 0
T* x14
cnot x13 x14
H x14
T 0
cnot bell136 0
T* 0
cnot bell136 0
H bell136
measure bell136
cz bell136 x13
H 0
T* 0
cnot 1 0
T 0
cnot bell140 0
T* 0
cnot 1 0
T 0
cnot bell140 0
H 1
T* 1
cnot bell144 1
T 1
cnot bell146 1
T* 1
cnot bell144 1
T 1
cnot bell146 1
H 1
T 0
H bell158
cnot bell158 bell159
cnot 0 bell159
measure bell159
cnot bell159 bell158
cnot x1 bell158
H bell160
cnot bell160 bell161
cnot bell158 bell161
measure bell161
cnot bell161 bell160
reset bell161
cnot 0 bell160
cnot bell160 0
H bell160
measure bell160
cz bell160 x1
H bell158
measure bell158
cz bell158 0
T* 0
H bell162
cnot bell162 bell163
cnot 0 bell163
measure bell163
cnot bell163 bell162
cnot x11 bell162
H bell164
cnot bell164 bell165
cnot bell162 bell165
measure bell165
cnot bell165 bell164
reset bell165
cnot 0 bell164
cnot bell164 0
H bell164
measure bell164
cz bell164 x11
H bell162
measure bell162
cz bell162 0
T 0
H bell166
cnot bell166 bell167
cnot 0 bell167
measure bell167
cnot bell167 bell166
cnot x1 bell166
H bell168
cnot bell168 bell169
cnot bell166 bell169
measure bell169
cnot bell169 bell168
reset bell169
cnot 0 bell168
cnot bell168 0
H bell168
measure bell168
cz bell168 x1
H bell166
measure bell166
cz bell166 0
T* 0
cnot bell146 0
H 0
T x13
H x13
T x13
H bell170
cnot bell170 bell171
cnot 0 bell171
measure bell171
cnot bell171 bell170
cnot bell170 x13
T* x13
cnot x12 x13
T x13
cnot bell170 x13
H bell170
measure bell170
cz bell170 0
T* x13
cnot x12 x13
H x13
T 0
cnot bell140 0
T* 0
cnot bell140 0
H bell140
measure bell140
cz bell140 x12
H 0
T* 0
H bell172
cnot bell172 bell173
cnot 0 bell173
measure bell173
cnot bell173 bell172
cnot x1 bell172
H bell174
cnot bell174 bell175
cnot bell172 bell175
measure bell175
cnot bell175 bell174
reset bell175
cnot 0 bell174
cnot bell174 0
H bell174
measure bell174
cz bell174 x1
H bell172
measure bell172
cz bell172 0
T 0
cnot bell146 0
T* 0
cnot bell144 0
H bell144
measure bell144
cz bell144 x1
T 0
cnot bell146 0
H bell146
measure bell146
cz bell146 x11
H 0
cnot x2 x12
T x12
cnot x2 x12
H x12
T x12
H bell176
cnot bell176 bell177
cnot x1 bell177
measure bell177
cnot bell177 bell176
cnot bell176 x12
T* x12
H bell178
cnot bell178 bell179
cnot x11 bell179
measure bell179
cnot bell179 bell178
cnot bell178 x12
T x12
cnot bell176 x12
H bell176
measure bell176
cz bell176 x1
T* x12
cnot bell178 x12
H bell178
measure bell178
cz bell178 x11
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
END
