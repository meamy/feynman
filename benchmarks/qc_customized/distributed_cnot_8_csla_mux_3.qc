# Hyperedge cut (ebits): 39

# Actual ebits used (Synthesis): 64
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/csla_mux_3.qc):
#   Qubits: 15
#   H: 20
#   T: 70
#   cnot: 80
#   Depth: 58
#   T depth: 26
# Result (20.908ms):
#   Qubits: 143
#   H: 148
#   T: 62
#   cnot: 316
#   cz: 71
#   measure: 128
#   reset: 132
#   swap: 7
#   Depth: 225
#   T depth: 29


# Result Circuit
.v cin a0 b0 c0 d0 a1 b1 c1 d1 e1 a2 b2 c2 d2 e2 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i cin a0 b0 a1 b1 a2 b2
.o cin a0 b0 c0 d0 a1 b1 c1 d1 e1 a2 b2 c2 d2 e2
BEGIN 
H c0
H c1
H c2
T c0
H bell0
cnot bell0 bell1
cnot a0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
H bell2
cnot bell2 bell3
cnot b0 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
T c0
cnot bell0 c0
H bell0
measure bell0
cz bell0 a0
T* c0
cnot bell2 c0
H bell2
measure bell2
cz bell2 b0
H c0
T c1
H bell4
cnot bell4 bell5
cnot a1 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c1
T* c1
H bell6
cnot bell6 bell7
cnot b1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c1
T c1
cnot bell4 c1
H bell4
measure bell4
cz bell4 a1
T* c1
cnot bell6 c1
H bell6
measure bell6
cz bell6 b1
H c1
T c2
H bell8
cnot bell8 bell9
cnot a2 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c2
T* c2
H bell10
cnot bell10 bell11
cnot b2 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c2
T c2
cnot bell8 c2
H bell8
measure bell8
cz bell8 a2
T* c2
cnot bell10 c2
H bell10
measure bell10
cz bell10 b2
H c2
cnot c2 e2
H bell12
cnot bell12 bell13
cnot c1 bell13
measure bell13
cnot bell13 bell12
cnot bell12 e1
H bell12
measure bell12
cz bell12 c1
H bell14
cnot bell14 bell15
cnot c0 bell15
measure bell15
cnot bell15 bell14
cnot bell14 d0
H bell16
cnot bell16 bell17
cnot a2 bell17
measure bell17
cnot bell17 bell16
cnot bell16 b2
H bell18
cnot bell18 bell19
cnot a1 bell19
measure bell19
cnot bell19 bell18
cnot bell18 b1
H bell18
measure bell18
cz bell18 a1
cnot a0 b0
H c1
H e1
H c2
H e2
T e1
H bell20
cnot bell20 bell21
cnot b1 bell21
measure bell21
cnot bell21 bell20
cnot bell20 e1
T* e1
cnot bell14 e1
T e1
cnot bell20 e1
H bell20
measure bell20
cz bell20 b1
T* e1
swap d0 d2
cnot bell14 e1
H bell14
measure bell14
cz bell14 c0
H bell22
cnot bell22 bell23
cnot c0 bell23
measure bell23
cnot bell23 bell22
cnot bell22 d2
H bell22
measure bell22
cz bell22 c0
H bell24
cnot bell24 bell25
cnot c0 bell25
measure bell25
cnot bell25 bell24
cnot bell24 d0
H bell24
measure bell24
cz bell24 c0
cnot d2 b2
cnot b2 d2
H bell26
cnot bell26 bell27
cnot b0 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c0
H bell26
measure bell26
cz bell26 b0
H e1
T* c1
H bell28
cnot bell28 bell29
cnot b1 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c1
T c1
H bell30
cnot bell30 bell31
cnot c0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c1
T* c1
cnot bell28 c1
H bell28
measure bell28
cz bell28 b1
T c1
cnot bell30 c1
H c1
T c2
H bell32
cnot bell32 bell33
cnot b2 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c2
T* c2
H bell34
cnot bell34 bell35
cnot c1 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c2
H bell34
measure bell34
cz bell34 c1
T c2
cnot bell32 c2
H bell32
measure bell32
cz bell32 b2
T* c2
cnot c0 b1
cnot d2 b2
cnot d1 c1
H bell36
cnot bell36 bell37
cnot d1 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c2
H bell36
measure bell36
cz bell36 d1
H bell38
cnot bell38 bell39
cnot d2 bell39
measure bell39
cnot bell39 bell38
cnot bell38 d1
H bell38
measure bell38
cz bell38 d2
H bell40
cnot bell40 bell41
cnot e1 bell41
measure bell41
cnot bell41 bell40
cnot bell40 d2
H bell40
measure bell40
cz bell40 e1
cnot c1 d1
H bell42
cnot bell42 bell43
cnot c1 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c2
swap b2 d1
H bell44
cnot bell44 bell45
cnot b1 bell45
measure bell45
cnot bell45 bell44
cnot bell44 d1
H bell44
measure bell44
cz bell44 b1
H bell46
cnot bell46 bell47
cnot b0 bell47
measure bell47
cnot bell47 bell46
cnot bell46 d1
H bell46
measure bell46
cz bell46 b0
H c2
T* e2
cnot bell42 e2
H bell48
cnot bell48 bell49
cnot b2 bell49
measure bell49
cnot bell49 bell48
cnot bell48 e2
T e2
H bell50
cnot bell50 bell51
cnot d2 bell51
measure bell51
cnot bell51 bell50
cnot bell50 e2
T e2
cnot bell42 e2
H bell42
measure bell42
cz bell42 c1
cnot bell48 e2
H bell48
measure bell48
cz bell48 b2
T* e2
cnot bell50 e2
H bell50
measure bell50
cz bell50 d2
H e2
cnot d2 b2
H bell52
cnot bell52 bell53
cnot e1 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c1
cnot e2 c2
cnot bell52 d1
H bell52
measure bell52
cz bell52 e1
swap d1 e1
swap c1 d1
H bell54
cnot bell54 bell55
cnot b2 bell55
measure bell55
cnot bell55 bell54
cnot bell54 d1
cnot bell54 c1
H bell54
measure bell54
cz bell54 b2
H bell56
cnot bell56 bell57
cnot b1 bell57
measure bell57
cnot bell57 bell56
cnot bell56 e1
H bell56
measure bell56
cz bell56 b1
swap b1 d1
H bell58
cnot bell58 bell59
cnot b0 bell59
measure bell59
cnot bell59 bell58
cnot bell58 e1
H bell58
measure bell58
cz bell58 b0
H bell60
cnot bell60 bell61
cnot b0 bell61
measure bell61
cnot bell61 bell60
cnot bell60 d1
H bell60
measure bell60
cz bell60 b0
H bell62
cnot bell62 bell63
cnot b0 bell63
measure bell63
cnot bell63 bell62
cnot bell62 b1
H bell62
measure bell62
cz bell62 b0
H e2
T d2
cnot b2 d2
T* d2
H bell64
cnot bell64 bell65
cnot c1 bell65
measure bell65
cnot bell65 bell64
cnot bell64 d2
T* d2
cnot bell16 d2
T d2
cnot bell64 d2
H bell64
measure bell64
cz bell64 c1
cnot b2 d2
cnot bell16 d2
H bell16
measure bell16
cz bell16 a2
H d2
T* d1
H bell66
cnot bell66 bell67
cnot b0 bell67
measure bell67
cnot bell67 bell66
cnot bell66 d1
T d1
cnot bell30 d1
T* d1
H bell68
cnot bell68 bell69
cnot a1 bell69
measure bell69
cnot bell69 bell68
cnot bell68 d1
T d1
cnot bell30 d1
H bell30
measure bell30
cz bell30 c0
cnot bell66 d1
cnot bell68 d1
H bell68
measure bell68
cz bell68 a1
H d1
T e2
cnot c2 e2
T* e2
H bell70
cnot bell70 bell71
cnot cin bell71
measure bell71
cnot bell71 bell70
cnot bell70 e2
T e2
cnot c2 e2
T* e2
cnot bell70 e2
H bell70
measure bell70
cz bell70 cin
H e2
T* d2
cnot b2 d2
T d2
H bell72
cnot bell72 bell73
cnot cin bell73
measure bell73
cnot bell73 bell72
cnot bell72 d2
T* d2
cnot b2 d2
T d2
cnot bell72 d2
H bell72
measure bell72
cz bell72 cin
H d2
T d1
cnot bell66 d1
T* d1
H bell74
cnot bell74 bell75
cnot cin bell75
measure bell75
cnot bell75 bell74
cnot bell74 d1
T d1
cnot bell66 d1
H bell66
measure bell66
cz bell66 b0
T* d1
cnot bell74 d1
H bell74
measure bell74
cz bell74 cin
H d1
T a0
cnot a0 b0
T b0
T cin
H bell76
cnot bell76 bell77
cnot b0 bell77
measure bell77
cnot bell77 bell76
cnot bell76 cin
H bell76
measure bell76
cz bell76 b0
H bell78
cnot bell78 bell79
cnot a0 bell79
measure bell79
cnot bell79 bell78
cnot bell78 cin
H bell78
measure bell78
cz bell78 a0
T* cin
T* b2
H bell80
cnot bell80 bell81
cnot cin bell81
measure bell81
cnot bell81 bell80
cnot bell80 b2
H bell82
cnot bell82 bell83
cnot b0 bell83
measure bell83
cnot bell83 bell82
cnot bell82 b2
H bell84
cnot bell84 bell85
cnot a0 bell85
measure bell85
cnot bell85 bell84
cnot bell84 b2
T b2
T* c0
H bell86
cnot bell86 bell87
cnot c0 bell87
measure bell87
cnot bell87 bell86
cnot b0 bell86
cnot a0 bell86
H bell88
cnot bell88 bell89
cnot bell86 bell89
measure bell89
cnot bell89 bell88
reset bell89
cnot c0 bell88
cnot bell88 c0
H bell88
measure bell88
cz bell88 a0
cz bell88 b0
H bell86
measure bell86
cz bell86 c0
T c0
T c1
H bell90
cnot bell90 bell91
cnot c1 bell91
measure bell91
cnot bell91 bell90
cnot bell80 bell90
H bell80
measure bell80
cz bell80 cin
cnot b2 bell90
cnot bell82 bell90
H bell82
measure bell82
cz bell82 b0
cnot bell84 bell90
H bell92
cnot bell92 bell93
cnot bell90 bell93
measure bell93
cnot bell93 bell92
reset bell93
cnot c1 bell92
cnot bell92 c1
H bell92
measure bell92
cz bell92 a0
cz bell92 b0
cz bell92 b2
cz bell92 cin
H bell90
measure bell90
cz bell90 c1
H bell84
measure bell84
cz bell84 a0
T* c1
T c2
H bell94
cnot bell94 bell95
cnot c2 bell95
measure bell95
cnot bell95 bell94
cnot cin bell94
H bell96
cnot bell96 bell97
cnot b0 bell97
measure bell97
cnot bell97 bell96
cnot bell96 bell94
H bell96
measure bell96
cz bell96 b0
H bell98
cnot bell98 bell99
cnot a0 bell99
measure bell99
cnot bell99 bell98
cnot bell98 bell94
H bell100
cnot bell100 bell101
cnot bell94 bell101
measure bell101
cnot bell101 bell100
reset bell101
cnot c2 bell100
cnot bell100 c2
H bell100
measure bell100
cz bell100 a0
cz bell100 b0
cz bell100 cin
H bell94
measure bell94
cz bell94 c2
H bell98
measure bell98
cz bell98 a0
T* c2
T a1
T a2
H bell102
cnot bell102 bell103
cnot d1 bell103
measure bell103
cnot bell103 bell102
cnot bell102 a0
H bell102
measure bell102
cz bell102 d1
H bell104
cnot bell104 bell105
cnot b1 bell105
measure bell105
cnot bell105 bell104
cnot bell104 b0
H bell104
measure bell104
cz bell104 b1
H bell106
cnot bell106 bell107
cnot d1 bell107
measure bell107
cnot bell107 bell106
cnot bell106 b1
cnot d2 b2
cnot bell106 c0
H bell106
measure bell106
cz bell106 d1
H bell108
cnot bell108 bell109
cnot c1 bell109
measure bell109
cnot bell109 bell108
cnot d2 bell108
H bell110
cnot bell110 bell111
cnot d1 bell111
measure bell111
cnot bell111 bell110
cnot bell110 cin
H bell110
measure bell110
cz bell110 d1
cnot e2 c2
H bell112
cnot bell112 bell113
cnot cin bell113
measure bell113
cnot bell113 bell112
cnot bell112 c2
H bell112
measure bell112
cz bell112 cin
H bell114
cnot bell114 bell115
cnot cin bell115
measure bell115
cnot bell115 bell114
cnot bell114 d1
H bell114
measure bell114
cz bell114 cin
H bell116
cnot bell116 bell117
cnot cin bell117
measure bell117
cnot bell117 bell116
cnot bell116 b2
H bell116
measure bell116
cz bell116 cin
H bell118
cnot bell118 bell119
cnot b1 bell119
measure bell119
cnot bell119 bell118
cnot bell118 b2
H bell118
measure bell118
cz bell118 b1
H bell120
cnot bell120 bell121
cnot b1 bell121
measure bell121
cnot bell121 bell120
cnot bell120 cin
H bell120
measure bell120
cz bell120 b1
H bell122
cnot bell122 bell123
cnot b1 bell123
measure bell123
cnot bell123 bell122
cnot bell122 c2
H bell122
measure bell122
cz bell122 b1
cnot b2 bell108
H bell124
cnot bell124 bell125
cnot bell108 bell125
measure bell125
cnot bell125 bell124
reset bell125
cnot c1 bell124
cnot bell124 c1
H bell124
measure bell124
cz bell124 b2
cz bell124 d2
H bell108
measure bell108
cz bell108 c1
cnot b1 c0
swap b0 d1
H bell126
cnot bell126 bell127
cnot d1 bell127
measure bell127
cnot bell127 bell126
cnot bell126 a0
H bell126
measure bell126
cz bell126 d1
swap a0 d1
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
END
