# Hyperedge cut (ebits): 37

# Actual ebits used (Synthesis): 67
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/hwb6.qc):
#   Qubits: 7
#   H: 30
#   T: 105
#   X: 8
#   cnot: 116
#   Depth: 134
#   T depth: 53
# Result (22.764ms):
#   Qubits: 141
#   H: 160
#   S: 4
#   T: 81
#   X: 5
#   Z: 4
#   cnot: 315
#   cz: 69
#   measure: 134
#   reset: 135
#   swap: 1
#   Depth: 344
#   T depth: 68


# Result Circuit
.v a b c d e f 0 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a b c d e f
.o a b c d e f
BEGIN 
H bell0
cnot bell0 bell1
cnot c bell1
measure bell1
cnot bell1 bell0
cnot bell0 a
H bell0
measure bell0
cz bell0 c
H c
T c
H bell2
cnot bell2 bell3
cnot a bell3
measure bell3
cnot bell3 bell2
cnot bell2 c
T c
H bell4
cnot bell4 bell5
cnot b bell5
measure bell5
cnot bell5 bell4
cnot bell4 c
T* c
cnot bell2 c
H bell2
measure bell2
cz bell2 a
T* c
cnot bell4 c
H bell4
measure bell4
cz bell4 b
H c
T b
H bell6
cnot bell6 bell7
cnot a bell7
measure bell7
cnot bell7 bell6
cnot bell6 b
T b
H bell8
cnot bell8 bell9
cnot f bell9
measure bell9
cnot bell9 bell8
cnot bell8 d
H bell8
measure bell8
cz bell8 f
H bell10
cnot bell10 bell11
cnot e bell11
measure bell11
cnot bell11 bell10
cnot bell10 f
H bell10
measure bell10
cz bell10 e
cnot bell6 b
H b
T b
cnot bell6 b
T b
H bell12
cnot bell12 bell13
cnot c bell13
measure bell13
cnot bell13 bell12
cnot bell12 b
T* b
cnot bell6 b
H bell6
measure bell6
cz bell6 a
T* b
cnot bell12 b
H bell12
measure bell12
cz bell12 c
H b
H f
T f
H bell14
cnot bell14 bell15
cnot a bell15
measure bell15
cnot bell15 bell14
cnot bell14 f
T f
H bell16
cnot bell16 bell17
cnot c bell17
measure bell17
cnot bell17 bell16
cnot bell16 f
T* f
cnot bell14 f
H bell14
measure bell14
cz bell14 a
T* f
cnot bell16 f
H bell16
measure bell16
cz bell16 c
H bell18
cnot bell18 bell19
cnot b bell19
measure bell19
cnot bell19 bell18
cnot bell18 d
H bell18
measure bell18
cz bell18 b
T f
H bell20
cnot bell20 bell21
cnot b bell21
measure bell21
cnot bell21 bell20
cnot bell20 f
T f
H bell22
cnot bell22 bell23
cnot d bell23
measure bell23
cnot bell23 bell22
cnot bell22 f
T* f
cnot bell20 f
H bell20
measure bell20
cz bell20 b
T* f
cnot bell22 f
H bell22
measure bell22
cz bell22 d
H f
T d
H bell24
cnot bell24 bell25
cnot b bell25
measure bell25
cnot bell25 bell24
cnot bell24 d
H bell24
measure bell24
cz bell24 b
T d
H bell26
cnot bell26 bell27
cnot f bell27
measure bell27
cnot bell27 bell26
cnot bell26 e
H bell26
measure bell26
cz bell26 f
H bell28
cnot bell28 bell29
cnot b bell29
measure bell29
cnot bell29 bell28
cnot bell28 e
H bell28
measure bell28
cz bell28 b
H bell30
cnot bell30 bell31
cnot b bell31
measure bell31
cnot bell31 bell30
cnot bell30 d
H bell30
measure bell30
cz bell30 b
swap a b
H d
T d
H bell32
cnot bell32 bell33
cnot b bell33
measure bell33
cnot bell33 bell32
cnot bell32 d
T d
H bell34
cnot bell34 bell35
cnot c bell35
measure bell35
cnot bell35 bell34
cnot bell34 d
T* d
cnot bell32 d
H bell32
measure bell32
cz bell32 b
T* d
cnot bell34 d
H bell34
measure bell34
cz bell34 c
H d
T* c
Z c
H bell36
cnot bell36 bell37
cnot b bell37
measure bell37
cnot bell37 bell36
cnot bell36 c
T* c
Z c
cnot bell36 c
H bell36
measure bell36
cz bell36 b
H bell38
cnot bell38 bell39
cnot b bell39
measure bell39
cnot bell39 bell38
cnot bell38 f
H bell38
measure bell38
cz bell38 b
H c
T c
H bell40
cnot bell40 bell41
cnot e bell41
measure bell41
cnot bell41 bell40
cnot bell40 c
T c
H bell42
cnot bell42 bell43
cnot f bell43
measure bell43
cnot bell43 bell42
cnot bell42 c
T* c
cnot bell40 c
H bell40
measure bell40
cz bell40 e
T* c
cnot bell42 c
H bell42
measure bell42
cz bell42 f
H c
H 0
T 0
H bell44
cnot bell44 bell45
cnot c bell45
measure bell45
cnot bell45 bell44
cnot bell44 0
T* 0
H bell46
cnot bell46 bell47
cnot e bell47
measure bell47
cnot bell47 bell46
cnot bell46 0
T* 0
cnot bell44 0
T 0
cnot bell46 0
H 0
Z b
X b
H b
T b
H bell48
cnot bell48 bell49
cnot 0 bell49
measure bell49
cnot bell49 bell48
cnot bell48 b
T* b
H bell50
cnot bell50 bell51
cnot f bell51
measure bell51
cnot bell51 bell50
cnot bell50 b
T b
cnot bell48 b
H bell48
measure bell48
cz bell48 0
T* b
cnot bell50 b
H bell50
measure bell50
cz bell50 f
H b
T 0
H bell52
cnot bell52 bell53
cnot f bell53
measure bell53
cnot bell53 bell52
cnot bell52 0
T* 0
cnot bell52 0
H bell52
measure bell52
cz bell52 f
H 0
T* 0
cnot bell44 0
T 0
cnot bell46 0
T 0
cnot bell44 0
H bell44
measure bell44
cz bell44 c
T* 0
cnot bell46 0
H bell46
measure bell46
cz bell46 e
H 0
H bell54
cnot bell54 bell55
cnot e bell55
measure bell55
cnot bell55 bell54
cnot bell54 c
H bell54
measure bell54
cz bell54 e
S f
H bell56
cnot bell56 bell57
cnot e bell57
measure bell57
cnot bell57 bell56
cnot bell56 f
T f
T* a
H bell58
cnot bell58 bell59
cnot f bell59
measure bell59
cnot bell59 bell58
cnot bell58 c
H bell58
measure bell58
cz bell58 f
cnot bell56 f
H bell56
measure bell56
cz bell56 e
H bell60
cnot bell60 bell61
cnot f bell61
measure bell61
cnot bell61 bell60
cnot bell60 a
H bell60
measure bell60
cz bell60 f
H bell62
cnot bell62 bell63
cnot a bell63
measure bell63
cnot bell63 bell62
cnot bell62 d
H bell62
measure bell62
cz bell62 a
H f
T f
H bell64
cnot bell64 bell65
cnot b bell65
measure bell65
cnot bell65 bell64
cnot bell64 f
T* f
H bell66
cnot bell66 bell67
cnot c bell67
measure bell67
cnot bell67 bell66
cnot bell66 f
T f
cnot bell64 f
H bell64
measure bell64
cz bell64 b
T* f
cnot bell66 f
H bell68
cnot bell68 bell69
cnot d bell69
measure bell69
cnot bell69 bell68
cnot bell68 b
H bell68
measure bell68
cz bell68 d
H bell70
cnot bell70 bell71
cnot d bell71
measure bell71
cnot bell71 bell70
cnot bell70 e
H bell70
measure bell70
cz bell70 d
H bell72
cnot bell72 bell73
cnot e bell73
measure bell73
cnot bell73 bell72
cnot bell72 a
H bell72
measure bell72
cz bell72 e
T f
cnot bell66 f
T* f
H bell74
cnot bell74 bell75
cnot e bell75
measure bell75
cnot bell75 bell74
cnot bell74 f
T f
cnot bell66 f
H bell66
measure bell66
cz bell66 c
T* f
cnot bell74 f
H bell74
measure bell74
cz bell74 e
H f
H bell76
cnot bell76 bell77
cnot b bell77
measure bell77
cnot bell77 bell76
cnot bell76 d
T d
H bell78
cnot bell78 bell79
cnot c bell79
measure bell79
cnot bell79 bell78
cnot bell78 d
T* d
H bell80
cnot bell80 bell81
cnot e bell81
measure bell81
cnot bell81 bell80
cnot bell80 d
cnot bell78 d
H bell78
measure bell78
cz bell78 c
cnot bell76 d
T* d
H bell82
cnot bell82 bell83
cnot f bell83
measure bell83
cnot bell83 bell82
cnot bell82 c
H bell82
measure bell82
cz bell82 f
cnot bell80 d
H bell80
measure bell80
cz bell80 e
H bell84
cnot bell84 bell85
cnot e bell85
measure bell85
cnot bell85 bell84
cnot bell84 f
H bell84
measure bell84
cz bell84 e
X d
H d
T d
cnot bell76 d
T d
H bell86
cnot bell86 bell87
cnot e bell87
measure bell87
cnot bell87 bell86
cnot bell86 d
T* d
cnot bell76 d
H bell76
measure bell76
cz bell76 b
T* d
cnot bell86 d
H bell86
measure bell86
cz bell86 e
H d
H bell88
cnot bell88 bell89
cnot c bell89
measure bell89
cnot bell89 bell88
cnot bell88 f
T* f
H bell90
cnot bell90 bell91
cnot e bell91
measure bell91
cnot bell91 bell90
cnot bell90 f
S f
cnot bell90 f
H bell90
measure bell90
cz bell90 e
cnot bell88 f
H bell88
measure bell88
cz bell88 c
H f
T f
H bell92
cnot bell92 bell93
cnot a bell93
measure bell93
cnot bell93 bell92
cnot bell92 f
T f
H bell94
cnot bell94 bell95
cnot d bell95
measure bell95
cnot bell95 bell94
cnot bell94 f
T* f
cnot bell92 f
H bell92
measure bell92
cz bell92 a
T* f
cnot bell94 f
H bell94
measure bell94
cz bell94 d
H f
T* a
H bell96
cnot bell96 bell97
cnot d bell97
measure bell97
cnot bell97 bell96
cnot bell96 a
T a
cnot bell96 a
H bell96
measure bell96
cz bell96 d
H bell98
cnot bell98 bell99
cnot a bell99
measure bell99
cnot bell99 bell98
cnot bell98 c
H bell98
measure bell98
cz bell98 a
H a
T a
H bell100
cnot bell100 bell101
cnot b bell101
measure bell101
cnot bell101 bell100
cnot bell100 a
T a
H bell102
cnot bell102 bell103
cnot e bell103
measure bell103
cnot bell103 bell102
cnot bell102 a
T* a
cnot bell100 a
H bell100
measure bell100
cz bell100 b
T* a
cnot bell102 a
H bell102
measure bell102
cz bell102 e
H a
S* b
H bell104
cnot bell104 bell105
cnot e bell105
measure bell105
cnot bell105 bell104
cnot bell104 b
S b
H bell106
cnot bell106 bell107
cnot d bell107
measure bell107
cnot bell107 bell106
cnot bell106 c
H bell106
measure bell106
cz bell106 d
cnot bell104 b
H bell104
measure bell104
cz bell104 e
X b
H b
T b
H bell108
cnot bell108 bell109
cnot a bell109
measure bell109
cnot bell109 bell108
cnot bell108 b
T* b
H bell110
cnot bell110 bell111
cnot c bell111
measure bell111
cnot bell111 bell110
cnot bell110 b
T b
cnot bell108 b
H bell108
measure bell108
cz bell108 a
T* b
cnot bell110 b
H bell110
measure bell110
cz bell110 c
H b
T a
T c
H bell112
cnot bell112 bell113
cnot a bell113
measure bell113
cnot bell113 bell112
cnot bell112 c
H bell112
measure bell112
cz bell112 a
T* c
T d
T* e
Z e
H bell114
cnot bell114 bell115
cnot b bell115
measure bell115
cnot bell115 bell114
cnot bell114 a
H bell114
measure bell114
cz bell114 b
H bell116
cnot bell116 bell117
cnot f bell117
measure bell117
cnot bell117 bell116
cnot bell116 d
H bell116
measure bell116
cz bell116 f
H bell118
cnot bell118 bell119
cnot f bell119
measure bell119
cnot bell119 bell118
cnot bell118 e
H bell118
measure bell118
cz bell118 f
H bell120
cnot bell120 bell121
cnot d bell121
measure bell121
cnot bell121 bell120
cnot bell120 e
H bell120
measure bell120
cz bell120 d
H bell122
cnot bell122 bell123
cnot c bell123
measure bell123
cnot bell123 bell122
H bell124
cnot bell124 bell125
cnot e bell125
measure bell125
cnot bell125 bell124
cnot bell122 bell124
H bell122
measure bell122
cz bell122 c
cnot b bell124
H bell126
cnot bell126 bell127
cnot a bell127
measure bell127
cnot bell127 bell126
cnot bell126 bell124
H bell128
cnot bell128 bell129
cnot bell124 bell129
measure bell129
cnot bell129 bell128
reset bell129
cnot e bell128
cnot bell128 e
H bell128
measure bell128
cz bell128 a
cz bell128 b
cz bell128 c
H bell124
measure bell124
cz bell124 e
H bell126
measure bell126
cz bell126 a
H bell130
cnot bell130 bell131
cnot a bell131
measure bell131
cnot bell131 bell130
cnot bell130 c
H bell130
measure bell130
cz bell130 a
H bell132
cnot bell132 bell133
cnot a bell133
measure bell133
cnot bell133 bell132
cnot bell132 b
H bell132
measure bell132
cz bell132 a
X c
X f
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
END
