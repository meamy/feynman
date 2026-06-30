# Hyperedge cut (ebits): 43

# Actual ebits used (Synthesis): 56
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/csum_mux_9.qc):
#   Qubits: 30
#   H: 28
#   T: 196
#   X: 28
#   cnot: 168
#   Depth: 53
#   T depth: 24
# Result (48.357ms):
#   Qubits: 142
#   H: 140
#   S: 28
#   T: 84
#   cnot: 338
#   cz: 56
#   measure: 112
#   reset: 112
#   Depth: 91
#   T depth: 16


# Result Circuit
.v c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 a0 a1 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 b0 b1 b2 b3 e70 e71 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 e70 e71
.o c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 a0 a1 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 b0 b1 b2 b3 e70 e71
BEGIN 
H e10
H e11
H a0
H a1
H e30
H e31
H e50
H e51
H b0
H b1
H b2
H b3
H e70
H e71
S e10
H bell0
cnot bell0 bell1
cnot c00 bell1
measure bell1
cnot bell1 bell0
cnot bell0 e10
H bell2
cnot bell2 bell3
cnot c10 bell3
measure bell3
cnot bell3 bell2
cnot bell2 e10
T* e10
cnot bell0 e10
T* e10
H bell4
cnot bell4 bell5
cnot c11 bell5
measure bell5
cnot bell5 bell4
cnot bell4 e10
cnot bell2 e10
T* e10
cnot bell0 e10
T e10
cnot bell4 e10
cnot bell0 e10
H bell0
measure bell0
cz bell0 c00
H e10
S e11
H bell6
cnot bell6 bell7
cnot c01 bell7
measure bell7
cnot bell7 bell6
cnot bell6 e11
cnot bell2 e11
T* e11
cnot bell6 e11
T* e11
cnot bell4 e11
cnot bell2 e11
H bell2
measure bell2
cz bell2 c10
T* e11
cnot bell6 e11
T e11
cnot bell4 e11
H bell4
measure bell4
cz bell4 c11
cnot bell6 e11
H bell6
measure bell6
cz bell6 c01
H e11
S a0
H bell8
cnot bell8 bell9
cnot c20 bell9
measure bell9
cnot bell9 bell8
cnot bell8 a0
H bell10
cnot bell10 bell11
cnot c30 bell11
measure bell11
cnot bell11 bell10
cnot bell10 a0
T* a0
cnot bell8 a0
T* a0
H bell12
cnot bell12 bell13
cnot c31 bell13
measure bell13
cnot bell13 bell12
cnot bell12 a0
cnot bell10 a0
T* a0
cnot bell8 a0
T a0
cnot bell8 a0
H bell8
measure bell8
cz bell8 c20
cnot bell12 a0
H a0
S a1
H bell14
cnot bell14 bell15
cnot c21 bell15
measure bell15
cnot bell15 bell14
cnot bell14 a1
cnot bell10 a1
T* a1
cnot bell14 a1
T* a1
cnot bell12 a1
cnot bell10 a1
H bell10
measure bell10
cz bell10 c30
T* a1
cnot bell14 a1
T a1
cnot bell14 a1
H bell14
measure bell14
cz bell14 c21
cnot bell12 a1
H bell12
measure bell12
cz bell12 c31
H a1
S e50
H bell16
cnot bell16 bell17
cnot c40 bell17
measure bell17
cnot bell17 bell16
cnot bell16 e50
H bell18
cnot bell18 bell19
cnot c50 bell19
measure bell19
cnot bell19 bell18
cnot bell18 e50
T* e50
cnot bell16 e50
T* e50
H bell20
cnot bell20 bell21
cnot c51 bell21
measure bell21
cnot bell21 bell20
cnot bell20 e50
cnot bell18 e50
T* e50
cnot bell16 e50
T e50
cnot bell20 e50
cnot bell16 e50
H bell16
measure bell16
cz bell16 c40
H e50
S e51
H bell22
cnot bell22 bell23
cnot c41 bell23
measure bell23
cnot bell23 bell22
cnot bell22 e51
cnot bell18 e51
T* e51
cnot bell22 e51
T* e51
cnot bell20 e51
cnot bell18 e51
H bell18
measure bell18
cz bell18 c50
T* e51
cnot bell22 e51
T e51
cnot bell20 e51
H bell20
measure bell20
cz bell20 c51
cnot bell22 e51
H bell22
measure bell22
cz bell22 c41
H e51
S b0
H bell24
cnot bell24 bell25
cnot c60 bell25
measure bell25
cnot bell25 bell24
cnot bell24 b0
cnot c70 b0
T* b0
cnot bell24 b0
T* b0
H bell26
cnot bell26 bell27
cnot c71 bell27
measure bell27
cnot bell27 bell26
cnot bell26 b0
cnot c70 b0
T* b0
cnot bell24 b0
T b0
cnot bell24 b0
cnot bell26 b0
H bell26
measure bell26
cz bell26 c71
H b0
S b1
H bell28
cnot bell28 bell29
cnot c61 bell29
measure bell29
cnot bell29 bell28
cnot bell28 b1
H bell30
cnot bell30 bell31
cnot c70 bell31
measure bell31
cnot bell31 bell30
cnot bell30 b1
T* b1
cnot bell28 b1
T* b1
H bell32
cnot bell32 bell33
cnot c71 bell33
measure bell33
cnot bell33 bell32
cnot bell32 b1
cnot bell30 b1
H bell30
measure bell30
cz bell30 c70
T* b1
cnot bell28 b1
T b1
cnot bell28 b1
H bell28
measure bell28
cz bell28 c61
cnot bell32 b1
H bell32
measure bell32
cz bell32 c71
H b1
S e30
H bell34
cnot bell34 bell35
cnot a0 bell35
measure bell35
cnot bell35 bell34
cnot bell34 e30
T* e30
H bell36
cnot bell36 bell37
cnot e10 bell37
measure bell37
cnot bell37 bell36
cnot bell36 e30
T* e30
cnot bell34 e30
H bell38
cnot bell38 bell39
cnot a1 bell39
measure bell39
cnot bell39 bell38
cnot bell38 e30
T e30
cnot bell36 e30
H bell36
measure bell36
cz bell36 e10
T* e30
cnot bell38 e30
H e30
S e31
cnot bell34 e31
T* e31
H bell40
cnot bell40 bell41
cnot e11 bell41
measure bell41
cnot bell41 bell40
cnot bell40 e31
T* e31
cnot bell34 e31
H bell34
measure bell34
cz bell34 a0
cnot bell38 e31
T e31
cnot bell40 e31
H bell40
measure bell40
cz bell40 e11
T* e31
cnot bell38 e31
H bell38
measure bell38
cz bell38 a1
H e31
S b2
H bell42
cnot bell42 bell43
cnot b0 bell43
measure bell43
cnot bell43 bell42
cnot bell42 b2
T* b2
H bell44
cnot bell44 bell45
cnot e50 bell45
measure bell45
cnot bell45 bell44
cnot bell44 b2
T* b2
cnot bell42 b2
H bell46
cnot bell46 bell47
cnot b1 bell47
measure bell47
cnot bell47 bell46
cnot bell46 b2
T b2
cnot bell44 b2
H bell44
measure bell44
cz bell44 e50
T* b2
cnot bell46 b2
H b2
S b3
cnot bell42 b3
T* b3
H bell48
cnot bell48 bell49
cnot e51 bell49
measure bell49
cnot bell49 bell48
cnot bell48 b3
T* b3
cnot bell42 b3
H bell42
measure bell42
cz bell42 b0
cnot bell46 b3
T b3
cnot bell48 b3
H bell48
measure bell48
cz bell48 e51
T* b3
cnot bell46 b3
H bell46
measure bell46
cz bell46 b1
H b3
S e70
H bell50
cnot bell50 bell51
cnot b2 bell51
measure bell51
cnot bell51 bell50
cnot bell50 e70
T* e70
H bell52
cnot bell52 bell53
cnot e30 bell53
measure bell53
cnot bell53 bell52
cnot bell52 e70
T* e70
cnot bell50 e70
H bell50
measure bell50
cz bell50 b2
H bell54
cnot bell54 bell55
cnot b3 bell55
measure bell55
cnot bell55 bell54
cnot bell54 e70
T e70
cnot bell52 e70
H bell52
measure bell52
cz bell52 e30
T* e70
cnot bell54 e70
H bell54
measure bell54
cz bell54 b3
H e70
S e71
H bell56
cnot bell56 bell57
cnot b2 bell57
measure bell57
cnot bell57 bell56
cnot bell56 e71
T* e71
H bell58
cnot bell58 bell59
cnot e31 bell59
measure bell59
cnot bell59 bell58
cnot bell58 e71
T* e71
cnot bell56 e71
H bell56
measure bell56
cz bell56 b2
H bell60
cnot bell60 bell61
cnot b3 bell61
measure bell61
cnot bell61 bell60
cnot bell60 e71
T e71
cnot bell58 e71
H bell58
measure bell58
cz bell58 e31
T* e71
cnot bell60 e71
H bell60
measure bell60
cz bell60 b3
H e71
S c10
H bell62
cnot bell62 bell63
cnot c00 bell63
measure bell63
cnot bell63 bell62
cnot bell62 c10
T c10
H bell64
cnot bell64 bell65
cnot c01 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c10
cnot bell62 c10
T c10
S c11
cnot bell62 c11
T* c11
cnot bell64 c11
cnot bell62 c11
H bell62
measure bell62
cz bell62 c00
T* c11
S c30
cnot c20 c30
T c30
H bell66
cnot bell66 bell67
cnot c30 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c21
H bell68
cnot bell68 bell69
cnot c20 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c21
T c21
S c31
cnot bell68 c31
T* c31
cnot bell66 c31
cnot c21 c31
T* c31
S c50
cnot c40 c50
T c50
H bell70
cnot bell70 bell71
cnot c50 bell71
measure bell71
cnot bell71 bell70
cnot bell70 c41
H bell72
cnot bell72 bell73
cnot c40 bell73
measure bell73
cnot bell73 bell72
cnot bell72 c41
T c41
S c51
cnot bell72 c51
T* c51
cnot bell70 c51
cnot c41 c51
T* c51
S c70
cnot bell24 c70
H bell24
measure bell24
cz bell24 c60
T c70
H bell74
cnot bell74 bell75
cnot c70 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c61
H bell76
cnot bell76 bell77
cnot c60 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c61
T c61
S c71
cnot bell76 c71
H bell76
measure bell76
cz bell76 c60
T* c71
cnot bell74 c71
cnot c61 c71
T* c71
S a0
H bell78
cnot bell78 bell79
cnot a0 bell79
measure bell79
cnot bell79 bell78
cnot bell78 e10
T e10
S a1
H bell80
cnot bell80 bell81
cnot e10 bell81
measure bell81
cnot bell81 bell80
cnot bell80 a1
cnot a0 a1
T* a1
cnot bell78 e11
T e11
cnot e10 e11
H bell82
cnot bell82 bell83
cnot a1 bell83
measure bell83
cnot bell83 bell82
cnot bell82 e11
H bell82
measure bell82
cz bell82 a1
T* e11
S b2
H bell84
cnot bell84 bell85
cnot b2 bell85
measure bell85
cnot bell85 bell84
cnot bell84 e30
T e30
S b3
H bell86
cnot bell86 bell87
cnot e30 bell87
measure bell87
cnot bell87 bell86
cnot bell86 b3
cnot b2 b3
T* b3
cnot bell84 e31
T e31
cnot e30 e31
H bell88
cnot bell88 bell89
cnot b3 bell89
measure bell89
cnot bell89 bell88
cnot bell88 e31
H bell88
measure bell88
cz bell88 b3
T* e31
S b0
H bell90
cnot bell90 bell91
cnot b0 bell91
measure bell91
cnot bell91 bell90
cnot bell90 e50
H bell90
measure bell90
cz bell90 b0
T e50
S b1
H bell92
cnot bell92 bell93
cnot e50 bell93
measure bell93
cnot bell93 bell92
cnot bell92 b1
H bell94
cnot bell94 bell95
cnot b0 bell95
measure bell95
cnot bell95 bell94
cnot bell94 b1
H bell94
measure bell94
cz bell94 b0
T* b1
H bell96
cnot bell96 bell97
cnot b0 bell97
measure bell97
cnot bell97 bell96
cnot bell96 e51
T e51
cnot e50 e51
H bell98
cnot bell98 bell99
cnot b1 bell99
measure bell99
cnot bell99 bell98
cnot bell98 e51
H bell98
measure bell98
cz bell98 b1
T* e51
cnot bell80 a1
H bell80
measure bell80
cz bell80 e10
cnot bell86 b3
H bell86
measure bell86
cz bell86 e30
cnot bell92 b1
H bell92
measure bell92
cz bell92 e50
cnot bell66 c21
H bell66
measure bell66
cz bell66 c30
cnot bell70 c41
H bell70
measure bell70
cz bell70 c50
cnot bell74 c61
H bell74
measure bell74
cz bell74 c70
H bell100
cnot bell100 bell101
cnot c60 bell101
measure bell101
cnot bell101 bell100
cnot bell100 c70
H bell100
measure bell100
cz bell100 c60
H bell102
cnot bell102 bell103
cnot c60 bell103
measure bell103
cnot bell103 bell102
cnot bell102 c61
H bell102
measure bell102
cz bell102 c60
cnot c61 c71
cnot c41 c51
cnot bell72 c51
cnot c40 c50
cnot bell72 c41
H bell72
measure bell72
cz bell72 c40
cnot bell68 c21
H bell68
measure bell68
cz bell68 c20
cnot c21 c31
cnot c20 c30
cnot bell64 c10
cnot bell64 c11
H bell64
measure bell64
cz bell64 c01
cnot b2 b3
H bell104
cnot bell104 bell105
cnot b1 bell105
measure bell105
cnot bell105 bell104
cnot bell104 e51
H bell104
measure bell104
cz bell104 b1
H bell106
cnot bell106 bell107
cnot b3 bell107
measure bell107
cnot bell107 bell106
cnot bell106 e31
H bell106
measure bell106
cz bell106 b3
cnot bell84 e30
H bell84
measure bell84
cz bell84 b2
cnot a0 a1
cnot bell96 e51
cnot bell96 e50
H bell96
measure bell96
cz bell96 b0
H bell108
cnot bell108 bell109
cnot a1 bell109
measure bell109
cnot bell109 bell108
cnot bell108 e11
H bell108
measure bell108
cz bell108 a1
cnot bell78 e10
H bell78
measure bell78
cz bell78 a0
H bell110
cnot bell110 bell111
cnot b0 bell111
measure bell111
cnot bell111 bell110
cnot bell110 b1
H bell110
measure bell110
cz bell110 b0
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
END
