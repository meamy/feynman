# Hyperedge cut (ebits): 51

# Actual ebits used (Synthesis): 51
# Distribution Verification: PASS
# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/fprenorm.qc):
#   Qubits: 10
#   H: 32
#   T: 112
#   X: 1
#   cnot: 121
#   Depth: 121
#   T depth: 50
# Result (22.212ms):
#   Qubits: 112
#   H: 132
#   S: 5
#   T: 87
#   X: 1
#   cnot: 291
#   cz: 51
#   measure: 102
#   reset: 102
#   swap: 4
#   Depth: 281
#   T depth: 65


# Result Circuit
.v q1 q2 a1 a2 a3 x1 x2 x3 x4 t bell0 bell1 bell10 bell100 bell101 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i x1 x2 x3 x4
.o q1 q2 a1 a2 a3 x1 x2 x3 x4 t
BEGIN 
H bell0
cnot bell0 bell1
cnot x1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 a1
H bell0
measure bell0
cz bell0 x1
swap t x1
swap a1 x1
H q1
T q1
H bell2
cnot bell2 bell3
cnot t bell3
measure bell3
cnot bell3 bell2
cnot bell2 q1
T q1
H bell4
cnot bell4 bell5
cnot x2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 q1
T* q1
cnot bell2 q1
H bell2
measure bell2
cz bell2 t
T* q1
cnot bell4 q1
H bell4
measure bell4
cz bell4 x2
H q1
H bell6
cnot bell6 bell7
cnot q1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 t
H bell6
measure bell6
cz bell6 q1
H q2
T q2
H bell8
cnot bell8 bell9
cnot t bell9
measure bell9
cnot bell9 bell8
cnot bell8 q2
T q2
H bell10
cnot bell10 bell11
cnot x3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 q2
T* q2
cnot bell8 q2
H bell8
measure bell8
cz bell8 t
T* q2
cnot bell10 q2
H q2
H bell12
cnot bell12 bell13
cnot q2 bell13
measure bell13
cnot bell13 bell12
cnot bell12 t
H q1
T q1
H bell14
cnot bell14 bell15
cnot t bell15
measure bell15
cnot bell15 bell14
cnot bell14 q1
T q1
H bell16
cnot bell16 bell17
cnot x4 bell17
measure bell17
cnot bell17 bell16
cnot bell16 q1
T* q1
cnot bell14 q1
H bell14
measure bell14
cz bell14 t
T* q1
cnot bell16 q1
H q1
cnot bell12 t
T* t
cnot bell10 t
T t
cnot bell10 t
H bell10
measure bell10
cz bell10 x3
cnot bell12 t
H bell12
measure bell12
cz bell12 q2
H q2
T q2
H bell18
cnot bell18 bell19
cnot t bell19
measure bell19
cnot bell19 bell18
cnot bell18 q2
T q2
cnot bell16 q2
T* q2
cnot bell18 q2
H bell18
measure bell18
cz bell18 t
T* q2
cnot bell16 q2
H q2
S* t
cnot bell16 t
S t
cnot bell16 t
H bell16
measure bell16
cz bell16 x4
X t
H t
T t
H bell20
cnot bell20 bell21
cnot q1 bell21
measure bell21
cnot bell21 bell20
cnot bell20 t
T* t
H bell22
cnot bell22 bell23
cnot q2 bell23
measure bell23
cnot bell23 bell22
cnot bell22 t
T t
cnot bell20 t
T* t
cnot bell22 t
H t
H bell24
cnot bell24 bell25
cnot a2 bell25
measure bell25
cnot bell25 bell24
cnot bell24 a1
H a3
T a3
H bell26
cnot bell26 bell27
cnot a1 bell27
measure bell27
cnot bell27 bell26
cnot bell26 a3
T* a3
cnot bell20 a3
T a3
cnot bell26 a3
H bell26
measure bell26
cz bell26 a1
T* a3
cnot bell20 a3
H a3
H bell28
cnot bell28 bell29
cnot x1 bell29
measure bell29
cnot bell29 bell28
cnot bell28 a1
cnot bell24 a1
H bell24
measure bell24
cz bell24 a2
cnot bell28 a3
H bell28
measure bell28
cz bell28 x1
H bell30
cnot bell30 bell31
cnot a3 bell31
measure bell31
cnot bell31 bell30
cnot bell30 x1
swap a2 x1
swap a1 x1
H bell32
cnot bell32 bell33
cnot a1 bell33
measure bell33
cnot bell33 bell32
cnot bell32 a2
H x1
T x1
cnot bell30 x1
T* x1
cnot bell20 x1
T x1
cnot bell30 x1
H bell30
measure bell30
cz bell30 a3
T* x1
cnot bell20 x1
H x1
T a3
H bell34
cnot bell34 bell35
cnot a2 bell35
measure bell35
cnot bell35 bell34
cnot bell34 a3
cnot bell32 a3
T* a3
cnot bell20 a3
cnot bell34 a3
cnot bell32 a3
T* a3
T x2
H bell36
cnot bell36 bell37
cnot x1 bell37
measure bell37
cnot bell37 bell36
cnot bell36 a3
H bell36
measure bell36
cz bell36 x1
cnot bell20 a3
H bell38
cnot bell38 bell39
cnot x2 bell39
measure bell39
cnot bell39 bell38
cnot bell38 x1
H bell38
measure bell38
cz bell38 x2
H x2
T x2
cnot bell20 x2
T* x2
H bell40
cnot bell40 bell41
cnot x1 bell41
measure bell41
cnot bell41 bell40
cnot bell40 x2
T x2
cnot bell20 x2
T* x2
cnot bell40 x2
H bell40
measure bell40
cz bell40 x1
H x2
T x1
H bell42
cnot bell42 bell43
cnot a3 bell43
measure bell43
cnot bell43 bell42
cnot bell42 x1
cnot bell34 x1
cnot bell32 x1
T x1
cnot bell20 x1
cnot bell42 x1
cnot bell34 x1
H bell34
measure bell34
cz bell34 a2
cnot bell32 x1
H bell32
measure bell32
cz bell32 a1
T* x1
T x3
H bell44
cnot bell44 bell45
cnot x2 bell45
measure bell45
cnot bell45 bell44
cnot bell44 x1
H bell44
measure bell44
cz bell44 x2
H bell46
cnot bell46 bell47
cnot x3 bell47
measure bell47
cnot bell47 bell46
cnot bell46 x2
H bell46
measure bell46
cz bell46 x3
cnot bell20 x1
H x3
T x3
cnot bell20 x3
T* x3
H bell48
cnot bell48 bell49
cnot x2 bell49
measure bell49
cnot bell49 bell48
cnot bell48 x3
T x3
cnot bell20 x3
T* x3
cnot bell48 x3
H bell48
measure bell48
cz bell48 x2
H x3
T x2
cnot bell20 x2
T* x2
S x4
H bell50
cnot bell50 bell51
cnot x3 bell51
measure bell51
cnot bell51 bell50
cnot bell50 x2
H bell50
measure bell50
cz bell50 x3
H bell52
cnot bell52 bell53
cnot x4 bell53
measure bell53
cnot bell53 bell52
cnot bell52 x3
H bell52
measure bell52
cz bell52 x4
cnot bell20 x2
H x4
T x4
cnot bell20 x4
T* x4
H bell54
cnot bell54 bell55
cnot x3 bell55
measure bell55
cnot bell55 bell54
cnot bell54 x4
T x4
cnot bell20 x4
T* x4
cnot bell54 x4
H bell54
measure bell54
cz bell54 x3
H x4
T a1
cnot bell20 a1
T* a1
cnot bell42 a1
H bell42
measure bell42
cz bell42 a3
cnot bell20 a1
H bell56
cnot bell56 bell57
cnot x4 bell57
measure bell57
cnot bell57 bell56
cnot bell56 x3
H bell56
measure bell56
cz bell56 x4
H a3
T a3
H bell58
cnot bell58 bell59
cnot a1 bell59
measure bell59
cnot bell59 bell58
cnot bell58 a3
T* a3
cnot bell22 a3
T a3
cnot bell58 a3
H bell58
measure bell58
cz bell58 a1
T* a3
cnot bell22 a3
H a3
H bell60
cnot bell60 bell61
cnot a3 bell61
measure bell61
cnot bell61 bell60
cnot bell60 a1
H bell60
measure bell60
cz bell60 a3
H bell62
cnot bell62 bell63
cnot x1 bell63
measure bell63
cnot bell63 bell62
cnot bell62 a2
H bell62
measure bell62
cz bell62 x1
H x1
T x1
H bell64
cnot bell64 bell65
cnot a2 bell65
measure bell65
cnot bell65 bell64
cnot bell64 x1
T* x1
cnot bell22 x1
T x1
cnot bell64 x1
H bell64
measure bell64
cz bell64 a2
T* x1
cnot bell22 x1
H x1
H bell66
cnot bell66 bell67
cnot a1 bell67
measure bell67
cnot bell67 bell66
cnot bell66 a3
T a3
cnot bell22 a3
T* a3
H bell68
cnot bell68 bell69
cnot x1 bell69
measure bell69
cnot bell69 bell68
cnot bell68 a2
H bell68
measure bell68
cz bell68 x1
cnot bell22 a3
H bell70
cnot bell70 bell71
cnot x2 bell71
measure bell71
cnot bell71 bell70
cnot bell70 a3
H bell70
measure bell70
cz bell70 x2
cnot bell66 a3
H bell66
measure bell66
cz bell66 a1
H x2
T x2
H bell72
cnot bell72 bell73
cnot a3 bell73
measure bell73
cnot bell73 bell72
cnot bell72 x2
T* x2
cnot bell22 x2
T x2
cnot bell72 x2
H bell72
measure bell72
cz bell72 a3
T* x2
cnot bell22 x2
H bell22
measure bell22
cz bell22 q2
H x2
H bell74
cnot bell74 bell75
cnot a2 bell75
measure bell75
cnot bell75 bell74
cnot bell74 x1
T x1
H bell76
cnot bell76 bell77
cnot x3 bell77
measure bell77
cnot bell77 bell76
cnot bell76 x4
T x4
cnot bell20 x4
T* x4
H bell78
cnot bell78 bell79
cnot x1 bell79
measure bell79
cnot bell79 bell78
cnot bell78 q2
T* q2
H bell80
cnot bell80 bell81
cnot x2 bell81
measure bell81
cnot bell81 bell80
cnot bell80 a3
H bell80
measure bell80
cz bell80 x2
cnot bell78 q2
H bell78
measure bell78
cz bell78 x1
cnot bell76 x1
cnot bell76 x4
H bell76
measure bell76
cz bell76 x3
cnot bell20 x4
H bell20
measure bell20
cz bell20 q1
cnot bell74 x1
H bell74
measure bell74
cz bell74 a2
H x3
T x3
H bell82
cnot bell82 bell83
cnot q2 bell83
measure bell83
cnot bell83 bell82
cnot bell82 x3
T* x3
H bell84
cnot bell84 bell85
cnot x1 bell85
measure bell85
cnot bell85 bell84
cnot bell84 x3
T x3
cnot bell82 x3
T* x3
cnot bell84 x3
H bell84
measure bell84
cz bell84 x1
H x3
H bell86
cnot bell86 bell87
cnot a3 bell87
measure bell87
cnot bell87 bell86
cnot bell86 x2
T x2
cnot bell82 x2
T* x2
H bell88
cnot bell88 bell89
cnot x3 bell89
measure bell89
cnot bell89 bell88
cnot bell88 x1
H bell88
measure bell88
cz bell88 x3
H bell90
cnot bell90 bell91
cnot x4 bell91
measure bell91
cnot bell91 bell90
cnot bell90 x2
H bell90
measure bell90
cz bell90 x4
cnot bell82 x2
cnot bell86 x2
H bell86
measure bell86
cz bell86 a3
H x4
T x4
cnot bell82 x4
T* x4
H bell92
cnot bell92 bell93
cnot x2 bell93
measure bell93
cnot bell93 bell92
cnot bell92 x4
T x4
cnot bell82 x4
H bell82
measure bell82
cz bell82 q2
T* x4
cnot bell92 x4
H bell92
measure bell92
cz bell92 x2
H x4
S* q1
S* q2
H bell94
cnot bell94 bell95
cnot q1 bell95
measure bell95
cnot bell95 bell94
cnot bell94 q2
T* q2
T x2
H bell96
cnot bell96 bell97
cnot q2 bell97
measure bell97
cnot bell97 bell96
cnot bell96 x2
cnot bell94 x2
T* x2
H bell98
cnot bell98 bell99
cnot x1 bell99
measure bell99
cnot bell99 bell98
cnot bell98 x3
T x3
cnot bell96 x3
cnot bell94 x3
T* x3
H bell100
cnot bell100 bell101
cnot x4 bell101
measure bell101
cnot bell101 bell100
cnot bell100 x2
H bell100
measure bell100
cz bell100 x4
cnot bell98 x3
H bell98
measure bell98
cz bell98 x1
cnot bell96 x3
cnot bell96 x2
H bell96
measure bell96
cz bell96 q2
cnot bell94 x3
cnot bell94 x2
cnot bell94 q2
H bell94
measure bell94
cz bell94 q1
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
END
