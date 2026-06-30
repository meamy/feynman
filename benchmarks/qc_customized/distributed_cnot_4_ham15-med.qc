# Hyperedge cut (ebits): 41

# Actual ebits used (Synthesis): 57
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/ham15-med.qc):
#   Qubits: 17
#   H: 164
#   T: 574
#   cnot: 534
#   Depth: 667
#   T depth: 291
# Result (106.114ms):
#   Qubits: 131
#   H: 212
#   S: 33
#   T: 372
#   Z: 7
#   cnot: 622
#   cz: 57
#   measure: 114
#   reset: 114
#   swap: 1
#   Depth: 928
#   T depth: 280


# Result Circuit
.v a b c d e f g h i j k l m n o 0 1 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a b c d e f g h i j k l m n o
.o a b c d e f g h i j k l m n o
BEGIN 
H bell0
cnot bell0 bell1
cnot o bell1
measure bell1
cnot bell1 bell0
cnot bell0 j
H bell0
measure bell0
cz bell0 o
cnot n o
H 1
T 1
cnot l 1
T* 1
H bell2
cnot bell2 bell3
cnot m bell3
measure bell3
cnot bell3 bell2
cnot bell2 1
T 1
cnot l 1
T* 1
cnot bell2 1
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
H bell4
cnot bell4 bell5
cnot 0 bell5
measure bell5
cnot bell5 bell4
cnot bell4 e
T* e
H bell6
cnot bell6 bell7
cnot o bell7
measure bell7
cnot bell7 bell6
cnot bell6 e
T e
cnot bell4 e
H bell4
measure bell4
cz bell4 0
T* e
cnot bell6 e
H bell6
measure bell6
cz bell6 o
H e
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell2 1
T 1
cnot l 1
T* 1
cnot bell2 1
S l
cnot bell2 l
S* l
T o
cnot o l
cnot bell2 l
H o
T o
cnot bell2 o
T* o
cnot n o
T o
cnot bell2 o
T* o
cnot n o
H o
T* n
Z n
cnot bell2 n
T* n
cnot bell2 n
H n
T n
cnot l n
T* n
cnot o n
T n
cnot l n
T* n
cnot o n
H n
T 1
cnot l 1
T* 1
cnot bell2 1
T 1
cnot l 1
T* 1
cnot bell2 1
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
H bell8
cnot bell8 bell9
cnot 0 bell9
measure bell9
cnot bell9 bell8
cnot bell8 b
T* b
H bell10
cnot bell10 bell11
cnot o bell11
measure bell11
cnot bell11 bell10
cnot bell10 b
T b
cnot bell8 b
H bell8
measure bell8
cz bell8 0
T* b
cnot bell10 b
H bell10
measure bell10
cz bell10 o
H b
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell2 1
T 1
cnot l 1
T* 1
cnot bell2 1
H bell12
cnot bell12 bell13
cnot o bell13
measure bell13
cnot bell13 bell12
cnot bell12 k
H bell12
measure bell12
cz bell12 o
T 0
cnot l 0
T* 0
cnot bell2 0
T 0
cnot l 0
T* 0
cnot bell2 0
H 0
S o
cnot l o
T* o
cnot l o
H o
T o
cnot 0 o
T* o
cnot n o
T o
cnot 0 o
T* o
cnot n o
H o
T 0
cnot n 0
T* 0
cnot n 0
H 0
T 0
cnot l 0
T* 0
cnot bell2 0
T 0
cnot l 0
T* 0
cnot bell2 0
H j
T j
H bell14
cnot bell14 bell15
cnot l bell15
measure bell15
cnot bell15 bell14
cnot bell14 j
T* j
H bell16
cnot bell16 bell17
cnot o bell17
measure bell17
cnot bell17 bell16
cnot bell16 j
T j
cnot bell14 j
H bell14
measure bell14
cz bell14 l
T* j
cnot bell16 j
H bell16
measure bell16
cz bell16 o
T 1
cnot l 1
T* 1
cnot bell2 1
T 1
cnot l 1
T* 1
cnot bell2 1
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
H bell18
cnot bell18 bell19
cnot 0 bell19
measure bell19
cnot bell19 bell18
cnot bell18 f
T* f
H bell20
cnot bell20 bell21
cnot o bell21
measure bell21
cnot bell21 bell20
cnot bell20 f
T f
cnot bell18 f
H bell18
measure bell18
cz bell18 0
T* f
cnot bell20 f
H bell20
measure bell20
cz bell20 o
H f
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell2 1
T 1
cnot l 1
T* 1
cnot bell2 1
H bell2
measure bell2
cz bell2 m
H a
T a
H bell22
cnot bell22 bell23
cnot m bell23
measure bell23
cnot bell23 bell22
cnot bell22 a
T* a
H bell24
cnot bell24 bell25
cnot o bell25
measure bell25
cnot bell25 bell24
cnot bell24 a
T a
cnot bell22 a
H bell22
measure bell22
cz bell22 m
T* a
cnot bell24 a
T a
H bell26
cnot bell26 bell27
cnot n bell27
measure bell27
cnot bell27 bell26
cnot bell26 a
T* a
cnot bell24 a
T a
cnot bell26 a
H bell26
measure bell26
cz bell26 n
T* a
cnot bell24 a
T 1
cnot l 1
T* 1
H bell28
cnot bell28 bell29
cnot m bell29
measure bell29
cnot bell29 bell28
cnot bell28 1
T 1
cnot l 1
T* 1
cnot bell28 1
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
H bell30
cnot bell30 bell31
cnot 0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 a
T* a
cnot bell24 a
T a
cnot bell30 a
H bell30
measure bell30
cz bell30 0
T* a
cnot bell24 a
H bell24
measure bell24
cz bell24 o
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell28 1
T 1
cnot l 1
T* 1
cnot bell28 1
H bell28
measure bell28
cz bell28 m
H bell32
cnot bell32 bell33
cnot o bell33
measure bell33
cnot bell33 bell32
cnot bell32 m
H bell32
measure bell32
cz bell32 o
T 1
cnot l 1
T* 1
H bell34
cnot bell34 bell35
cnot m bell35
measure bell35
cnot bell35 bell34
cnot bell34 1
T 1
cnot l 1
T* 1
cnot bell34 1
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
H bell36
cnot bell36 bell37
cnot 0 bell37
measure bell37
cnot bell37 bell36
cnot bell36 d
T* d
H bell38
cnot bell38 bell39
cnot o bell39
measure bell39
cnot bell39 bell38
cnot bell38 d
T d
cnot bell36 d
H bell36
measure bell36
cz bell36 0
T* d
cnot bell38 d
H bell38
measure bell38
cz bell38 o
H d
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell34 1
T 1
cnot l 1
T* 1
cnot bell34 1
H bell34
measure bell34
cz bell34 m
T j
cnot m j
T* j
H bell40
cnot bell40 bell41
cnot o bell41
measure bell41
cnot bell41 bell40
cnot bell40 j
T j
cnot m j
T* j
cnot bell40 j
H bell40
measure bell40
cz bell40 o
H c
T c
H bell42
cnot bell42 bell43
cnot m bell43
measure bell43
cnot bell43 bell42
cnot bell42 c
T* c
H bell44
cnot bell44 bell45
cnot o bell45
measure bell45
cnot bell45 bell44
cnot bell44 c
T c
cnot bell42 c
H bell42
measure bell42
cz bell42 m
T* c
cnot bell44 c
T 1
cnot l 1
T* 1
H bell46
cnot bell46 bell47
cnot m bell47
measure bell47
cnot bell47 bell46
cnot bell46 1
T 1
cnot l 1
T* 1
cnot bell46 1
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
H bell48
cnot bell48 bell49
cnot 0 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c
T* c
cnot bell44 c
T c
cnot bell48 c
H bell48
measure bell48
cz bell48 0
T* c
cnot bell44 c
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell46 1
T 1
cnot l 1
T* 1
cnot bell46 1
T 0
cnot l 0
T* 0
cnot bell46 0
T 0
cnot l 0
T* 0
cnot bell46 0
H 0
Z n
cnot o n
T* n
cnot o n
H n
T n
cnot 0 n
T* n
cnot o n
T n
cnot 0 n
T* n
cnot o n
H n
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot l 0
T* 0
cnot bell46 0
T 0
cnot l 0
T* 0
cnot bell46 0
T 0
cnot bell46 0
T* 0
cnot n 0
T 0
cnot bell46 0
T* 0
cnot n 0
H 0
T c
H bell50
cnot bell50 bell51
cnot 0 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c
T* c
cnot bell44 c
T c
cnot bell50 c
H bell50
measure bell50
cz bell50 0
T* c
cnot bell44 c
H bell44
measure bell44
cz bell44 o
H c
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot bell46 0
T* 0
cnot n 0
T 0
cnot bell46 0
T* 0
cnot n 0
T 0
cnot bell46 0
T* 0
cnot n 0
T 0
cnot bell46 0
T* 0
cnot n 0
H 0
cnot bell46 l
S l
cnot o l
cnot bell46 l
T* l
cnot o l
H l
T l
cnot 0 l
T* l
cnot o l
T l
cnot 0 l
T* l
cnot o l
H l
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot bell46 0
T* 0
cnot n 0
T 0
cnot bell46 0
T* 0
cnot n 0
T a
H bell52
cnot bell52 bell53
cnot l bell53
measure bell53
cnot bell53 bell52
cnot bell52 a
T* a
H bell54
cnot bell54 bell55
cnot o bell55
measure bell55
cnot bell55 bell54
cnot bell54 a
T a
cnot bell52 a
H bell52
measure bell52
cz bell52 l
T* a
cnot bell54 a
H bell54
measure bell54
cz bell54 o
H a
T 1
cnot l 1
T* 1
cnot bell46 1
T 1
cnot l 1
T* 1
cnot bell46 1
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
H bell56
cnot bell56 bell57
cnot 0 bell57
measure bell57
cnot bell57 bell56
cnot bell56 g
T* g
H bell58
cnot bell58 bell59
cnot o bell59
measure bell59
cnot bell59 bell58
cnot bell58 g
T g
cnot bell56 g
H bell56
measure bell56
cz bell56 0
T* g
cnot bell58 g
H bell58
measure bell58
cz bell58 o
H g
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell46 1
T 1
cnot l 1
T* 1
cnot bell46 1
S* n
cnot bell46 n
Z n
cnot bell46 n
H n
T n
cnot l n
T* n
cnot o n
T n
cnot l n
T* n
cnot o n
H n
Z l
cnot bell46 l
S* l
cnot o l
cnot bell46 l
S* l
cnot o l
H l
T l
cnot n l
T* l
cnot o l
T l
cnot n l
T* l
cnot o l
H l
T 1
cnot l 1
T* 1
cnot bell46 1
T 1
cnot l 1
T* 1
cnot bell46 1
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
H bell60
cnot bell60 bell61
cnot 0 bell61
measure bell61
cnot bell61 bell60
cnot bell60 h
T* h
H bell62
cnot bell62 bell63
cnot o bell63
measure bell63
cnot bell63 bell62
cnot bell62 h
T h
cnot bell60 h
H bell60
measure bell60
cz bell60 0
T* h
cnot bell62 h
H bell62
measure bell62
cz bell62 o
H h
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell46 1
T 1
cnot l 1
T* 1
cnot bell46 1
H bell46
measure bell46
cz bell46 m
T 0
cnot l 0
T* 0
cnot n 0
T 0
cnot l 0
T* 0
cnot n 0
H 0
T* m
H bell64
cnot bell64 bell65
cnot l bell65
measure bell65
cnot bell65 bell64
cnot bell64 m
S* m
H bell66
cnot bell66 bell67
cnot o bell67
measure bell67
cnot bell67 bell66
cnot bell66 m
cnot bell64 m
S m
cnot bell66 m
H m
T m
H bell68
cnot bell68 bell69
cnot 0 bell69
measure bell69
cnot bell69 bell68
cnot bell68 m
T* m
cnot bell66 m
T m
cnot bell68 m
H bell68
measure bell68
cz bell68 0
T* m
cnot bell66 m
H m
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot l 0
T* 0
cnot n 0
T 0
cnot l 0
T* 0
cnot n 0
T 1
cnot l 1
T* 1
H bell70
cnot bell70 bell71
cnot m bell71
measure bell71
cnot bell71 bell70
cnot bell70 1
T 1
cnot l 1
T* 1
cnot bell70 1
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
H bell72
cnot bell72 bell73
cnot 0 bell73
measure bell73
cnot bell73 bell72
cnot bell72 j
T* j
cnot bell66 j
T j
cnot bell72 j
H bell72
measure bell72
cz bell72 0
T* j
cnot bell66 j
H j
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell70 1
T 1
cnot l 1
T* 1
cnot bell70 1
T 1
cnot l 1
T* 1
cnot bell70 1
T 1
cnot l 1
T* 1
cnot bell70 1
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
H bell74
cnot bell74 bell75
cnot 0 bell75
measure bell75
cnot bell75 bell74
cnot bell74 k
T* k
cnot bell66 k
T k
cnot bell74 k
H bell74
measure bell74
cz bell74 0
T* k
cnot bell66 k
H bell66
measure bell66
cz bell66 o
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell70 1
T 1
cnot l 1
T* 1
cnot bell70 1
Z o
cnot n o
T* o
cnot n o
H o
T o
cnot l o
T* o
cnot bell70 o
T o
cnot l o
T* o
cnot bell70 o
H o
T k
cnot bell64 k
T* k
H bell76
cnot bell76 bell77
cnot n bell77
measure bell77
cnot bell77 bell76
cnot bell76 k
T k
cnot bell64 k
H bell64
measure bell64
cz bell64 l
T* k
cnot bell76 k
H bell76
measure bell76
cz bell76 n
H k
cnot o n
T 1
cnot l 1
T* 1
cnot bell70 1
T 1
cnot l 1
T* 1
cnot bell70 1
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
H bell78
cnot bell78 bell79
cnot 0 bell79
measure bell79
cnot bell79 bell78
cnot bell78 i
T* i
H bell80
cnot bell80 bell81
cnot o bell81
measure bell81
cnot bell81 bell80
cnot bell80 i
T i
cnot bell78 i
H bell78
measure bell78
cz bell78 0
T* i
cnot bell80 i
H bell80
measure bell80
cz bell80 o
H i
T 0
cnot o 0
T* 0
cnot o 0
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
cnot l 1
T* 1
cnot bell70 1
T 1
cnot l 1
T* 1
cnot bell70 1
H bell70
measure bell70
cz bell70 m
H 1
Z l
S n
T o
cnot n o
S o
cnot l o
T o
Z o
T* m
H bell82
cnot bell82 bell83
cnot l bell83
measure bell83
cnot bell83 bell82
cnot bell82 m
H bell82
measure bell82
cz bell82 l
T m
cnot k j
cnot o l
cnot n o
H bell84
cnot bell84 bell85
cnot o bell85
measure bell85
cnot bell85 bell84
cnot bell84 m
H bell84
measure bell84
cz bell84 o
swap m n
cnot l n
H bell86
cnot bell86 bell87
cnot k bell87
measure bell87
cnot bell87 bell86
cnot bell86 n
cnot bell86 o
H bell86
measure bell86
cz bell86 k
cnot j m
cnot m i
cnot i m
H bell88
cnot bell88 bell89
cnot i bell89
measure bell89
cnot bell89 bell88
cnot bell88 l
H bell88
measure bell88
cz bell88 i
H bell90
cnot bell90 bell91
cnot l bell91
measure bell91
cnot bell91 bell90
cnot bell90 h
H bell90
measure bell90
cz bell90 l
H bell92
cnot bell92 bell93
cnot h bell93
measure bell93
cnot bell93 bell92
cnot bell92 l
H bell92
measure bell92
cz bell92 h
H bell94
cnot bell94 bell95
cnot j bell95
measure bell95
cnot bell95 bell94
cnot bell94 n
H bell94
measure bell94
cz bell94 j
H bell96
cnot bell96 bell97
cnot h bell97
measure bell97
cnot bell97 bell96
cnot bell96 k
H bell96
measure bell96
cz bell96 h
H bell98
cnot bell98 bell99
cnot k bell99
measure bell99
cnot bell99 bell98
cnot bell98 g
H bell98
measure bell98
cz bell98 k
H bell100
cnot bell100 bell101
cnot g bell101
measure bell101
cnot bell101 bell100
cnot bell100 j
H bell102
cnot bell102 bell103
cnot j bell103
measure bell103
cnot bell103 bell102
cnot bell102 f
H bell102
measure bell102
cz bell102 j
H bell104
cnot bell104 bell105
cnot f bell105
measure bell105
cnot bell105 bell104
cnot bell104 j
cnot bell104 i
H bell104
measure bell104
cz bell104 f
H bell106
cnot bell106 bell107
cnot i bell107
measure bell107
cnot bell107 bell106
cnot bell106 e
H bell106
measure bell106
cz bell106 i
H bell108
cnot bell108 bell109
cnot e bell109
measure bell109
cnot bell109 bell108
cnot bell108 i
H bell108
measure bell108
cz bell108 e
cnot bell100 k
H bell100
measure bell100
cz bell100 g
cnot e h
cnot h d
H bell110
cnot bell110 bell111
cnot d bell111
measure bell111
cnot bell111 bell110
cnot bell110 g
H bell110
measure bell110
cz bell110 d
cnot g c
cnot c g
cnot c f
cnot f b
cnot b f
cnot d h
H bell112
cnot bell112 bell113
cnot b bell113
measure bell113
cnot bell113 bell112
cnot bell112 e
H bell112
measure bell112
cz bell112 b
cnot e a
cnot a e
cnot a d
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
END
