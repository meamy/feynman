# Hyperedge cut (ebits): 41

# Actual ebits used (Synthesis): 54
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/ham15-low.qc):
#   Qubits: 17
#   H: 46
#   T: 161
#   cnot: 236
#   Depth: 238
#   T depth: 85
# Result (50.219ms):
#   Qubits: 125
#   H: 146
#   S: 3
#   T: 113
#   cnot: 383
#   cz: 55
#   measure: 108
#   reset: 109
#   swap: 1
#   Depth: 397
#   T depth: 93


# Result Circuit
.v a b c d e f g h i j k l m n o 0 1 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a b c d e f g h i j k l m n o
.o a b c d e f g h i j k l m n o
BEGIN 
H bell0
cnot bell0 bell1
cnot k bell1
measure bell1
cnot bell1 bell0
cnot bell0 a
H bell0
measure bell0
cz bell0 k
H bell2
cnot bell2 bell3
cnot k bell3
measure bell3
cnot bell3 bell2
cnot bell2 f
H bell2
measure bell2
cz bell2 k
cnot k g
H bell4
cnot bell4 bell5
cnot k bell5
measure bell5
cnot bell5 bell4
cnot bell4 h
H bell4
measure bell4
cz bell4 k
H bell6
cnot bell6 bell7
cnot m bell7
measure bell7
cnot bell7 bell6
cnot bell6 i
cnot m n
cnot n l
cnot l n
cnot i h
cnot i e
H i
T i
H bell8
cnot bell8 bell9
cnot l bell9
measure bell9
cnot bell9 bell8
cnot bell8 i
T* i
cnot bell6 i
T i
cnot bell8 i
H bell8
measure bell8
cz bell8 l
T* i
cnot bell6 i
H bell6
measure bell6
cz bell6 m
H i
T m
cnot l m
T* m
H bell10
cnot bell10 bell11
cnot o bell11
measure bell11
cnot bell11 bell10
cnot bell10 a
H bell10
measure bell10
cz bell10 o
cnot i e
H bell12
cnot bell12 bell13
cnot o bell13
measure bell13
cnot bell13 bell12
cnot bell12 g
H bell12
measure bell12
cz bell12 o
cnot i h
H bell14
cnot bell14 bell15
cnot o bell15
measure bell15
cnot bell15 bell14
cnot bell14 i
H bell14
measure bell14
cz bell14 o
cnot o n
cnot l m
H bell16
cnot bell16 bell17
cnot m bell17
measure bell17
cnot bell17 bell16
cnot bell16 d
H bell16
measure bell16
cz bell16 m
H m
T m
cnot n m
T* m
cnot o m
T m
cnot n m
T* m
cnot o m
H m
T o
cnot n o
T* o
H bell18
cnot bell18 bell19
cnot m bell19
measure bell19
cnot bell19 bell18
cnot bell18 d
H bell18
measure bell18
cz bell18 m
cnot n o
cnot m n
H o
T o
cnot m o
T* o
cnot n o
T o
cnot m o
T* o
cnot n o
H o
T m
H bell20
cnot bell20 bell21
cnot m bell21
measure bell21
cnot bell21 bell20
cnot bell20 k
H bell20
measure bell20
cz bell20 m
swap 0 1
H m
T m
cnot n m
T* m
cnot o m
T m
cnot n m
T* m
cnot o m
H m
H bell22
cnot bell22 bell23
cnot k bell23
measure bell23
cnot bell23 bell22
cnot bell22 e
cnot bell22 i
cnot bell22 j
H bell22
measure bell22
cz bell22 k
H bell24
cnot bell24 bell25
cnot m bell25
measure bell25
cnot bell25 bell24
cnot bell24 k
H bell24
measure bell24
cz bell24 m
cnot k d
cnot k c
H bell26
cnot bell26 bell27
cnot k bell27
measure bell27
cnot bell27 bell26
cnot bell26 b
H bell26
measure bell26
cz bell26 k
H 1
T 1
H bell28
cnot bell28 bell29
cnot l bell29
measure bell29
cnot bell29 bell28
cnot bell28 1
T* 1
H bell30
cnot bell30 bell31
cnot m bell31
measure bell31
cnot bell31 bell30
cnot bell30 1
T 1
cnot bell28 1
T* 1
cnot bell30 1
H 1
H 0
T 0
H bell32
cnot bell32 bell33
cnot 1 bell33
measure bell33
cnot bell33 bell32
cnot bell32 0
T* 0
cnot n 0
T 0
cnot bell32 0
T* 0
cnot n 0
H 0
H k
T k
H bell34
cnot bell34 bell35
cnot 0 bell35
measure bell35
cnot bell35 bell34
cnot bell34 k
T* k
H bell36
cnot bell36 bell37
cnot o bell37
measure bell37
cnot bell37 bell36
cnot bell36 k
T k
cnot bell34 k
H bell34
measure bell34
cz bell34 0
T* k
cnot bell36 k
H k
T 0
cnot o 0
T* 0
cnot o 0
H 0
T* 0
cnot bell32 0
T 0
cnot n 0
T* 0
cnot bell32 0
H bell32
measure bell32
cz bell32 1
T 0
cnot n 0
H 1
T* 1
cnot bell28 1
T 1
cnot bell30 1
T* 1
cnot bell28 1
H bell28
measure bell28
cz bell28 l
T 1
cnot bell30 1
H bell30
measure bell30
cz bell30 m
H 1
H bell38
cnot bell38 bell39
cnot k bell39
measure bell39
cnot bell39 bell38
cnot bell38 b
H bell38
measure bell38
cz bell38 k
cnot k c
cnot k d
H bell40
cnot bell40 bell41
cnot k bell41
measure bell41
cnot bell41 bell40
cnot bell40 e
cnot k g
cnot bell40 j
H bell40
measure bell40
cz bell40 k
H bell42
cnot bell42 bell43
cnot l bell43
measure bell43
cnot bell43 bell42
cnot bell42 k
H bell42
measure bell42
cz bell42 l
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
H 0
T l
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
T* 0
cnot m 0
T 0
cnot n 0
T* 0
cnot m 0
T 0
cnot n 0
H bell44
cnot bell44 bell45
cnot k bell45
measure bell45
cnot bell45 bell44
cnot bell44 f
H bell44
measure bell44
cz bell44 k
H bell46
cnot bell46 bell47
cnot m bell47
measure bell47
cnot bell47 bell46
cnot bell46 h
H bell46
measure bell46
cz bell46 m
H bell48
cnot bell48 bell49
cnot n bell49
measure bell49
cnot bell49 bell48
cnot bell48 k
H bell50
cnot bell50 bell51
cnot l bell51
measure bell51
cnot bell51 bell50
cnot bell50 k
H bell50
measure bell50
cz bell50 l
cnot l m
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
H 0
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
T* 0
cnot m 0
T 0
cnot n 0
T* 0
cnot m 0
T 0
cnot n 0
cnot bell48 c
cnot bell48 d
H bell48
measure bell48
cz bell48 n
H bell52
cnot bell52 bell53
cnot l bell53
measure bell53
cnot bell53 bell52
cnot bell52 f
H bell52
measure bell52
cz bell52 l
H bell54
cnot bell54 bell55
cnot n bell55
measure bell55
cnot bell55 bell54
cnot bell54 e
H bell54
measure bell54
cz bell54 n
cnot l m
H bell56
cnot bell56 bell57
cnot m bell57
measure bell57
cnot bell57 bell56
cnot bell56 j
H bell56
measure bell56
cz bell56 m
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot l 0
T* 0
cnot m 0
H 0
S n
cnot m n
cnot l n
cnot o n
cnot m n
cnot l n
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
T* 0
cnot l 0
T 0
cnot m 0
T* 0
cnot l 0
T 0
cnot m 0
H bell58
cnot bell58 bell59
cnot n bell59
measure bell59
cnot bell59 bell58
cnot bell58 c
cnot bell58 d
cnot bell58 k
H bell58
measure bell58
cz bell58 n
H bell60
cnot bell60 bell61
cnot k bell61
measure bell61
cnot bell61 bell60
cnot bell60 i
H bell62
cnot bell62 bell63
cnot m bell63
measure bell63
cnot bell63 bell62
cnot bell62 c
H bell62
measure bell62
cz bell62 m
cnot bell60 a
H bell60
measure bell60
cz bell60 k
H bell64
cnot bell64 bell65
cnot m bell65
measure bell65
cnot bell65 bell64
cnot bell64 a
H bell64
measure bell64
cz bell64 m
H m
T m
cnot l m
T* m
cnot o m
T m
cnot l m
T* m
cnot o m
H m
H bell66
cnot bell66 bell67
cnot m bell67
measure bell67
cnot bell67 bell66
cnot bell66 c
cnot bell36 g
H bell68
cnot bell68 bell69
cnot h bell69
measure bell69
cnot bell69 bell68
cnot bell66 bell68
H bell66
measure bell66
cz bell66 m
cnot bell36 k
H bell36
measure bell36
cz bell36 o
cnot o n
cnot k bell68
H bell70
cnot bell70 bell71
cnot bell68 bell71
measure bell71
cnot bell71 bell70
reset bell71
cnot h bell70
cnot bell70 h
H bell70
measure bell70
cz bell70 k
cz bell70 m
H bell68
measure bell68
cz bell68 h
H bell72
cnot bell72 bell73
cnot n bell73
measure bell73
cnot bell73 bell72
cnot bell72 e
H bell72
measure bell72
cz bell72 n
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot l 0
T* 0
cnot m 0
H 0
S* o
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
T* 0
cnot l 0
T 0
cnot m 0
T* 0
cnot l 0
T 0
cnot m 0
H 0
T l
H bell74
cnot bell74 bell75
cnot o bell75
measure bell75
cnot bell75 bell74
cnot bell74 g
cnot bell74 k
H bell74
measure bell74
cz bell74 o
cnot o l
cnot o m
H bell76
cnot bell76 bell77
cnot m bell77
measure bell77
cnot bell77 bell76
cnot bell76 e
cnot bell76 a
H bell76
measure bell76
cz bell76 m
H o
T o
cnot l o
T* o
cnot n o
T o
cnot l o
T* o
cnot n o
H o
T l
S n
cnot l n
T* n
cnot l m
cnot k g
H bell78
cnot bell78 bell79
cnot k bell79
measure bell79
cnot bell79 bell78
cnot bell78 j
H bell78
measure bell78
cz bell78 k
cnot o l
cnot o m
cnot l n
cnot l m
H bell80
cnot bell80 bell81
cnot n bell81
measure bell81
cnot bell81 bell80
cnot bell80 k
H bell80
measure bell80
cz bell80 n
H bell82
cnot bell82 bell83
cnot k bell83
measure bell83
cnot bell83 bell82
cnot bell82 n
H bell82
measure bell82
cz bell82 k
cnot n o
H bell84
cnot bell84 bell85
cnot j bell85
measure bell85
cnot bell85 bell84
cnot bell84 m
cnot j i
H bell86
cnot bell86 bell87
cnot i bell87
measure bell87
cnot bell87 bell86
cnot bell86 m
cnot bell86 l
H bell86
measure bell86
cz bell86 i
cnot i h
H bell88
cnot bell88 bell89
cnot h bell89
measure bell89
cnot bell89 bell88
cnot bell88 l
H bell88
measure bell88
cz bell88 h
cnot bell84 n
H bell84
measure bell84
cz bell84 j
H bell90
cnot bell90 bell91
cnot h bell91
measure bell91
cnot bell91 bell90
cnot bell90 k
cnot bell90 g
H bell90
measure bell90
cz bell90 h
H bell92
cnot bell92 bell93
cnot g bell93
measure bell93
cnot bell93 bell92
cnot bell92 j
H bell92
measure bell92
cz bell92 g
H bell94
cnot bell94 bell95
cnot j bell95
measure bell95
cnot bell95 bell94
cnot bell94 f
H bell94
measure bell94
cz bell94 j
H bell96
cnot bell96 bell97
cnot f bell97
measure bell97
cnot bell97 bell96
cnot bell96 j
cnot bell96 i
H bell96
measure bell96
cz bell96 f
cnot i e
cnot e i
cnot g k
cnot e h
H bell98
cnot bell98 bell99
cnot h bell99
measure bell99
cnot bell99 bell98
cnot bell98 d
H bell98
measure bell98
cz bell98 h
cnot d g
cnot g c
cnot c g
H bell100
cnot bell100 bell101
cnot c bell101
measure bell101
cnot bell101 bell100
cnot bell100 f
H bell100
measure bell100
cz bell100 c
cnot f b
cnot b f
H bell102
cnot bell102 bell103
cnot d bell103
measure bell103
cnot bell103 bell102
cnot bell102 h
H bell102
measure bell102
cz bell102 d
H bell104
cnot bell104 bell105
cnot b bell105
measure bell105
cnot bell105 bell104
cnot bell104 e
H bell104
measure bell104
cz bell104 b
cnot e a
cnot a e
H bell106
cnot bell106 bell107
cnot a bell107
measure bell107
cnot bell107 bell106
cnot bell106 d
H bell106
measure bell106
cz bell106 a
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
END
