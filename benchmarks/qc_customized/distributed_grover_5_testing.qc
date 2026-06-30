# Hyperedge cut (ebits): 48

# Actual ebits used (Synthesis): 48
# Distribution Verification: PASS
# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/grover_5.qc):
#   Qubits: 9
#   H: 142
#   T: 336
#   X: 65
#   cnot: 288
#   Depth: 389
#   T depth: 152
# Result (41.297ms):
#   Qubits: 105
#   H: 196
#   T: 216
#   X: 9
#   cnot: 352
#   cz: 48
#   measure: 96
#   reset: 96
#   Depth: 550
#   T depth: 168


# Result Circuit
.v a b c d e result 0 1 2 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95
.i 
.o a b c d e result 0 1 2
BEGIN 
H a
H b
H c
H d
H e
X result
H 0
T 0
cnot a 0
T 0
H bell0
cnot bell0 bell1
cnot b bell1
measure bell1
cnot bell1 bell0
cnot bell0 0
T 0
cnot a 0
T 0
cnot bell0 0
H 0
H 1
T 1
H bell2
cnot bell2 bell3
cnot 0 bell3
measure bell3
cnot bell3 bell2
cnot bell2 1
T* 1
H bell4
cnot bell4 bell5
cnot c bell5
measure bell5
cnot bell5 bell4
cnot bell4 1
T 1
cnot bell2 1
T* 1
cnot bell4 1
H 1
H 2
T 2
H bell6
cnot bell6 bell7
cnot 1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 2
T* 2
H bell8
cnot bell8 bell9
cnot d bell9
measure bell9
cnot bell9 bell8
cnot bell8 2
T 2
cnot bell6 2
T* 2
cnot bell8 2
H 2
T result
H bell10
cnot bell10 bell11
cnot 2 bell11
measure bell11
cnot bell11 bell10
cnot bell10 result
T* result
H bell12
cnot bell12 bell13
cnot e bell13
measure bell13
cnot bell13 bell12
cnot bell12 result
T* result
cnot bell10 result
H bell10
measure bell10
cz bell10 2
T result
cnot bell12 result
T 2
cnot bell12 2
T 2
cnot bell12 2
H bell12
measure bell12
cz bell12 e
H 2
T* 2
cnot bell6 2
T 2
cnot bell8 2
T* 2
cnot bell6 2
H bell6
measure bell6
cz bell6 1
T 2
cnot bell8 2
H bell8
measure bell8
cz bell8 d
H 1
T* 1
cnot bell2 1
T 1
cnot bell4 1
T* 1
cnot bell2 1
H bell2
measure bell2
cz bell2 0
T 1
cnot bell4 1
H bell4
measure bell4
cz bell4 c
H 0
T* 0
cnot a 0
T* 0
cnot bell0 0
T* 0
cnot a 0
T* 0
cnot bell0 0
H bell0
measure bell0
cz bell0 b
H a
H b
H c
H d
T* e
H e
T 0
cnot a 0
T 0
H bell14
cnot bell14 bell15
cnot b bell15
measure bell15
cnot bell15 bell14
cnot bell14 0
T 0
cnot a 0
T 0
cnot bell14 0
H 0
T 1
H bell16
cnot bell16 bell17
cnot 0 bell17
measure bell17
cnot bell17 bell16
cnot bell16 1
T* 1
H bell18
cnot bell18 bell19
cnot c bell19
measure bell19
cnot bell19 bell18
cnot bell18 1
T* 1
cnot bell16 1
T 1
cnot bell18 1
H 1
X e
H e
T e
H bell20
cnot bell20 bell21
cnot 1 bell21
measure bell21
cnot bell21 bell20
cnot bell20 e
T* e
H bell22
cnot bell22 bell23
cnot d bell23
measure bell23
cnot bell23 bell22
cnot bell22 e
T* e
cnot bell20 e
H bell20
measure bell20
cz bell20 1
T e
cnot bell22 e
H e
T 1
cnot bell22 1
T 1
cnot bell22 1
H bell22
measure bell22
cz bell22 d
H 1
T* 1
cnot bell16 1
T 1
cnot bell18 1
T 1
cnot bell16 1
H bell16
measure bell16
cz bell16 0
T* 1
cnot bell18 1
H bell18
measure bell18
cz bell18 c
H 0
T* 0
cnot a 0
T* 0
cnot bell14 0
T* 0
cnot a 0
T* 0
cnot bell14 0
H bell14
measure bell14
cz bell14 b
H a
H b
H c
T* d
H d
X e
H e
T 0
cnot a 0
T 0
H bell24
cnot bell24 bell25
cnot b bell25
measure bell25
cnot bell25 bell24
cnot bell24 0
T 0
cnot a 0
T 0
cnot bell24 0
H 0
T 1
H bell26
cnot bell26 bell27
cnot 0 bell27
measure bell27
cnot bell27 bell26
cnot bell26 1
T* 1
H bell28
cnot bell28 bell29
cnot c bell29
measure bell29
cnot bell29 bell28
cnot bell28 1
T 1
cnot bell26 1
T* 1
cnot bell28 1
H 1
T 2
H bell30
cnot bell30 bell31
cnot 1 bell31
measure bell31
cnot bell31 bell30
cnot bell30 2
T* 2
H bell32
cnot bell32 bell33
cnot d bell33
measure bell33
cnot bell33 bell32
cnot bell32 2
T 2
cnot bell30 2
T* 2
cnot bell32 2
H 2
T result
H bell34
cnot bell34 bell35
cnot 2 bell35
measure bell35
cnot bell35 bell34
cnot bell34 result
T* result
H bell36
cnot bell36 bell37
cnot e bell37
measure bell37
cnot bell37 bell36
cnot bell36 result
T* result
cnot bell34 result
H bell34
measure bell34
cz bell34 2
T result
cnot bell36 result
T 2
cnot bell36 2
T 2
cnot bell36 2
H bell36
measure bell36
cz bell36 e
H 2
T* 2
cnot bell30 2
T 2
cnot bell32 2
T* 2
cnot bell30 2
H bell30
measure bell30
cz bell30 1
T 2
cnot bell32 2
H bell32
measure bell32
cz bell32 d
H 1
T* 1
cnot bell26 1
T 1
cnot bell28 1
T* 1
cnot bell26 1
H bell26
measure bell26
cz bell26 0
T 1
cnot bell28 1
H bell28
measure bell28
cz bell28 c
H 0
T* 0
cnot a 0
T* 0
cnot bell24 0
T* 0
cnot a 0
T* 0
cnot bell24 0
H bell24
measure bell24
cz bell24 b
H a
H b
H c
H d
T* e
H e
T 0
cnot a 0
T 0
H bell38
cnot bell38 bell39
cnot b bell39
measure bell39
cnot bell39 bell38
cnot bell38 0
T 0
cnot a 0
T 0
cnot bell38 0
H 0
T 1
H bell40
cnot bell40 bell41
cnot 0 bell41
measure bell41
cnot bell41 bell40
cnot bell40 1
T* 1
H bell42
cnot bell42 bell43
cnot c bell43
measure bell43
cnot bell43 bell42
cnot bell42 1
T* 1
cnot bell40 1
T 1
cnot bell42 1
H 1
X e
H e
T e
H bell44
cnot bell44 bell45
cnot 1 bell45
measure bell45
cnot bell45 bell44
cnot bell44 e
T* e
H bell46
cnot bell46 bell47
cnot d bell47
measure bell47
cnot bell47 bell46
cnot bell46 e
T* e
cnot bell44 e
H bell44
measure bell44
cz bell44 1
T e
cnot bell46 e
H e
T 1
cnot bell46 1
T 1
cnot bell46 1
H bell46
measure bell46
cz bell46 d
H 1
T* 1
cnot bell40 1
T 1
cnot bell42 1
T 1
cnot bell40 1
H bell40
measure bell40
cz bell40 0
T* 1
cnot bell42 1
H bell42
measure bell42
cz bell42 c
H 0
T* 0
cnot a 0
T* 0
cnot bell38 0
T* 0
cnot a 0
T* 0
cnot bell38 0
H bell38
measure bell38
cz bell38 b
H a
H b
H c
T* d
H d
X e
H e
T 0
cnot a 0
T 0
H bell48
cnot bell48 bell49
cnot b bell49
measure bell49
cnot bell49 bell48
cnot bell48 0
T 0
cnot a 0
T 0
cnot bell48 0
H 0
T 1
H bell50
cnot bell50 bell51
cnot 0 bell51
measure bell51
cnot bell51 bell50
cnot bell50 1
T* 1
H bell52
cnot bell52 bell53
cnot c bell53
measure bell53
cnot bell53 bell52
cnot bell52 1
T 1
cnot bell50 1
T* 1
cnot bell52 1
H 1
T 2
H bell54
cnot bell54 bell55
cnot 1 bell55
measure bell55
cnot bell55 bell54
cnot bell54 2
T* 2
H bell56
cnot bell56 bell57
cnot d bell57
measure bell57
cnot bell57 bell56
cnot bell56 2
T 2
cnot bell54 2
T* 2
cnot bell56 2
H 2
T result
H bell58
cnot bell58 bell59
cnot 2 bell59
measure bell59
cnot bell59 bell58
cnot bell58 result
T* result
H bell60
cnot bell60 bell61
cnot e bell61
measure bell61
cnot bell61 bell60
cnot bell60 result
T* result
cnot bell58 result
H bell58
measure bell58
cz bell58 2
T result
cnot bell60 result
T 2
cnot bell60 2
T 2
cnot bell60 2
H bell60
measure bell60
cz bell60 e
H 2
T* 2
cnot bell54 2
T 2
cnot bell56 2
T* 2
cnot bell54 2
H bell54
measure bell54
cz bell54 1
T 2
cnot bell56 2
H bell56
measure bell56
cz bell56 d
H 1
T* 1
cnot bell50 1
T 1
cnot bell52 1
T* 1
cnot bell50 1
H bell50
measure bell50
cz bell50 0
T 1
cnot bell52 1
H bell52
measure bell52
cz bell52 c
H 0
T* 0
cnot a 0
T* 0
cnot bell48 0
T* 0
cnot a 0
T* 0
cnot bell48 0
H bell48
measure bell48
cz bell48 b
H a
H b
H c
H d
T* e
H e
T 0
cnot a 0
T 0
H bell62
cnot bell62 bell63
cnot b bell63
measure bell63
cnot bell63 bell62
cnot bell62 0
T 0
cnot a 0
T 0
cnot bell62 0
H 0
T 1
H bell64
cnot bell64 bell65
cnot 0 bell65
measure bell65
cnot bell65 bell64
cnot bell64 1
T* 1
H bell66
cnot bell66 bell67
cnot c bell67
measure bell67
cnot bell67 bell66
cnot bell66 1
T* 1
cnot bell64 1
T 1
cnot bell66 1
H 1
X e
H e
T e
H bell68
cnot bell68 bell69
cnot 1 bell69
measure bell69
cnot bell69 bell68
cnot bell68 e
T* e
H bell70
cnot bell70 bell71
cnot d bell71
measure bell71
cnot bell71 bell70
cnot bell70 e
T* e
cnot bell68 e
H bell68
measure bell68
cz bell68 1
T e
cnot bell70 e
H e
T 1
cnot bell70 1
T 1
cnot bell70 1
H bell70
measure bell70
cz bell70 d
H 1
T* 1
cnot bell64 1
T 1
cnot bell66 1
T 1
cnot bell64 1
H bell64
measure bell64
cz bell64 0
T* 1
cnot bell66 1
H bell66
measure bell66
cz bell66 c
H 0
T* 0
cnot a 0
T* 0
cnot bell62 0
T* 0
cnot a 0
T* 0
cnot bell62 0
H bell62
measure bell62
cz bell62 b
H a
H b
H c
T* d
H d
X e
H e
T 0
cnot a 0
T 0
H bell72
cnot bell72 bell73
cnot b bell73
measure bell73
cnot bell73 bell72
cnot bell72 0
T 0
cnot a 0
T 0
cnot bell72 0
H 0
T 1
H bell74
cnot bell74 bell75
cnot 0 bell75
measure bell75
cnot bell75 bell74
cnot bell74 1
T* 1
H bell76
cnot bell76 bell77
cnot c bell77
measure bell77
cnot bell77 bell76
cnot bell76 1
T 1
cnot bell74 1
T* 1
cnot bell76 1
H 1
T 2
H bell78
cnot bell78 bell79
cnot 1 bell79
measure bell79
cnot bell79 bell78
cnot bell78 2
T* 2
H bell80
cnot bell80 bell81
cnot d bell81
measure bell81
cnot bell81 bell80
cnot bell80 2
T 2
cnot bell78 2
T* 2
cnot bell80 2
H 2
T result
H bell82
cnot bell82 bell83
cnot 2 bell83
measure bell83
cnot bell83 bell82
cnot bell82 result
T* result
H bell84
cnot bell84 bell85
cnot e bell85
measure bell85
cnot bell85 bell84
cnot bell84 result
T* result
cnot bell82 result
H bell82
measure bell82
cz bell82 2
T result
cnot bell84 result
H result
T 2
cnot bell84 2
T 2
cnot bell84 2
H bell84
measure bell84
cz bell84 e
H 2
T* 2
cnot bell78 2
T 2
cnot bell80 2
T* 2
cnot bell78 2
H bell78
measure bell78
cz bell78 1
T 2
cnot bell80 2
H bell80
measure bell80
cz bell80 d
H 2
H 1
T* 1
cnot bell74 1
T 1
cnot bell76 1
T* 1
cnot bell74 1
H bell74
measure bell74
cz bell74 0
T 1
cnot bell76 1
H bell76
measure bell76
cz bell76 c
H 0
T* 0
cnot a 0
T* 0
cnot bell72 0
T* 0
cnot a 0
T* 0
cnot bell72 0
H bell72
measure bell72
cz bell72 b
H a
H b
H c
H d
T* e
H e
T 0
cnot a 0
T 0
H bell86
cnot bell86 bell87
cnot b bell87
measure bell87
cnot bell87 bell86
cnot bell86 0
T 0
cnot a 0
T 0
cnot bell86 0
H 0
T 1
H bell88
cnot bell88 bell89
cnot 0 bell89
measure bell89
cnot bell89 bell88
cnot bell88 1
T* 1
H bell90
cnot bell90 bell91
cnot c bell91
measure bell91
cnot bell91 bell90
cnot bell90 1
T* 1
cnot bell88 1
T 1
cnot bell90 1
H 1
X e
H e
T e
H bell92
cnot bell92 bell93
cnot 1 bell93
measure bell93
cnot bell93 bell92
cnot bell92 e
T* e
H bell94
cnot bell94 bell95
cnot d bell95
measure bell95
cnot bell95 bell94
cnot bell94 e
T* e
cnot bell92 e
H bell92
measure bell92
cz bell92 1
T e
cnot bell94 e
H e
T 1
cnot bell94 1
T 1
cnot bell94 1
H bell94
measure bell94
cz bell94 d
H 1
T* 1
cnot bell88 1
T 1
cnot bell90 1
T 1
cnot bell88 1
H bell88
measure bell88
cz bell88 0
T* 1
cnot bell90 1
H bell90
measure bell90
cz bell90 c
H 1
H 0
T* 0
cnot a 0
T* 0
cnot bell86 0
T* 0
cnot a 0
T* 0
cnot bell86 0
H bell86
measure bell86
cz bell86 b
H 0
H a
H b
H c
T* d
H d
X e
H e
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
END
