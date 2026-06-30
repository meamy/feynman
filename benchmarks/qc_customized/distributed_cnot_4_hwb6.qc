# Hyperedge cut (ebits): 31

# Actual ebits used (Synthesis): 44
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
# Result (23.669ms):
#   Qubits: 95
#   H: 114
#   S: 4
#   T: 81
#   X: 5
#   Z: 4
#   cnot: 250
#   cz: 48
#   measure: 88
#   reset: 91
#   swap: 1
#   Depth: 285
#   T depth: 68


# Result Circuit
.v a b c d e f 0 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell9
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
cnot a b
T b
cnot f d
H bell6
cnot bell6 bell7
cnot e bell7
measure bell7
cnot bell7 bell6
cnot bell6 f
H bell6
measure bell6
cz bell6 e
cnot a b
H b
T b
cnot a b
T b
H bell8
cnot bell8 bell9
cnot c bell9
measure bell9
cnot bell9 bell8
cnot bell8 b
T* b
cnot a b
T* b
cnot bell8 b
H bell8
measure bell8
cz bell8 c
H b
H f
T f
H bell10
cnot bell10 bell11
cnot a bell11
measure bell11
cnot bell11 bell10
cnot bell10 f
T f
H bell12
cnot bell12 bell13
cnot c bell13
measure bell13
cnot bell13 bell12
cnot bell12 f
T* f
cnot bell10 f
H bell10
measure bell10
cz bell10 a
T* f
cnot bell12 f
H bell14
cnot bell14 bell15
cnot b bell15
measure bell15
cnot bell15 bell14
cnot bell14 d
T f
cnot bell14 f
T f
cnot d f
T* f
cnot bell14 f
T* f
cnot d f
H f
T d
cnot bell14 d
T d
H bell16
cnot bell16 bell17
cnot e bell17
measure bell17
cnot bell17 bell16
cnot f bell16
cnot bell14 bell16
H bell18
cnot bell18 bell19
cnot bell16 bell19
measure bell19
cnot bell19 bell18
reset bell19
cnot e bell18
cnot bell18 e
H bell18
measure bell18
cz bell18 b
cz bell18 f
H bell16
measure bell16
cz bell16 e
cnot bell14 d
H bell14
measure bell14
cz bell14 b
swap a b
H d
T d
H bell20
cnot bell20 bell21
cnot b bell21
measure bell21
cnot bell21 bell20
cnot bell20 d
T d
cnot bell12 d
T* d
cnot bell20 d
H bell20
measure bell20
cz bell20 b
T* d
cnot bell12 d
H bell12
measure bell12
cz bell12 c
H d
T* c
Z c
H bell22
cnot bell22 bell23
cnot b bell23
measure bell23
cnot bell23 bell22
cnot bell22 c
T* c
Z c
cnot bell22 c
H bell22
measure bell22
cz bell22 b
H bell24
cnot bell24 bell25
cnot b bell25
measure bell25
cnot bell25 bell24
cnot bell24 f
H bell24
measure bell24
cz bell24 b
H c
T c
H bell26
cnot bell26 bell27
cnot e bell27
measure bell27
cnot bell27 bell26
cnot bell26 c
T c
H bell28
cnot bell28 bell29
cnot f bell29
measure bell29
cnot bell29 bell28
cnot bell28 c
T* c
cnot bell26 c
T* c
cnot bell28 c
H bell28
measure bell28
cz bell28 f
H c
H 0
T 0
cnot c 0
T* 0
cnot bell26 0
T* 0
cnot c 0
T 0
cnot bell26 0
H 0
Z b
X b
H b
T b
H bell30
cnot bell30 bell31
cnot 0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 b
T* b
H bell32
cnot bell32 bell33
cnot f bell33
measure bell33
cnot bell33 bell32
cnot bell32 b
T b
cnot bell30 b
H bell30
measure bell30
cz bell30 0
T* b
cnot bell32 b
H bell32
measure bell32
cz bell32 f
H b
T 0
H bell34
cnot bell34 bell35
cnot f bell35
measure bell35
cnot bell35 bell34
cnot bell34 0
T* 0
cnot bell34 0
H bell34
measure bell34
cz bell34 f
H 0
T* 0
cnot c 0
T 0
cnot bell26 0
T 0
cnot c 0
T* 0
cnot bell26 0
H 0
cnot bell26 c
H bell26
measure bell26
cz bell26 e
S f
H bell36
cnot bell36 bell37
cnot e bell37
measure bell37
cnot bell37 bell36
cnot bell36 f
T f
T* a
H bell38
cnot bell38 bell39
cnot f bell39
measure bell39
cnot bell39 bell38
cnot bell38 c
H bell38
measure bell38
cz bell38 f
cnot bell36 f
H bell36
measure bell36
cz bell36 e
H bell40
cnot bell40 bell41
cnot f bell41
measure bell41
cnot bell41 bell40
cnot bell40 a
H bell40
measure bell40
cz bell40 f
H bell42
cnot bell42 bell43
cnot a bell43
measure bell43
cnot bell43 bell42
cnot bell42 d
H bell42
measure bell42
cz bell42 a
H f
T f
H bell44
cnot bell44 bell45
cnot b bell45
measure bell45
cnot bell45 bell44
cnot bell44 f
T* f
H bell46
cnot bell46 bell47
cnot c bell47
measure bell47
cnot bell47 bell46
cnot bell46 f
T f
cnot bell44 f
H bell44
measure bell44
cz bell44 b
T* f
cnot bell46 f
H bell48
cnot bell48 bell49
cnot d bell49
measure bell49
cnot bell49 bell48
cnot bell48 b
H bell48
measure bell48
cz bell48 d
H bell50
cnot bell50 bell51
cnot d bell51
measure bell51
cnot bell51 bell50
cnot bell50 e
H bell50
measure bell50
cz bell50 d
H bell52
cnot bell52 bell53
cnot e bell53
measure bell53
cnot bell53 bell52
cnot bell52 a
H bell52
measure bell52
cz bell52 e
T f
cnot bell46 f
T* f
H bell54
cnot bell54 bell55
cnot e bell55
measure bell55
cnot bell55 bell54
cnot bell54 f
T f
cnot bell46 f
T* f
cnot bell54 f
H f
H bell56
cnot bell56 bell57
cnot b bell57
measure bell57
cnot bell57 bell56
cnot bell56 d
T d
cnot bell46 d
T* d
cnot bell54 d
cnot bell46 d
H bell46
measure bell46
cz bell46 c
cnot bell56 d
T* d
H bell58
cnot bell58 bell59
cnot f bell59
measure bell59
cnot bell59 bell58
cnot bell58 c
H bell58
measure bell58
cz bell58 f
cnot bell54 d
cnot bell54 f
X d
H d
T d
cnot bell56 d
T d
cnot bell54 d
T* d
cnot bell56 d
H bell56
measure bell56
cz bell56 b
T* d
cnot bell54 d
H d
H bell60
cnot bell60 bell61
cnot c bell61
measure bell61
cnot bell61 bell60
cnot bell60 f
T* f
cnot bell54 f
S f
cnot bell54 f
H bell54
measure bell54
cz bell54 e
cnot bell60 f
H bell60
measure bell60
cz bell60 c
H f
T f
H bell62
cnot bell62 bell63
cnot a bell63
measure bell63
cnot bell63 bell62
cnot bell62 f
T f
cnot d f
T* f
cnot bell62 f
H bell62
measure bell62
cz bell62 a
T* f
cnot d f
H f
T* a
H bell64
cnot bell64 bell65
cnot d bell65
measure bell65
cnot bell65 bell64
cnot bell64 a
T a
cnot bell64 a
H bell64
measure bell64
cz bell64 d
H bell66
cnot bell66 bell67
cnot a bell67
measure bell67
cnot bell67 bell66
cnot bell66 c
H bell66
measure bell66
cz bell66 a
H a
T a
cnot b a
T a
H bell68
cnot bell68 bell69
cnot e bell69
measure bell69
cnot bell69 bell68
cnot bell68 a
T* a
cnot b a
T* a
cnot bell68 a
H a
S* b
cnot bell68 b
S b
H bell70
cnot bell70 bell71
cnot d bell71
measure bell71
cnot bell71 bell70
cnot bell70 c
H bell70
measure bell70
cz bell70 d
cnot bell68 b
H bell68
measure bell68
cz bell68 e
X b
H b
T b
cnot a b
T* b
H bell72
cnot bell72 bell73
cnot c bell73
measure bell73
cnot bell73 bell72
cnot bell72 b
T b
cnot a b
T* b
cnot bell72 b
H bell72
measure bell72
cz bell72 c
H b
T a
T c
H bell74
cnot bell74 bell75
cnot a bell75
measure bell75
cnot bell75 bell74
cnot bell74 c
H bell74
measure bell74
cz bell74 a
T* c
T d
T* e
Z e
cnot b a
cnot f d
H bell76
cnot bell76 bell77
cnot e bell77
measure bell77
cnot bell77 bell76
cnot f bell76
cnot d bell76
H bell78
cnot bell78 bell79
cnot bell76 bell79
measure bell79
cnot bell79 bell78
reset bell79
cnot e bell78
cnot bell78 e
H bell78
measure bell78
cz bell78 d
cz bell78 f
H bell76
measure bell76
cz bell76 e
H bell80
cnot bell80 bell81
cnot c bell81
measure bell81
cnot bell81 bell80
H bell82
cnot bell82 bell83
cnot e bell83
measure bell83
cnot bell83 bell82
cnot bell80 bell82
H bell80
measure bell80
cz bell80 c
cnot b bell82
cnot a bell82
H bell84
cnot bell84 bell85
cnot bell82 bell85
measure bell85
cnot bell85 bell84
reset bell85
cnot e bell84
cnot bell84 e
H bell84
measure bell84
cz bell84 a
cz bell84 b
cz bell84 c
H bell82
measure bell82
cz bell82 e
H bell86
cnot bell86 bell87
cnot a bell87
measure bell87
cnot bell87 bell86
cnot bell86 c
H bell86
measure bell86
cz bell86 a
cnot a b
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
END
