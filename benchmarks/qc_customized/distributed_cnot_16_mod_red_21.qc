# Hyperedge cut (ebits): 17

# Actual ebits used (Synthesis): 39
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_red_21.qc):
#   Qubits: 11
#   H: 30
#   T: 119
#   X: 24
#   cnot: 105
#   Depth: 141
#   T depth: 57
# Result (19.788ms):
#   Qubits: 89
#   H: 108
#   S: 1
#   T: 73
#   cnot: 217
#   cz: 39
#   measure: 78
#   reset: 78
#   Depth: 243
#   T depth: 59


# Result Circuit
.v x0 x1 c1 x2 c2 x3 c3 x4 c4 d4 z bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell8 bell9
.i x0 x1 x2 x3 x4 z
.o x0 x1 c1 x2 c2 x3 c3 x4 c4 d4 z
BEGIN 
H c2
T c2
H bell0
cnot bell0 bell1
cnot x1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c2
T* c2
H bell2
cnot bell2 bell3
cnot x2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c2
T c2
cnot bell0 c2
H bell0
measure bell0
cz bell0 x1
T* c2
cnot bell2 c2
H c2
H c3
T c3
H bell4
cnot bell4 bell5
cnot c2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c3
T c3
H bell6
cnot bell6 bell7
cnot x3 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c3
T c3
cnot bell4 c3
H bell4
measure bell4
cz bell4 c2
T c3
cnot bell6 c3
H bell6
measure bell6
cz bell6 x3
H c3
H d4
T d4
H bell8
cnot bell8 bell9
cnot c3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 d4
T d4
H bell10
cnot bell10 bell11
cnot x4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 d4
T* d4
cnot bell8 d4
H bell8
measure bell8
cz bell8 c3
T* d4
cnot bell10 d4
H bell10
measure bell10
cz bell10 x4
H d4
T* c3
H bell12
cnot bell12 bell13
cnot x4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c3
T c3
cnot bell12 c3
H bell12
measure bell12
cz bell12 x4
H c3
H c4
T c4
H bell14
cnot bell14 bell15
cnot d4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c4
T* c4
H bell16
cnot bell16 bell17
cnot z bell17
measure bell17
cnot bell17 bell16
cnot bell16 c4
T c4
cnot bell14 c4
T* c4
cnot bell16 c4
H c4
H bell18
cnot bell18 bell19
cnot c3 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c2
T* c2
H bell20
cnot bell20 bell21
cnot x3 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c2
T* c2
cnot bell18 c2
H bell18
measure bell18
cz bell18 c3
cnot bell20 c2
H bell20
measure bell20
cz bell20 x3
H c2
H c1
T c1
H bell22
cnot bell22 bell23
cnot x0 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c1
H bell24
cnot bell24 bell25
cnot c4 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c1
T* c1
H bell26
cnot bell26 bell27
cnot x1 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c1
H bell26
measure bell26
cz bell26 x1
cnot bell24 c1
T c1
cnot bell22 c1
H bell22
measure bell22
cz bell22 x0
cnot bell24 c1
H bell24
measure bell24
cz bell24 c4
T* c1
H bell28
cnot bell28 bell29
cnot c4 bell29
measure bell29
cnot bell29 bell28
cnot bell28 x3
H bell28
measure bell28
cz bell28 c4
H bell30
cnot bell30 bell31
cnot c4 bell31
measure bell31
cnot bell31 bell30
cnot bell30 x1
H bell30
measure bell30
cz bell30 c4
H bell32
cnot bell32 bell33
cnot c4 bell33
measure bell33
cnot bell33 bell32
cnot bell32 x0
H bell32
measure bell32
cz bell32 c4
H bell34
cnot bell34 bell35
cnot x1 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c1
H bell34
measure bell34
cz bell34 x1
H c1
H bell36
cnot bell36 bell37
cnot c1 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c2
T c2
cnot bell2 c2
T* c2
cnot bell36 c2
H bell38
cnot bell38 bell39
cnot x1 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c2
H bell40
cnot bell40 bell41
cnot c4 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c2
T* c2
cnot bell2 c2
T c2
cnot bell40 c2
H bell40
measure bell40
cz bell40 c4
cnot bell38 c2
H bell38
measure bell38
cz bell38 x1
H c2
H bell42
cnot bell42 bell43
cnot c2 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c3
T c3
H bell44
cnot bell44 bell45
cnot x3 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c3
T* c3
cnot bell42 c3
T* c3
H bell46
cnot bell46 bell47
cnot c4 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c3
T* c3
cnot bell44 c3
cnot bell46 c3
H bell46
measure bell46
cz bell46 c4
H c3
T x4
H x4
T x4
H bell48
cnot bell48 bell49
cnot c3 bell49
measure bell49
cnot bell49 bell48
cnot bell48 x4
T x4
H bell50
cnot bell50 bell51
cnot c4 bell51
measure bell51
cnot bell51 bell50
cnot bell50 x4
T* x4
cnot bell48 x4
H bell48
measure bell48
cz bell48 c3
T* x4
cnot bell50 x4
H bell50
measure bell50
cz bell50 c4
H x4
T* c3
H bell52
cnot bell52 bell53
cnot c4 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c3
T c3
cnot bell52 c3
H bell52
measure bell52
cz bell52 c4
H c3
T* c3
cnot bell42 c3
T* c3
cnot bell44 c3
T c3
cnot bell42 c3
H bell42
measure bell42
cz bell42 c2
T c3
cnot bell44 c3
H bell44
measure bell44
cz bell44 x3
H c3
H bell54
cnot bell54 bell55
cnot c2 bell55
measure bell55
cnot bell55 bell54
cnot bell54 x3
H bell56
cnot bell56 bell57
cnot c4 bell57
measure bell57
cnot bell57 bell56
cnot bell56 x3
cnot bell54 x3
cnot bell56 x3
H x3
T* x3
cnot bell54 x3
T x3
cnot bell56 x3
T* x3
cnot bell54 x3
H bell54
measure bell54
cz bell54 c2
T x3
cnot bell56 x3
H bell56
measure bell56
cz bell56 c4
H x3
T* c2
H bell58
cnot bell58 bell59
cnot c4 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c2
T c2
cnot bell58 c2
H bell58
measure bell58
cz bell58 c4
H c2
T* c2
cnot bell36 c2
T* c2
cnot bell2 c2
T c2
cnot bell36 c2
H bell36
measure bell36
cz bell36 c1
T c2
cnot bell2 c2
H bell2
measure bell2
cz bell2 x2
H c2
H bell60
cnot bell60 bell61
cnot c1 bell61
measure bell61
cnot bell61 bell60
cnot bell60 x2
H bell62
cnot bell62 bell63
cnot x1 bell63
measure bell63
cnot bell63 bell62
cnot bell62 x2
H bell64
cnot bell64 bell65
cnot c4 bell65
measure bell65
cnot bell65 bell64
cnot bell64 x2
cnot bell60 x2
cnot bell62 x2
H bell62
measure bell62
cz bell62 x1
cnot bell64 x2
H x2
T* x2
cnot bell60 x2
T* x2
cnot bell64 x2
T x2
cnot bell60 x2
H bell60
measure bell60
cz bell60 c1
T x2
cnot bell64 x2
H bell64
measure bell64
cz bell64 c4
H x2
T c1
H bell66
cnot bell66 bell67
cnot c4 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c1
T* c1
cnot bell66 c1
H bell66
measure bell66
cz bell66 c4
H c1
T* c1
H bell68
cnot bell68 bell69
cnot x0 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c1
T c1
H bell70
cnot bell70 bell71
cnot x1 bell71
measure bell71
cnot bell71 bell70
cnot bell70 c1
T* c1
cnot bell68 c1
H bell68
measure bell68
cz bell68 x0
T c1
cnot bell70 c1
H bell70
measure bell70
cz bell70 x1
H c1
H bell72
cnot bell72 bell73
cnot c4 bell73
measure bell73
cnot bell73 bell72
cnot bell72 x1
H bell74
cnot bell74 bell75
cnot x0 bell75
measure bell75
cnot bell75 bell74
cnot bell74 x1
cnot bell72 x1
cnot bell74 x1
H x1
T* x1
cnot bell72 x1
T x1
cnot bell74 x1
T x1
cnot bell72 x1
H bell72
measure bell72
cz bell72 c4
T* x1
cnot bell74 x1
H bell74
measure bell74
cz bell74 x0
H x1
S* c4
H bell76
cnot bell76 bell77
cnot x0 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c4
T* c4
cnot bell76 c4
H bell76
measure bell76
cz bell76 x0
H c4
T* c4
cnot bell14 c4
T c4
cnot bell16 c4
T* c4
cnot bell14 c4
H bell14
measure bell14
cz bell14 d4
T c4
cnot bell16 c4
H bell16
measure bell16
cz bell16 z
H c4
T x0
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
END
