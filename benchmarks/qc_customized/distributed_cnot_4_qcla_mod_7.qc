# Hyperedge cut (ebits): 33

# Actual ebits used (Synthesis): 38
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/qcla_mod_7.qc):
#   Qubits: 26
#   H: 82
#   T: 413
#   X: 7
#   cnot: 382
#   Depth: 172
#   T depth: 77
# Result (128.311ms):
#   Qubits: 102
#   H: 158
#   S: 24
#   T: 237
#   X: 7
#   cnot: 492
#   cz: 38
#   measure: 76
#   reset: 76
#   Depth: 218
#   T depth: 65


# Result Circuit
.v e a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell8 bell9
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6
.o e a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6
BEGIN 
H e
H c0
H d0
H c1
H d1
H c2
H d2
H c3
H c4
H d4
H c5
H d5
T c0
cnot b0 c0
H bell0
cnot bell0 bell1
cnot a0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
cnot b1 c0
cnot a1 c0
T c0
cnot b0 c0
cnot bell0 c0
T* c0
cnot b1 c0
cnot a6 b6
cnot a5 b5
cnot a4 b4
H bell2
cnot bell2 bell3
cnot a3 bell3
measure bell3
cnot bell3 bell2
cnot bell2 b3
cnot a1 c0
cnot a2 b2
cnot a1 b1
cnot bell0 b0
H c0
T d0
cnot bell0 d0
T* d0
cnot b0 d0
T* d0
cnot bell0 d0
T d0
cnot b0 d0
H d0
T c2
cnot b2 c2
T* c2
cnot b3 c2
T c2
cnot b2 c2
T* c2
cnot b3 c2
H c2
T d2
cnot a2 d2
T* d2
cnot b2 d2
T* d2
cnot a2 d2
T d2
cnot b2 d2
H d2
T c4
cnot b4 c4
T* c4
cnot b5 c4
T c4
cnot b4 c4
T* c4
cnot b5 c4
H c4
T d4
cnot a4 d4
T* d4
cnot b4 d4
T* d4
cnot a4 d4
T d4
cnot b4 d4
H d4
T c1
cnot c0 c1
T* c1
H bell4
cnot bell4 bell5
cnot c2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c1
T c1
cnot c0 c1
T* c1
cnot bell4 c1
H bell4
measure bell4
cz bell4 c2
H c1
S d1
cnot a1 d1
T* d1
cnot b1 d1
T* d1
cnot a1 d1
cnot d0 d1
T d1
cnot b1 d1
T* d1
cnot d0 d1
H d1
T c5
cnot b6 c5
T* c5
H bell6
cnot bell6 bell7
cnot c4 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c5
T c5
cnot b6 c5
T* c5
cnot bell6 c5
H bell6
measure bell6
cz bell6 c4
H c5
S d5
cnot a5 d5
T* d5
cnot b5 d5
T* d5
cnot a5 d5
cnot d4 d5
T d5
cnot b5 d5
T* d5
cnot d4 d5
H d5
T c3
cnot a3 c3
T* c3
H bell8
cnot bell8 bell9
cnot b3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c3
T* c3
cnot a3 c3
H bell10
cnot bell10 bell11
cnot c2 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c3
cnot bell8 c3
T c3
H bell12
cnot bell12 bell13
cnot d1 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c3
T* c3
cnot bell10 c3
H bell10
measure bell10
cz bell10 c2
T c3
H bell14
cnot bell14 bell15
cnot d2 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c3
cnot bell12 c3
H bell12
measure bell12
cz bell12 d1
T* c3
cnot bell8 c3
T c3
cnot bell14 c3
H bell14
measure bell14
cz bell14 d2
cnot bell8 c3
H bell8
measure bell8
cz bell8 b3
H c3
S* e
cnot a6 e
T* e
cnot b6 e
T* e
cnot a6 e
S e
H bell16
cnot bell16 bell17
cnot c1 bell17
measure bell17
cnot bell17 bell16
cnot bell16 e
cnot b6 e
T e
cnot c5 e
T* e
cnot bell16 e
S e
cnot c3 e
T* e
cnot c5 e
T e
H bell18
cnot bell18 bell19
cnot d5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 e
cnot c3 e
T e
cnot b6 e
T* e
cnot bell18 e
H bell18
measure bell18
cz bell18 d5
cnot b6 e
H e
T* c3
cnot c5 c3
T c3
cnot c5 c3
H c3
T* c3
cnot bell16 c3
T c3
cnot e c3
T* c3
cnot bell16 c3
H bell16
measure bell16
cz bell16 c1
T c3
cnot e c3
H c3
T* d1
H bell20
cnot bell20 bell21
cnot c2 bell21
measure bell21
cnot bell21 bell20
cnot bell20 d1
T d1
cnot bell20 d1
H d1
S* c1
H bell22
cnot bell22 bell23
cnot c5 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c1
T c1
H bell24
cnot bell24 bell25
cnot e bell25
measure bell25
cnot bell25 bell24
cnot bell24 c1
cnot bell22 c1
H bell22
measure bell22
cz bell22 c5
T c1
cnot bell24 c1
H c1
T d0
cnot b1 d0
T* d0
cnot b1 d0
H d0
T d4
cnot b5 d4
T* d4
cnot b5 d4
H d4
S* c5
H c5
T* d5
H bell26
cnot bell26 bell27
cnot b6 bell27
measure bell27
cnot bell27 bell26
cnot bell26 d5
T d5
cnot bell26 d5
H d5
T* d0
cnot b0 d0
T d0
cnot bell24 d0
T* d0
cnot b0 d0
T d0
cnot bell24 d0
H d0
T* d1
cnot c0 d1
T d1
cnot bell24 d1
T* d1
cnot c0 d1
T d1
cnot bell24 d1
H d1
T* d4
cnot b4 d4
T d4
H bell28
cnot bell28 bell29
cnot c3 bell29
measure bell29
cnot bell29 bell28
cnot bell28 d4
T* d4
cnot b4 d4
T d4
cnot bell28 d4
H d4
T* d5
cnot bell28 d5
T d5
cnot c4 d5
T* d5
cnot bell28 d5
T d5
cnot c4 d5
H d5
T* c0
cnot c1 c0
T c0
cnot bell20 c0
T* c0
cnot c1 c0
cnot bell24 c0
cnot bell20 c0
H bell20
measure bell20
cz bell20 c2
T c0
cnot bell24 c0
H c0
T* c2
H bell30
cnot bell30 bell31
cnot c1 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c2
T c2
cnot bell30 c2
H bell30
measure bell30
cz bell30 c1
H c2
T d2
cnot b3 d2
T* d2
cnot b3 d2
H d2
T* c4
cnot bell26 c4
H bell32
cnot bell32 bell33
cnot c5 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c4
T* c4
cnot bell26 c4
H bell26
measure bell26
cz bell26 b6
T c4
cnot bell28 c4
cnot bell32 c4
T c4
cnot bell28 c4
H c4
T* d2
cnot b2 d2
T d2
H bell34
cnot bell34 bell35
cnot d1 bell35
measure bell35
cnot bell35 bell34
cnot bell34 d2
T* d2
cnot b2 d2
T d2
cnot bell34 d2
H d2
cnot b2 b3
cnot c2 b3
T* b3
cnot b2 b3
T b3
cnot bell2 b3
cnot c2 b3
T b3
cnot d0 b1
cnot bell24 b0
cnot bell28 b4
cnot bell34 b2
cnot d2 b3
cnot d4 b5
H bell36
cnot bell36 bell37
cnot d5 bell37
measure bell37
cnot bell37 bell36
cnot bell36 b6
H bell36
measure bell36
cz bell36 d5
cnot a6 b6
cnot a5 b5
cnot a4 b4
cnot a2 b2
cnot a1 b1
cnot bell0 b0
H d2
cnot b0 c0
T c0
cnot b1 c0
T c0
cnot b0 c0
T c0
cnot d0 c0
cnot a1 c0
T c0
cnot bell24 c0
cnot b0 c0
cnot bell0 c0
T* c0
cnot d0 c0
cnot b1 c0
cnot a1 c0
T c0
cnot bell24 c0
cnot b0 c0
cnot bell0 c0
H c0
cnot b2 c2
T c2
cnot b3 c2
T c2
cnot b2 c2
T c2
cnot bell34 c2
cnot b3 c2
cnot b2 c2
cnot a2 c2
T c2
cnot bell34 c2
cnot b2 c2
cnot a2 c2
H c2
T d2
cnot b2 d2
T d2
cnot bell34 d2
T* d2
cnot b2 d2
T* d2
cnot bell34 d2
H bell34
measure bell34
cz bell34 d1
H d2
cnot b4 c4
T c4
cnot b5 c4
T c4
cnot b4 c4
T c4
cnot bell28 c4
cnot b5 c4
cnot b4 c4
cnot a4 c4
T c4
cnot d4 c4
cnot b5 c4
cnot a5 c4
T* c4
cnot bell28 c4
cnot b4 c4
cnot a4 c4
T c4
cnot d4 c4
cnot b5 c4
cnot a5 c4
H c4
cnot b1 d0
T d0
cnot a1 d0
cnot bell24 d0
cnot b0 d0
cnot bell0 d0
cnot bell24 d0
cnot b1 d0
cnot b0 d0
cnot a1 d0
cnot bell0 d0
H bell0
measure bell0
cz bell0 a0
H d0
H bell38
cnot bell38 bell39
cnot b2 bell39
measure bell39
cnot bell39 bell38
cnot bell38 d1
S d1
H bell40
cnot bell40 bell41
cnot a2 bell41
measure bell41
cnot bell41 bell40
cnot bell40 d1
S* d1
cnot bell38 d1
H bell38
measure bell38
cz bell38 b2
cnot bell40 d1
H bell40
measure bell40
cz bell40 a2
H d1
cnot b5 d4
T d4
cnot a5 d4
cnot bell28 d4
cnot b4 d4
cnot a4 d4
cnot bell28 d4
cnot b5 d4
cnot b4 d4
cnot a5 d4
cnot a4 d4
H d4
H bell42
cnot bell42 bell43
cnot b6 bell43
measure bell43
cnot bell43 bell42
cnot bell42 d5
T d5
H bell44
cnot bell44 bell45
cnot a6 bell45
measure bell45
cnot bell45 bell44
cnot bell44 d5
S* d5
cnot bell32 d5
T d5
cnot bell32 d5
H bell32
measure bell32
cz bell32 c5
cnot bell42 d5
cnot bell44 d5
H bell44
measure bell44
cz bell44 a6
H d5
T d1
cnot c0 d1
T* d1
cnot bell24 d1
T d1
cnot c0 d1
T* d1
cnot bell24 d1
H d1
cnot c0 c1
T* c1
H bell46
cnot bell46 bell47
cnot c2 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c1
T c1
cnot c0 c1
T* c1
cnot bell46 c1
H c1
T d0
cnot b0 d0
T d0
cnot bell24 d0
T* d0
cnot b0 d0
T* d0
cnot bell24 d0
H bell24
measure bell24
cz bell24 e
H d0
T d4
cnot b4 d4
T d4
cnot bell28 d4
T* d4
cnot b4 d4
T* d4
cnot bell28 d4
H d4
cnot b6 c5
T c5
H bell48
cnot bell48 bell49
cnot c4 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c5
T* c5
cnot b6 c5
T* c5
cnot bell48 c5
H c5
T d5
cnot bell28 d5
T* d5
cnot c4 d5
T d5
cnot bell28 d5
H bell28
measure bell28
cz bell28 c3
T* d5
cnot c4 d5
H d5
H bell50
cnot bell50 bell51
cnot b4 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c3
S c3
H bell52
cnot bell52 bell53
cnot a4 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c3
S* c3
cnot bell48 c3
cnot bell50 c3
H bell50
measure bell50
cz bell50 b4
cnot bell52 c3
H bell52
measure bell52
cz bell52 a4
T* c3
cnot bell48 c3
H bell48
measure bell48
cz bell48 c4
H c3
H bell54
cnot bell54 bell55
cnot c1 bell55
measure bell55
cnot bell55 bell54
cnot bell54 e
T* e
cnot c3 e
T e
cnot bell54 e
T* e
H bell56
cnot bell56 bell57
cnot b0 bell57
measure bell57
cnot bell57 bell56
cnot bell56 e
cnot c3 e
S e
H bell58
cnot bell58 bell59
cnot a0 bell59
measure bell59
cnot bell59 bell58
cnot bell58 e
S* e
H bell60
cnot bell60 bell61
cnot c0 bell61
measure bell61
cnot bell61 bell60
cnot bell60 e
cnot bell56 e
H bell56
measure bell56
cz bell56 b0
cnot bell58 e
H bell58
measure bell58
cz bell58 a0
T* e
cnot bell60 e
H bell60
measure bell60
cz bell60 c0
H e
T c3
cnot bell54 c3
T* c3
cnot bell54 c3
H bell54
measure bell54
cz bell54 c1
H c3
T c3
cnot c5 c3
T* c3
cnot e c3
T c3
cnot c5 c3
T* c3
cnot e c3
H c3
T c1
H c1
T d1
cnot bell46 d1
T* d1
H bell62
cnot bell62 bell63
cnot c3 bell63
measure bell63
cnot bell63 bell62
cnot bell62 d1
T d1
cnot bell46 d1
T* d1
cnot bell62 d1
H bell62
measure bell62
cz bell62 c3
H d1
T c5
cnot e c5
T* c5
cnot e c5
H c5
T d5
cnot bell42 d5
T d5
H bell64
cnot bell64 bell65
cnot e bell65
measure bell65
cnot bell65 bell64
cnot bell64 d5
T* d5
cnot bell42 d5
T* d5
cnot bell64 d5
H bell64
measure bell64
cz bell64 e
H d5
T c0
cnot c1 c0
T c0
cnot bell46 c0
T* c0
cnot c1 c0
cnot bell46 c0
H bell46
measure bell46
cz bell46 c2
H c0
T* d0
cnot b1 d0
T* d0
cnot d1 d0
T d0
cnot b1 d0
T d0
cnot d1 d0
H d0
T c2
H bell66
cnot bell66 bell67
cnot c1 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c2
T c2
H bell68
cnot bell68 bell69
cnot c3 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c2
cnot bell66 c2
H bell66
measure bell66
cz bell66 c1
T* c2
cnot bell68 c2
H c2
T* d2
cnot b3 d2
T* d2
cnot bell68 d2
T d2
cnot b3 d2
T d2
cnot bell68 d2
H bell68
measure bell68
cz bell68 c3
H d2
T c4
cnot bell42 c4
H bell70
cnot bell70 bell71
cnot c5 bell71
measure bell71
cnot bell71 bell70
cnot bell70 c4
T c4
cnot bell42 c4
H bell42
measure bell42
cz bell42 b6
T c4
cnot bell70 c4
H bell70
measure bell70
cz bell70 c5
H c4
T* d4
cnot b5 d4
T* d4
cnot d5 d4
T d4
cnot b5 d4
T d4
cnot d5 d4
H d4
T e
cnot a6 e
T e
cnot b6 e
T* e
cnot a6 e
S e
cnot b6 e
cnot a6 b6
cnot a5 b5
cnot a4 b4
cnot bell2 b3
cnot a2 b2
cnot a1 b1
H bell72
cnot bell72 bell73
cnot a0 bell73
measure bell73
cnot bell73 bell72
cnot bell72 b0
H e
T* c0
cnot b0 c0
cnot bell72 c0
T* c0
cnot b1 c0
cnot a1 c0
T* c0
cnot b0 c0
cnot bell72 c0
T* c0
cnot b1 c0
cnot a1 c0
H c0
T* d0
cnot bell72 d0
T d0
cnot b0 d0
T d0
cnot bell72 d0
T* d0
cnot b0 d0
H d0
T* c1
H c1
S* d1
cnot a1 d1
T d1
cnot b1 d1
cnot a1 d1
T* d1
cnot b1 d1
H d1
T* c2
cnot b2 c2
cnot a2 c2
T* c2
cnot b3 c2
cnot bell2 c2
T* c2
cnot b2 c2
cnot a2 c2
T* c2
cnot b3 c2
cnot bell2 c2
H bell2
measure bell2
cz bell2 a3
H c2
T* d2
cnot a2 d2
T d2
cnot b2 d2
T d2
cnot a2 d2
T* d2
cnot b2 d2
H d2
T* c3
cnot a3 c3
T c3
H bell74
cnot bell74 bell75
cnot b3 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c3
cnot a3 c3
T* c3
cnot bell74 c3
H bell74
measure bell74
cz bell74 b3
H c3
T* c4
cnot b4 c4
cnot a4 c4
T* c4
cnot b5 c4
cnot a5 c4
T* c4
cnot b4 c4
cnot a4 c4
T* c4
cnot b5 c4
cnot a5 c4
H c4
T* d4
cnot a4 d4
T d4
cnot b4 d4
T d4
cnot a4 d4
T* d4
cnot b4 d4
H d4
T* c5
cnot b6 c5
cnot a6 c5
T* c5
cnot b6 c5
cnot a6 c5
H c5
S* d5
cnot a5 d5
T d5
cnot b5 d5
cnot a5 d5
T* d5
cnot b5 d5
H d5
S b0
cnot bell72 b0
S* b0
T b1
S b2
cnot a2 b2
S* b2
T b3
S b4
cnot a4 b4
S* b4
T b5
T b6
cnot a6 b6
S* b6
cnot a6 b6
cnot a4 b4
cnot a2 b2
cnot bell72 b0
H bell72
measure bell72
cz bell72 a0
X b0
X b1
X b2
X b3
X b4
X b5
X b6
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
END
