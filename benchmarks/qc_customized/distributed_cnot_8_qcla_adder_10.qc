# Hyperedge cut (ebits): 34

# Actual ebits used (Synthesis): 35
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/qcla_adder_10.qc):
#   Qubits: 36
#   H: 50
#   T: 238
#   cnot: 233
#   Depth: 64
#   T depth: 30
# Result (109.299ms):
#   Qubits: 106
#   H: 120
#   S: 10
#   T: 162
#   cnot: 331
#   cz: 37
#   measure: 70
#   reset: 72
#   Depth: 106
#   T depth: 28


# Result Circuit
.v a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 d6 a7 b7 c7 a8 b8 c8 d8 a9 b9 c9 e bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell8 bell9
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 a8 b8 a9 b9
.o a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 d6 a7 b7 c7 a8 b8 c8 d8 a9 b9 c9 e
BEGIN 
H c0
H c1
H c2
H d2
H c3
H c4
H d4
H c5
H d5
H c6
H d6
H c7
H c8
H d8
H c9
T c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T* c0
cnot b0 c0
cnot a9 b9
cnot a8 b8
cnot a7 b7
H bell0
cnot bell0 bell1
cnot a6 bell1
measure bell1
cnot bell1 bell0
cnot bell0 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a2 b2
cnot a1 b1
H c0
T c2
H bell2
cnot bell2 bell3
cnot b2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c2
T* c2
cnot b3 c2
T c2
cnot bell2 c2
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
H bell4
cnot bell4 bell5
cnot b4 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c4
T* c4
H bell6
cnot bell6 bell7
cnot b5 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c4
T c4
cnot bell4 c4
T* c4
cnot bell6 c4
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
T c6
H bell8
cnot bell8 bell9
cnot b6 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c6
T* c6
H bell10
cnot bell10 bell11
cnot b7 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c6
T c6
cnot bell8 c6
T* c6
cnot bell10 c6
H c6
T d6
cnot bell0 d6
T* d6
cnot b6 d6
T* d6
cnot bell0 d6
H bell0
measure bell0
cz bell0 a6
T d6
cnot b6 d6
H d6
T c8
H bell12
cnot bell12 bell13
cnot b8 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c8
T* c8
cnot b9 c8
T c8
cnot bell12 c8
T* c8
cnot b9 c8
H c8
T d8
H bell14
cnot bell14 bell15
cnot a8 bell15
measure bell15
cnot bell15 bell14
cnot bell14 d8
T* d8
cnot bell12 d8
T* d8
cnot bell14 d8
H bell14
measure bell14
cz bell14 a8
T d8
cnot bell12 d8
H d8
H bell16
cnot bell16 bell17
cnot a1 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c1
T* c1
H bell18
cnot bell18 bell19
cnot b1 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c1
T* c1
cnot bell16 c1
H bell16
measure bell16
cz bell16 a1
S c1
H bell20
cnot bell20 bell21
cnot c0 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c1
T* c1
cnot bell18 c1
H bell18
measure bell18
cz bell18 b1
T c1
cnot bell20 c1
H bell20
measure bell20
cz bell20 c0
H c1
T* c5
cnot c4 c5
T c5
cnot c6 c5
T* c5
cnot c4 c5
T c5
cnot c6 c5
H c5
H bell22
cnot bell22 bell23
cnot a5 bell23
measure bell23
cnot bell23 bell22
cnot bell22 d5
T* d5
cnot bell6 d5
T* d5
cnot bell22 d5
H bell22
measure bell22
cz bell22 a5
S d5
H bell24
cnot bell24 bell25
cnot d4 bell25
measure bell25
cnot bell25 bell24
cnot bell24 d5
T* d5
cnot bell6 d5
T d5
cnot bell24 d5
H bell24
measure bell24
cz bell24 d4
H d5
T c3
cnot a3 c3
T* c3
cnot b3 c3
T* c3
cnot a3 c3
S c3
H bell26
cnot bell26 bell27
cnot c1 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c3
cnot b3 c3
T* c3
cnot c2 c3
T c3
cnot bell26 c3
T* c3
H bell28
cnot bell28 bell29
cnot d2 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c3
cnot c2 c3
T c3
cnot b3 c3
T* c3
cnot bell28 c3
H bell28
measure bell28
cz bell28 d2
cnot b3 c3
H c3
T d5
cnot c6 d5
T* d5
cnot c7 d5
T d5
cnot c6 d5
T* d5
cnot c7 d5
H d5
H bell30
cnot bell30 bell31
cnot a7 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c7
T* c7
cnot bell10 c7
T* c7
cnot bell30 c7
H bell30
measure bell30
cz bell30 a7
S c7
H bell32
cnot bell32 bell33
cnot c3 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c7
cnot bell10 c7
T c7
cnot c5 c7
T* c7
cnot bell32 c7
T c7
H bell34
cnot bell34 bell35
cnot d6 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c7
cnot c5 c7
T c7
cnot bell10 c7
T* c7
cnot c6 c7
cnot bell34 c7
H bell34
measure bell34
cz bell34 d6
cnot bell10 c7
T* c7
cnot c6 c7
H c7
T d5
cnot bell32 d5
T* d5
cnot c4 d5
T d5
cnot bell32 d5
T* d5
cnot c4 d5
H d5
T* d2
H bell36
cnot bell36 bell37
cnot b3 bell37
measure bell37
cnot bell37 bell36
cnot bell36 d2
T d2
cnot bell36 d2
H bell36
measure bell36
cz bell36 b3
H d2
T* d4
cnot b5 d4
T d4
cnot b5 d4
H d4
T* d6
cnot b7 d6
T d6
cnot b7 d6
H d6
T* d8
cnot b9 d8
T d8
cnot c9 d8
T* d8
cnot b9 d8
T d8
cnot c9 d8
H d8
T* c5
cnot bell32 c5
T c5
cnot bell32 c5
H c5
T c2
cnot bell26 c2
T* c2
cnot bell26 c2
H bell26
measure bell26
cz bell26 c1
H c2
T c4
cnot c5 c4
T* c4
cnot c6 c4
T c4
cnot c5 c4
cnot bell32 c4
cnot c6 c4
T* c4
cnot bell32 c4
H bell32
measure bell32
cz bell32 c3
H c4
T c6
cnot c5 c6
T* c6
cnot c5 c6
H c6
T c8
H bell38
cnot bell38 bell39
cnot c7 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c8
T* c8
cnot c9 c8
T c8
cnot bell38 c8
T* c8
cnot c9 c8
H c8
T* d2
cnot b2 d2
T d2
cnot c1 d2
T* d2
cnot b2 d2
T d2
cnot c1 d2
H d2
T* d4
cnot b4 d4
T d4
H bell40
cnot bell40 bell41
cnot c3 bell41
measure bell41
cnot bell41 bell40
cnot bell40 d4
T* d4
cnot b4 d4
T d4
cnot bell40 d4
H bell40
measure bell40
cz bell40 c3
H d4
T* d6
cnot b6 d6
T d6
H bell42
cnot bell42 bell43
cnot d5 bell43
measure bell43
cnot bell43 bell42
cnot bell42 d6
T* d6
cnot b6 d6
T d6
cnot bell42 d6
H bell42
measure bell42
cz bell42 d5
H d6
T* d8
cnot bell12 d8
T d8
cnot bell38 d8
T* d8
cnot bell12 d8
T d8
cnot bell38 d8
H d8
T c9
cnot a9 c9
T* c9
cnot b9 c9
T* c9
cnot a9 c9
S c9
cnot bell38 c9
cnot b9 c9
T* c9
cnot bell38 c9
H bell38
measure bell38
cz bell38 c7
H c9
T c5
H c5
T c2
cnot bell2 c2
T* c2
cnot b3 c2
T c2
cnot bell2 c2
H bell2
measure bell2
cz bell2 b2
T* c2
cnot b3 c2
H c2
T c4
cnot bell4 c4
T* c4
cnot bell6 c4
T c4
cnot bell4 c4
H bell4
measure bell4
cz bell4 b4
T* c4
cnot bell6 c4
H bell6
measure bell6
cz bell6 b5
H c4
T c6
cnot bell8 c6
T* c6
cnot bell10 c6
T c6
cnot bell8 c6
H bell8
measure bell8
cz bell8 b6
T* c6
cnot bell10 c6
H bell10
measure bell10
cz bell10 b7
H c6
T c8
cnot bell12 c8
T* c8
cnot b9 c8
T c8
cnot bell12 c8
H bell12
measure bell12
cz bell12 b8
T* c8
cnot b9 c8
H c8
T a2
cnot a2 b2
T b2
H bell44
cnot bell44 bell45
cnot b2 bell45
measure bell45
cnot bell45 bell44
cnot bell44 b3
H bell46
cnot bell46 bell47
cnot a2 bell47
measure bell47
cnot bell47 bell46
cnot bell46 b3
S* b3
T a3
cnot b3 a3
cnot bell44 a3
cnot bell46 a3
T a3
T a4
cnot a4 b4
T b4
cnot b4 b5
cnot a4 b5
S* b5
T a5
cnot b5 a5
cnot b4 a5
cnot a4 a5
T a5
T a6
H bell48
cnot bell48 bell49
cnot a6 bell49
measure bell49
cnot bell49 bell48
cnot bell48 b6
T b6
cnot b6 b7
cnot bell48 b7
S* b7
T a7
cnot b7 a7
cnot b6 a7
cnot bell48 a7
T a7
T a8
cnot a8 b8
T b8
H bell50
cnot bell50 bell51
cnot b8 bell51
measure bell51
cnot bell51 bell50
cnot bell50 b9
H bell52
cnot bell52 bell53
cnot a8 bell53
measure bell53
cnot bell53 bell52
cnot bell52 b9
S* b9
T a9
cnot b9 a9
cnot bell50 a9
cnot bell52 a9
T a9
T a0
T b0
cnot a0 b0
T* b0
T a1
S* b1
cnot a1 b1
T b1
T* c0
cnot b1 c0
cnot a1 c0
T c0
cnot b2 c1
cnot a2 c1
T c1
T* c3
H bell54
cnot bell54 bell55
cnot b4 bell55
measure bell55
cnot bell55 bell54
cnot bell54 c3
H bell54
measure bell54
cz bell54 b4
H bell56
cnot bell56 bell57
cnot a4 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c3
H bell56
measure bell56
cz bell56 a4
T c3
H bell58
cnot bell58 bell59
cnot c7 bell59
measure bell59
cnot bell59 bell58
cnot bell50 bell58
cnot bell52 bell58
H bell60
cnot bell60 bell61
cnot bell58 bell61
measure bell61
cnot bell61 bell60
reset bell61
cnot c7 bell60
cnot bell60 c7
H bell60
measure bell60
cz bell60 a8
cz bell60 b8
H bell58
measure bell58
cz bell58 c7
T c7
T* d5
H bell62
cnot bell62 bell63
cnot d5 bell63
measure bell63
cnot bell63 bell62
cnot b6 bell62
cnot bell48 bell62
H bell64
cnot bell64 bell65
cnot bell62 bell65
measure bell65
cnot bell65 bell64
reset bell65
cnot d5 bell64
cnot bell64 d5
H bell64
measure bell64
cz bell64 a6
cz bell64 b6
H bell62
measure bell62
cz bell62 d5
T d5
cnot bell50 b9
H bell50
measure bell50
cz bell50 b8
cnot b9 c8
cnot b6 b7
cnot b7 d6
cnot b5 d4
cnot bell44 b3
H bell44
measure bell44
cz bell44 b2
cnot b4 d4
H bell66
cnot bell66 bell67
cnot b3 bell67
measure bell67
cnot bell67 bell66
cnot bell66 d2
H bell66
measure bell66
cz bell66 b3
cnot b4 b5
cnot b9 a9
H bell68
cnot bell68 bell69
cnot b0 bell69
measure bell69
cnot bell69 bell68
cnot bell68 e
H bell68
measure bell68
cz bell68 b0
cnot a9 b9
cnot b7 a7
cnot a7 b7
cnot bell48 a7
cnot bell48 d6
H bell48
measure bell48
cz bell48 a6
cnot bell52 c8
cnot bell52 a9
H bell52
measure bell52
cz bell52 a8
cnot b5 a5
cnot a5 b5
cnot a4 a5
cnot b3 a3
cnot a4 d4
cnot a3 b3
cnot a2 d2
cnot a0 b0
cnot bell46 a3
H bell46
measure bell46
cz bell46 a2
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
END
