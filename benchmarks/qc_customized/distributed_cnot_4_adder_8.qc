# Hyperedge cut (ebits): 32

# Actual ebits used (Synthesis): 34
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/adder_8.qc):
#   Qubits: 24
#   H: 80
#   T: 399
#   X: 12
#   cnot: 409
#   Depth: 191
#   T depth: 82
# Result (115.158ms):
#   Qubits: 92
#   H: 148
#   S: 44
#   T: 215
#   Z: 23
#   cnot: 501
#   cz: 34
#   measure: 68
#   reset: 68
#   Depth: 263
#   T depth: 74


# Result Circuit
.v b0 a0 b1 a1 c1 b2 a2 b3 a3 c3 d3 b4 a4 b5 a5 c5 d5 e5 b6 a6 b7 a7 z c7 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell7 bell8 bell9
.i b0 a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 b6 a6 b7 a7 z
.o b0 a0 b1 a1 c1 b2 a2 b3 a3 c3 d3 b4 a4 b5 a5 c5 d5 e5 b6 a6 b7 a7 z c7
BEGIN 
cnot a7 z
cnot a7 b7
cnot a5 c5
cnot a3 c3
cnot a5 b5
cnot a3 b3
cnot a1 c1
cnot a1 b1
H a1
H a3
H a5
H a7
T a1
cnot a0 a1
T* a1
cnot b0 a1
T a1
cnot a0 a1
T* a1
cnot b0 a1
H a1
T a3
H bell0
cnot bell0 bell1
cnot a2 bell1
measure bell1
cnot bell1 bell0
cnot bell0 a3
T* a3
cnot b2 a3
T a3
cnot bell0 a3
T* a3
cnot b2 a3
H a3
T a5
H bell2
cnot bell2 bell3
cnot a4 bell3
measure bell3
cnot bell3 bell2
cnot bell2 a5
T* a5
cnot b4 a5
T a5
cnot bell2 a5
T* a5
cnot b4 a5
H a5
T a7
cnot a6 a7
T* a7
cnot b6 a7
T a7
cnot a6 a7
T* a7
cnot b6 a7
H a7
H c1
H c3
H c5
H z
H d3
H d5
H c7
T c1
cnot a1 c1
T* c1
cnot b1 c1
T c1
cnot a1 c1
T* c1
cnot b2 a3
cnot b4 a5
cnot b6 a7
cnot b1 c1
cnot a6 a7
cnot a6 b6
cnot bell2 a5
cnot bell2 b4
cnot bell0 b2
cnot bell0 a3
H c1
S d3
cnot a3 d3
T* d3
cnot b3 d3
T d3
cnot a3 d3
S* d3
cnot b2 d3
cnot a3 d3
T d3
cnot b3 d3
T* d3
cnot b2 d3
cnot a3 d3
H d3
T c5
cnot b4 c5
cnot a5 c5
T* c5
cnot b5 c5
T c5
cnot b4 c5
cnot a5 c5
T* c5
cnot b5 c5
H c5
S d5
cnot a5 d5
T* d5
cnot b5 d5
T d5
cnot a5 d5
S* d5
cnot b4 d5
cnot a5 d5
T d5
cnot b5 d5
T* d5
cnot b4 d5
cnot a5 d5
H d5
S c7
cnot a7 c7
T* c7
cnot b7 c7
T c7
cnot a7 c7
S* c7
cnot b6 c7
cnot a7 c7
T c7
cnot b7 c7
T* c7
cnot b6 c7
cnot a7 c7
H c7
H e5
T e5
H bell4
cnot bell4 bell5
cnot c7 bell5
measure bell5
cnot bell5 bell4
cnot bell4 e5
T* e5
cnot d5 e5
T e5
cnot bell4 e5
T* e5
cnot d5 e5
H e5
S c3
cnot b2 c3
cnot a3 c3
T* c3
cnot b3 c3
T c3
cnot b2 c3
cnot a3 c3
T* c3
H bell6
cnot bell6 bell7
cnot c1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c3
cnot b3 c3
T* c3
cnot d3 c3
T c3
cnot bell6 c3
T* c3
cnot d3 c3
H c3
T c5
cnot bell4 c5
T* c5
H bell8
cnot bell8 bell9
cnot z bell9
measure bell9
cnot bell9 bell8
cnot bell8 c5
T c5
cnot bell4 c5
T* c5
cnot bell8 c5
H bell8
measure bell8
cz bell8 z
H c5
T c5
H bell10
cnot bell10 bell11
cnot c3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c5
T* c5
cnot d5 c5
T c5
cnot bell10 c5
H bell10
measure bell10
cz bell10 c3
T* c5
cnot d5 c5
H c5
T* z
Z z
cnot b6 z
cnot a7 z
T* z
cnot b7 z
T z
cnot b6 z
cnot a7 z
T* z
H bell12
cnot bell12 bell13
cnot c3 bell13
measure bell13
cnot bell13 bell12
cnot bell12 z
cnot b7 z
T* z
H bell14
cnot bell14 bell15
cnot e5 bell15
measure bell15
cnot bell15 bell14
cnot bell14 z
T z
cnot bell12 z
H bell12
measure bell12
cz bell12 c3
T* z
cnot c7 z
cnot bell14 z
H bell14
measure bell14
cz bell14 e5
T* z
cnot c7 z
H z
T e5
H bell16
cnot bell16 bell17
cnot c3 bell17
measure bell17
cnot bell17 bell16
cnot bell16 e5
T* e5
cnot bell16 e5
H e5
T e5
cnot bell4 e5
T* e5
cnot d5 e5
T e5
cnot bell4 e5
T* e5
cnot d5 e5
H e5
T d3
cnot bell6 d3
T* d3
cnot bell6 d3
H d3
T* d5
Z d5
cnot bell16 d5
T* d5
cnot bell4 d5
cnot bell16 d5
S* d5
cnot bell4 d5
H bell4
measure bell4
cz bell4 c7
H d5
T* c7
Z c7
H c7
S c7
cnot a7 c7
T* c7
cnot b7 c7
T c7
cnot a7 c7
S* c7
cnot b6 c7
cnot a7 c7
T c7
cnot b7 c7
T* c7
cnot b2 a3
cnot b4 a5
cnot b6 a7
cnot a7 c7
cnot a6 b6
cnot bell2 b4
cnot bell0 b2
H c7
T a1
cnot b1 a1
T* a1
cnot b1 a1
H a1
T* a3
Z a3
cnot b2 a3
cnot bell0 a3
S a3
cnot b3 a3
S* a3
cnot b2 a3
cnot bell0 a3
T a3
Z a3
cnot d3 a3
T a3
cnot b2 a3
cnot bell0 a3
T a3
cnot b3 a3
T* a3
cnot b2 a3
cnot bell0 a3
T* a3
cnot d3 a3
H a3
T* a5
Z a5
cnot b4 a5
cnot bell2 a5
S a5
cnot b5 a5
S* a5
cnot b4 a5
cnot bell2 a5
T a5
Z a5
cnot d5 a5
T a5
cnot b4 a5
cnot bell2 a5
T a5
cnot b5 a5
T* a5
cnot b4 a5
cnot bell2 a5
T* a5
cnot d5 a5
H a5
T* a7
Z a7
cnot b6 a7
cnot a6 a7
S a7
cnot b7 a7
S* a7
cnot b6 a7
cnot a6 a7
T a7
Z a7
cnot b7 a7
H a7
T a1
cnot a0 a1
T* a1
cnot b0 a1
T a1
cnot a0 a1
T* a1
cnot b0 a1
H a1
T a3
cnot bell0 a3
T* a3
cnot b2 a3
T a3
cnot bell0 a3
H bell0
measure bell0
cz bell0 a2
T* a3
cnot b2 a3
H a3
T a5
cnot bell2 a5
T* a5
cnot b4 a5
T a5
cnot bell2 a5
H bell2
measure bell2
cz bell2 a4
T* a5
cnot b4 a5
H a5
T a7
cnot a6 a7
T* a7
cnot b6 a7
T a7
cnot a6 a7
T* a7
cnot b6 a7
H a7
T b1
cnot c1 a2
cnot bell6 a3
cnot c3 a4
cnot bell16 a5
H bell18
cnot bell18 bell19
cnot c5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 a6
cnot bell18 a7
cnot bell6 b2
cnot bell6 b3
H bell6
measure bell6
cz bell6 c1
cnot bell18 b6
cnot bell16 b4
cnot bell16 b5
H bell16
measure bell16
cz bell16 c3
cnot bell18 b7
H bell18
measure bell18
cz bell18 c5
cnot a7 b7
cnot a6 a7
cnot a6 b6
cnot a5 b5
H bell20
cnot bell20 bell21
cnot a4 bell21
measure bell21
cnot bell21 bell20
cnot bell20 a5
cnot bell20 b4
cnot a3 b3
H bell22
cnot bell22 bell23
cnot a2 bell23
measure bell23
cnot bell23 bell22
cnot bell22 b2
cnot a1 b1
cnot bell22 a3
H a1
H bell24
cnot bell24 bell25
cnot b3 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c1
H bell26
cnot bell26 bell27
cnot a3 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c1
cnot a2 c1
T c1
Z c1
H bell28
cnot bell28 bell29
cnot d3 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c1
S* c1
cnot bell28 c1
H bell28
measure bell28
cz bell28 d3
cnot bell24 c1
H bell24
measure bell24
cz bell24 b3
cnot bell26 c1
H bell26
measure bell26
cz bell26 a3
cnot a2 c1
H a3
H bell30
cnot bell30 bell31
cnot b5 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c3
H bell32
cnot bell32 bell33
cnot a5 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c3
cnot a4 c3
T c3
Z c3
H bell34
cnot bell34 bell35
cnot d5 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c3
S* c3
cnot bell34 c3
H bell34
measure bell34
cz bell34 d5
cnot bell30 c3
H bell30
measure bell30
cz bell30 b5
cnot bell32 c3
H bell32
measure bell32
cz bell32 a5
cnot a4 c3
H a5
H bell36
cnot bell36 bell37
cnot b7 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c5
H bell38
cnot bell38 bell39
cnot a7 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c5
H bell40
cnot bell40 bell41
cnot a6 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c5
T c5
Z c5
cnot bell36 c5
H bell36
measure bell36
cz bell36 b7
cnot bell38 c5
H bell38
measure bell38
cz bell38 a7
cnot bell40 c5
H bell40
measure bell40
cz bell40 a6
H a7
T a1
cnot a0 a1
T* a1
cnot b0 a1
T a1
cnot a0 a1
T* a1
cnot b0 a1
H a1
T a3
cnot bell22 a3
T* a3
cnot b2 a3
T a3
cnot bell22 a3
T* a3
cnot b2 a3
H a3
T a5
cnot bell20 a5
T* a5
cnot b4 a5
T a5
cnot bell20 a5
T* a5
cnot b4 a5
H a5
T a7
cnot a6 a7
T* a7
cnot b6 a7
T a7
cnot a6 a7
T* a7
cnot b6 a7
H a7
cnot a7 b7
cnot a5 b5
cnot a3 b3
cnot a1 b1
H a1
H a3
H a5
H a7
T a1
cnot a0 a1
T* a1
cnot b0 a1
T a1
cnot a0 a1
T* a1
cnot b0 a1
H a1
T a3
cnot bell22 a3
T* a3
cnot b2 a3
T a3
cnot bell22 a3
H bell22
measure bell22
cz bell22 a2
T* a3
cnot b2 a3
H a3
T a5
cnot bell20 a5
T* a5
cnot b4 a5
T a5
cnot bell20 a5
H bell20
measure bell20
cz bell20 a4
T* a5
cnot b4 a5
H a5
T a7
cnot a6 a7
T* a7
cnot b6 a7
T a7
cnot a6 a7
T* a7
cnot b6 a7
H a7
cnot c1 a2
cnot c3 a4
H bell42
cnot bell42 bell43
cnot c5 bell43
measure bell43
cnot bell43 bell42
cnot bell42 a6
H bell44
cnot bell44 bell45
cnot c1 bell45
measure bell45
cnot bell45 bell44
cnot bell44 b2
H bell44
measure bell44
cz bell44 c1
H bell46
cnot bell46 bell47
cnot c3 bell47
measure bell47
cnot bell47 bell46
cnot bell46 b4
H bell46
measure bell46
cz bell46 c3
cnot bell42 b6
H bell42
measure bell42
cz bell42 c5
cnot a6 a7
H bell48
cnot bell48 bell49
cnot a4 bell49
measure bell49
cnot bell49 bell48
cnot bell48 a5
cnot a5 b5
cnot a3 b3
H bell50
cnot bell50 bell51
cnot a2 bell51
measure bell51
cnot bell51 bell50
cnot bell50 b3
cnot a1 b1
cnot a0 b0
cnot bell50 a3
H a1
H a3
H a5
T a1
cnot a0 a1
T* a1
cnot b0 a1
T* a1
cnot a0 a1
T a1
cnot b0 a1
H a1
T a3
cnot bell50 a3
T* a3
cnot b2 a3
T* a3
cnot bell50 a3
T a3
cnot b2 a3
H a3
T a5
cnot bell48 a5
T* a5
cnot b4 a5
T* a5
cnot bell48 a5
T a5
cnot b4 a5
H a5
Z d3
cnot a3 d3
T* d3
cnot b3 d3
T* d3
cnot a3 d3
S d3
cnot b2 d3
cnot a3 d3
cnot bell50 d3
T d3
cnot b3 d3
T d3
cnot b2 a3
cnot b4 a5
cnot bell48 a5
cnot a3 d3
cnot bell48 b4
cnot bell50 d3
cnot bell50 b2
cnot bell50 a3
H d3
Z d5
cnot a5 d5
T d5
cnot b5 d5
T d5
cnot a5 d5
S d5
cnot b4 d5
cnot a5 d5
T* d5
cnot b5 d5
T* d5
cnot b4 d5
cnot a5 d5
H d5
H bell52
cnot bell52 bell53
cnot a6 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c5
S c5
H bell54
cnot bell54 bell55
cnot b6 bell55
measure bell55
cnot bell55 bell54
cnot bell54 c5
S c5
cnot bell52 c5
H bell52
measure bell52
cz bell52 a6
cnot bell54 c5
H bell54
measure bell54
cz bell54 b6
H c5
T* c3
Z c3
cnot a4 c3
S c3
H bell56
cnot bell56 bell57
cnot b4 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c3
cnot a4 c3
S c3
H bell58
cnot bell58 bell59
cnot c5 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c3
cnot bell56 c3
H bell56
measure bell56
cz bell56 b4
T* c3
H bell60
cnot bell60 bell61
cnot d5 bell61
measure bell61
cnot bell61 bell60
cnot bell60 c3
T c3
cnot bell58 c3
H bell58
measure bell58
cz bell58 c5
T* c3
cnot bell60 c3
H bell60
measure bell60
cz bell60 d5
H c3
S c1
cnot a2 c1
S c1
H bell62
cnot bell62 bell63
cnot b2 bell63
measure bell63
cnot bell63 bell62
cnot bell62 c1
cnot a2 c1
S c1
H bell64
cnot bell64 bell65
cnot c3 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c1
cnot bell62 c1
H bell62
measure bell62
cz bell62 b2
T* c1
H bell66
cnot bell66 bell67
cnot d3 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c1
T c1
cnot bell64 c1
H bell64
measure bell64
cz bell64 c3
T* c1
cnot bell66 c1
H bell66
measure bell66
cz bell66 d3
H c1
T d3
cnot c3 d3
T* d3
cnot c3 d3
H d3
T d5
cnot c5 d5
T* d5
cnot c5 d5
H d5
T c1
cnot a1 c1
T* c1
cnot b1 c1
T* c1
cnot a1 c1
T c1
cnot b2 a3
cnot b4 a5
cnot b1 c1
cnot bell48 b4
cnot bell50 b2
H c1
S c3
cnot a3 c3
T* c3
cnot b3 c3
T* c3
cnot a3 c3
T c3
cnot b3 c3
H c3
S d3
cnot a3 d3
T* d3
cnot b3 d3
T* d3
cnot a3 d3
S d3
cnot b2 d3
cnot a3 d3
cnot bell50 d3
T d3
cnot b3 d3
T d3
cnot b2 d3
cnot a3 d3
cnot bell50 d3
H d3
S c5
cnot a5 c5
T* c5
cnot b5 c5
T* c5
cnot a5 c5
T c5
cnot b5 c5
H c5
S d5
cnot a5 d5
T* d5
cnot b5 d5
T* d5
cnot a5 d5
S d5
cnot b4 d5
cnot a5 d5
cnot bell48 d5
T d5
cnot b5 d5
T d5
cnot b4 d5
cnot a5 d5
cnot bell48 d5
H d5
T a1
cnot b1 a1
T a1
cnot b1 a1
H a1
T* a3
Z a3
cnot b2 a3
cnot bell50 a3
S* a3
cnot b3 a3
S* a3
cnot b2 a3
cnot bell50 a3
T* a3
Z a3
cnot b3 a3
H a3
T* a5
Z a5
cnot b4 a5
cnot bell48 a5
S* a5
cnot b5 a5
S* a5
cnot b4 a5
cnot bell48 a5
T* a5
Z a5
cnot b5 a5
H a5
T a1
cnot a0 a1
T* a1
cnot b0 a1
T* a1
cnot a0 a1
T a1
cnot b0 a1
H a1
T a3
cnot bell50 a3
T* a3
cnot b2 a3
T* a3
cnot bell50 a3
H bell50
measure bell50
cz bell50 a2
T a3
cnot b2 a3
H a3
T a5
cnot bell48 a5
T* a5
cnot b4 a5
T* a5
cnot bell48 a5
H bell48
measure bell48
cz bell48 a4
T a5
cnot b4 a5
H a5
S* a0
S b0
cnot a0 b0
S* b0
Z a2
S* b2
Z a4
S* b4
S a6
T* b1
T* b3
Z b3
T* b5
Z b5
cnot a6 b6
S* b6
cnot a6 b6
cnot a5 c5
cnot a3 c3
cnot a5 b5
cnot a3 b3
cnot a1 c1
cnot a1 b1
cnot a0 b0
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
END
