# Hyperedge cut (ebits): 25

# Actual ebits used (Synthesis): 28
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/qcla_com_7.qc):
#   Qubits: 24
#   H: 39
#   T: 203
#   X: 15
#   cnot: 186
#   Depth: 70
#   T depth: 31
# Result (57.614ms):
#   Qubits: 80
#   H: 93
#   S: 6
#   T: 95
#   X: 1
#   Z: 2
#   cnot: 226
#   cz: 28
#   measure: 56
#   reset: 56
#   Depth: 97
#   T depth: 25


# Result Circuit
.v a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell6 bell7 bell8 bell9
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6
.o a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6
BEGIN 
H c0
H c1
H c2
H d2
H c3
H c4
H d4
H d5
H c6
T c0
H bell0
cnot bell0 bell1
cnot a0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T c0
H bell2
cnot bell2 bell3
cnot b0 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
T* c0
cnot bell0 c0
T* c0
cnot bell2 c0
H bell4
cnot bell4 bell5
cnot a6 bell5
measure bell5
cnot bell5 bell4
cnot bell4 b6
cnot a5 b5
H bell6
cnot bell6 bell7
cnot a4 bell7
measure bell7
cnot bell7 bell6
cnot bell6 b4
H bell8
cnot bell8 bell9
cnot a3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 b3
cnot a2 b2
H bell10
cnot bell10 bell11
cnot a1 bell11
measure bell11
cnot bell11 bell10
cnot bell10 b1
H c0
T c2
H bell12
cnot bell12 bell13
cnot b2 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c2
T c2
cnot b3 c2
T c2
cnot bell12 c2
H bell12
measure bell12
cz bell12 b2
T c2
cnot b3 c2
H c2
T d2
cnot a2 d2
T d2
cnot b2 d2
T* d2
cnot a2 d2
T* d2
cnot b2 d2
H d2
T c4
cnot b4 c4
T c4
H bell14
cnot bell14 bell15
cnot b5 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c4
T c4
cnot b4 c4
T c4
cnot bell14 c4
H c4
T d4
cnot bell6 d4
T d4
cnot b4 d4
T* d4
cnot bell6 d4
T* d4
cnot b4 d4
H d4
S c1
cnot bell10 c1
T c1
cnot b1 c1
T* c1
cnot bell10 c1
cnot c0 c1
T* c1
cnot b1 c1
T* c1
cnot c0 c1
H c1
T c5
cnot b6 c5
T c5
H bell16
cnot bell16 bell17
cnot c4 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c5
T* c5
cnot b6 c5
T* c5
cnot bell16 c5
H bell16
measure bell16
cz bell16 c4
H c5
S d5
cnot a5 d5
T d5
cnot b5 d5
T* d5
cnot a5 d5
H bell18
cnot bell18 bell19
cnot d4 bell19
measure bell19
cnot bell19 bell18
cnot bell18 d5
T* d5
cnot b5 d5
T* d5
cnot bell18 d5
H bell18
measure bell18
cz bell18 d4
H d5
T* c3
Z c3
cnot bell8 c3
T c3
cnot b3 c3
T* c3
cnot bell8 c3
H bell20
cnot bell20 bell21
cnot c1 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c3
cnot b3 c3
T* c3
cnot c2 c3
T c3
cnot bell20 c3
H bell20
measure bell20
cz bell20 c1
T* c3
H bell22
cnot bell22 bell23
cnot d2 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c3
cnot c2 c3
T* c3
cnot b3 c3
T* c3
cnot bell22 c3
H bell22
measure bell22
cz bell22 d2
cnot b3 c3
H c3
T c3
H bell24
cnot bell24 bell25
cnot c5 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c3
T* c3
H bell26
cnot bell26 bell27
cnot c6 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c3
T c3
cnot bell24 c3
H bell24
measure bell24
cz bell24 c5
T* c3
cnot bell26 c3
H bell26
measure bell26
cz bell26 c6
H c3
T c5
cnot c6 c5
T* c5
cnot c6 c5
H c5
T* d5
H bell28
cnot bell28 bell29
cnot b6 bell29
measure bell29
cnot bell29 bell28
cnot bell28 d5
T* d5
H bell30
cnot bell30 bell31
cnot c6 bell31
measure bell31
cnot bell31 bell30
cnot bell30 d5
T d5
cnot bell28 d5
H bell28
measure bell28
cz bell28 b6
T d5
cnot bell30 d5
H bell30
measure bell30
cz bell30 c6
H d5
H bell32
cnot bell32 bell33
cnot c2 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c1
H bell34
cnot bell34 bell35
cnot c3 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c1
T* c1
cnot bell32 c1
H bell32
measure bell32
cz bell32 c2
T c1
cnot bell34 c1
H bell34
measure bell34
cz bell34 c3
H c1
cnot b1 c0
cnot c1 c0
T c0
cnot b1 c0
T c0
cnot c1 c0
H c0
cnot c3 c2
T c2
cnot c3 c2
H c2
H bell36
cnot bell36 bell37
cnot b3 bell37
measure bell37
cnot bell37 bell36
cnot bell36 d2
H bell38
cnot bell38 bell39
cnot c3 bell39
measure bell39
cnot bell39 bell38
cnot bell38 d2
T d2
cnot bell36 d2
H bell36
measure bell36
cz bell36 b3
T d2
cnot bell38 d2
H bell38
measure bell38
cz bell38 c3
H d2
H bell40
cnot bell40 bell41
cnot b6 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c4
H bell42
cnot bell42 bell43
cnot c5 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c4
T c4
cnot bell40 c4
H bell40
measure bell40
cz bell40 b6
T c4
cnot bell42 c4
H bell42
measure bell42
cz bell42 c5
H c4
cnot bell14 d4
H bell44
cnot bell44 bell45
cnot d5 bell45
measure bell45
cnot bell45 bell44
cnot bell44 d4
T d4
cnot bell14 d4
H bell14
measure bell14
cz bell14 b5
T d4
cnot bell44 d4
H bell44
measure bell44
cz bell44 d5
H d4
T* c0
cnot bell0 c0
T* c0
cnot bell2 c0
T c0
cnot bell0 c0
H bell0
measure bell0
cz bell0 a0
T c0
cnot bell2 c0
H bell2
measure bell2
cz bell2 b0
cnot bell4 b6
cnot a5 b5
cnot bell6 b4
cnot bell8 b3
cnot a2 b2
cnot bell10 b1
H c0
S* c1
cnot bell10 c1
T* c1
cnot b1 c1
cnot bell10 c1
H bell10
measure bell10
cz bell10 a1
T c1
cnot b1 c1
H c1
T* c2
H bell46
cnot bell46 bell47
cnot b2 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c2
H bell48
cnot bell48 bell49
cnot a2 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c2
T* c2
cnot b3 c2
cnot bell8 c2
T* c2
cnot bell46 c2
H bell46
measure bell46
cz bell46 b2
cnot bell48 c2
H bell48
measure bell48
cz bell48 a2
T* c2
cnot b3 c2
cnot bell8 c2
H c2
T* d2
cnot a2 d2
T* d2
cnot b2 d2
T d2
cnot a2 d2
T d2
cnot b2 d2
H d2
T c3
Z c3
cnot bell8 c3
T* c3
cnot b3 c3
cnot bell8 c3
H bell8
measure bell8
cz bell8 a3
T c3
cnot b3 c3
H c3
T* c4
cnot b4 c4
cnot bell6 c4
T* c4
H bell50
cnot bell50 bell51
cnot b5 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c4
H bell52
cnot bell52 bell53
cnot a5 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c4
T* c4
cnot b4 c4
cnot bell6 c4
T* c4
cnot bell50 c4
H bell50
measure bell50
cz bell50 b5
cnot bell52 c4
H bell52
measure bell52
cz bell52 a5
H c4
T* d4
cnot bell6 d4
T* d4
cnot b4 d4
T d4
cnot bell6 d4
H bell6
measure bell6
cz bell6 a4
T d4
cnot b4 d4
H d4
T* c5
cnot b6 c5
cnot bell4 c5
T* c5
cnot b6 c5
cnot bell4 c5
H c5
S* d5
cnot a5 d5
T* d5
cnot b5 d5
cnot a5 d5
T d5
cnot b5 d5
H d5
T c6
cnot bell4 c6
T c6
cnot b6 c6
S* c6
cnot bell4 c6
H bell4
measure bell4
cz bell4 a6
T* c6
cnot b6 c6
H c6
T* a6
T b6
H bell54
cnot bell54 bell55
cnot a6 bell55
measure bell55
cnot bell55 bell54
cnot bell54 b6
S b6
cnot bell54 b6
H bell54
measure bell54
cz bell54 a6
X c6
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
END
