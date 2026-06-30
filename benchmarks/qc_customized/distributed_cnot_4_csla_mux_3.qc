# Hyperedge cut (ebits): 27

# Actual ebits used (Synthesis): 33
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/csla_mux_3.qc):
#   Qubits: 15
#   H: 20
#   T: 70
#   cnot: 80
#   Depth: 58
#   T depth: 26
# Result (22.192ms):
#   Qubits: 81
#   H: 86
#   T: 62
#   cnot: 217
#   cz: 36
#   measure: 66
#   reset: 67
#   swap: 7
#   Depth: 168
#   T depth: 29


# Result Circuit
.v cin a0 b0 c0 d0 a1 b1 c1 d1 e1 a2 b2 c2 d2 e2 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell7 bell8 bell9
.i cin a0 b0 a1 b1 a2 b2
.o cin a0 b0 c0 d0 a1 b1 c1 d1 e1 a2 b2 c2 d2 e2
BEGIN 
H c0
H c1
H c2
T c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T* c0
cnot b0 c0
H c0
T c1
H bell0
cnot bell0 bell1
cnot a1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c1
T* c1
H bell2
cnot bell2 bell3
cnot b1 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c1
T c1
cnot bell0 c1
H bell0
measure bell0
cz bell0 a1
T* c1
cnot bell2 c1
H bell2
measure bell2
cz bell2 b1
H c1
T c2
H bell4
cnot bell4 bell5
cnot a2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c2
T* c2
cnot b2 c2
T c2
cnot bell4 c2
T* c2
cnot b2 c2
H c2
cnot c2 e2
cnot c1 e1
H bell6
cnot bell6 bell7
cnot c0 bell7
measure bell7
cnot bell7 bell6
cnot bell6 d0
H bell6
measure bell6
cz bell6 c0
cnot bell4 b2
H bell4
measure bell4
cz bell4 a2
H bell8
cnot bell8 bell9
cnot a1 bell9
measure bell9
cnot bell9 bell8
cnot bell8 b1
H bell8
measure bell8
cz bell8 a1
cnot a0 b0
H c1
H e1
H c2
H e2
T e1
H bell10
cnot bell10 bell11
cnot b1 bell11
measure bell11
cnot bell11 bell10
cnot bell10 e1
T* e1
H bell12
cnot bell12 bell13
cnot c0 bell13
measure bell13
cnot bell13 bell12
cnot bell12 e1
T e1
cnot bell10 e1
T* e1
swap d0 d2
cnot bell12 e1
cnot bell12 d2
H bell12
measure bell12
cz bell12 c0
H bell14
cnot bell14 bell15
cnot c0 bell15
measure bell15
cnot bell15 bell14
cnot bell14 d0
H bell14
measure bell14
cz bell14 c0
H bell16
cnot bell16 bell17
cnot d2 bell17
measure bell17
cnot bell17 bell16
cnot bell16 b2
H bell16
measure bell16
cz bell16 d2
H bell18
cnot bell18 bell19
cnot b2 bell19
measure bell19
cnot bell19 bell18
cnot bell18 d2
H bell18
measure bell18
cz bell18 b2
cnot b0 c0
H e1
T* c1
cnot bell10 c1
T c1
H bell20
cnot bell20 bell21
cnot c0 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c1
T* c1
cnot bell10 c1
H bell10
measure bell10
cz bell10 b1
T c1
cnot bell20 c1
H c1
T c2
cnot b2 c2
T* c2
H bell22
cnot bell22 bell23
cnot c1 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c2
H bell22
measure bell22
cz bell22 c1
T c2
cnot b2 c2
T* c2
cnot c0 b1
H bell24
cnot bell24 bell25
cnot d2 bell25
measure bell25
cnot bell25 bell24
cnot bell24 b2
H bell24
measure bell24
cz bell24 d2
cnot d1 c1
H bell26
cnot bell26 bell27
cnot d1 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c2
H bell26
measure bell26
cz bell26 d1
cnot d2 d1
cnot e1 d2
cnot c1 d1
H bell28
cnot bell28 bell29
cnot c1 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c2
swap b2 d1
H bell30
cnot bell30 bell31
cnot b1 bell31
measure bell31
cnot bell31 bell30
cnot bell30 d1
H bell32
cnot bell32 bell33
cnot b0 bell33
measure bell33
cnot bell33 bell32
cnot bell32 d1
H c2
T* e2
cnot bell28 e2
cnot b2 e2
T e2
H bell34
cnot bell34 bell35
cnot d2 bell35
measure bell35
cnot bell35 bell34
cnot bell34 e2
T e2
cnot bell28 e2
H bell28
measure bell28
cz bell28 c1
cnot b2 e2
T* e2
cnot bell34 e2
H e2
cnot bell34 b2
H bell34
measure bell34
cz bell34 d2
cnot e1 c1
cnot e2 c2
cnot e1 d1
swap d1 e1
swap c1 d1
H bell36
cnot bell36 bell37
cnot b2 bell37
measure bell37
cnot bell37 bell36
cnot bell36 d1
cnot bell36 c1
cnot bell30 e1
H bell30
measure bell30
cz bell30 b1
swap b1 d1
cnot bell32 e1
cnot bell32 d1
cnot b0 b1
H e2
T d2
cnot bell36 d2
T* d2
cnot c1 d2
T* d2
H bell38
cnot bell38 bell39
cnot a2 bell39
measure bell39
cnot bell39 bell38
cnot bell38 d2
T d2
cnot c1 d2
cnot bell36 d2
cnot bell38 d2
H bell38
measure bell38
cz bell38 a2
H d2
T* d1
cnot bell32 d1
T d1
cnot bell20 d1
T* d1
H bell40
cnot bell40 bell41
cnot a1 bell41
measure bell41
cnot bell41 bell40
cnot bell40 d1
T d1
cnot bell20 d1
H bell20
measure bell20
cz bell20 c0
cnot bell32 d1
cnot bell40 d1
H bell40
measure bell40
cz bell40 a1
H d1
T e2
cnot c2 e2
T* e2
cnot cin e2
T e2
cnot c2 e2
T* e2
cnot cin e2
H e2
T* d2
cnot bell36 d2
T d2
H bell42
cnot bell42 bell43
cnot cin bell43
measure bell43
cnot bell43 bell42
cnot bell42 d2
T* d2
cnot bell36 d2
H bell36
measure bell36
cz bell36 b2
T d2
cnot bell42 d2
H d2
T d1
cnot bell32 d1
T* d1
cnot bell42 d1
T d1
cnot bell32 d1
H bell32
measure bell32
cz bell32 b0
T* d1
cnot bell42 d1
H bell42
measure bell42
cz bell42 cin
H d1
T a0
cnot a0 b0
T b0
T cin
H bell44
cnot bell44 bell45
cnot b0 bell45
measure bell45
cnot bell45 bell44
cnot bell44 cin
H bell46
cnot bell46 bell47
cnot a0 bell47
measure bell47
cnot bell47 bell46
cnot bell46 cin
T* cin
T* b2
cnot cin b2
cnot bell44 b2
cnot bell46 b2
T b2
T* c0
cnot b0 c0
cnot a0 c0
T c0
T c1
H bell48
cnot bell48 bell49
cnot c1 bell49
measure bell49
cnot bell49 bell48
cnot cin bell48
cnot b2 bell48
cnot bell44 bell48
cnot bell46 bell48
H bell50
cnot bell50 bell51
cnot bell48 bell51
measure bell51
cnot bell51 bell50
reset bell51
cnot c1 bell50
cnot bell50 c1
H bell50
measure bell50
cz bell50 a0
cz bell50 b0
cz bell50 b2
cz bell50 cin
H bell48
measure bell48
cz bell48 c1
T* c1
T c2
cnot cin c2
cnot bell44 c2
H bell44
measure bell44
cz bell44 b0
cnot bell46 c2
H bell46
measure bell46
cz bell46 a0
T* c2
T a1
T a2
H bell52
cnot bell52 bell53
cnot d1 bell53
measure bell53
cnot bell53 bell52
cnot bell52 a0
cnot b1 b0
cnot bell52 b1
H bell54
cnot bell54 bell55
cnot d2 bell55
measure bell55
cnot bell55 bell54
cnot bell54 b2
H bell54
measure bell54
cz bell54 d2
cnot bell52 c0
H bell52
measure bell52
cz bell52 d1
cnot d2 c1
H bell56
cnot bell56 bell57
cnot d1 bell57
measure bell57
cnot bell57 bell56
cnot bell56 cin
H bell56
measure bell56
cz bell56 d1
cnot e2 c2
cnot cin c2
H bell58
cnot bell58 bell59
cnot cin bell59
measure bell59
cnot bell59 bell58
cnot bell58 d1
H bell58
measure bell58
cz bell58 cin
cnot cin b2
H bell60
cnot bell60 bell61
cnot b1 bell61
measure bell61
cnot bell61 bell60
cnot bell60 b2
cnot bell60 cin
cnot bell60 c2
H bell60
measure bell60
cz bell60 b1
H bell62
cnot bell62 bell63
cnot b2 bell63
measure bell63
cnot bell63 bell62
cnot bell62 c1
H bell62
measure bell62
cz bell62 b2
cnot b1 c0
swap b0 d1
H bell64
cnot bell64 bell65
cnot d1 bell65
measure bell65
cnot bell65 bell64
cnot bell64 a0
H bell64
measure bell64
cz bell64 d1
swap a0 d1
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
END
