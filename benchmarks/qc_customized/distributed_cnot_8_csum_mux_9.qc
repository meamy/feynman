# Hyperedge cut (ebits): 28

# Actual ebits used (Synthesis): 28
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/csum_mux_9.qc):
#   Qubits: 30
#   H: 28
#   T: 196
#   X: 28
#   cnot: 168
#   Depth: 53
#   T depth: 24
# Result (55.003ms):
#   Qubits: 86
#   H: 84
#   S: 28
#   T: 84
#   cnot: 254
#   cz: 28
#   measure: 56
#   reset: 56
#   Depth: 66
#   T depth: 16


# Result Circuit
.v c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 a0 a1 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 b0 b1 b2 b3 e70 e71 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell6 bell7 bell8 bell9
.i c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 e70 e71
.o c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 a0 a1 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 b0 b1 b2 b3 e70 e71
BEGIN 
H e10
H e11
H a0
H a1
H e30
H e31
H e50
H e51
H b0
H b1
H b2
H b3
H e70
H e71
S e10
H bell0
cnot bell0 bell1
cnot c00 bell1
measure bell1
cnot bell1 bell0
cnot bell0 e10
H bell2
cnot bell2 bell3
cnot c10 bell3
measure bell3
cnot bell3 bell2
cnot bell2 e10
T* e10
cnot bell0 e10
T* e10
cnot c11 e10
cnot bell2 e10
T* e10
cnot bell0 e10
T e10
cnot c11 e10
cnot bell0 e10
H e10
S e11
H bell4
cnot bell4 bell5
cnot c01 bell5
measure bell5
cnot bell5 bell4
cnot bell4 e11
cnot bell2 e11
T* e11
cnot bell4 e11
T* e11
cnot c11 e11
cnot bell2 e11
H bell2
measure bell2
cz bell2 c10
T* e11
cnot bell4 e11
T e11
cnot c11 e11
cnot bell4 e11
H e11
S a0
H bell6
cnot bell6 bell7
cnot c20 bell7
measure bell7
cnot bell7 bell6
cnot bell6 a0
cnot c30 a0
T* a0
cnot bell6 a0
T* a0
cnot c31 a0
cnot c30 a0
T* a0
cnot bell6 a0
T a0
cnot bell6 a0
cnot c31 a0
H a0
S a1
H bell8
cnot bell8 bell9
cnot c21 bell9
measure bell9
cnot bell9 bell8
cnot bell8 a1
H bell10
cnot bell10 bell11
cnot c30 bell11
measure bell11
cnot bell11 bell10
cnot bell10 a1
T* a1
cnot bell8 a1
T* a1
H bell12
cnot bell12 bell13
cnot c31 bell13
measure bell13
cnot bell13 bell12
cnot bell12 a1
cnot bell10 a1
H bell10
measure bell10
cz bell10 c30
T* a1
cnot bell8 a1
T a1
cnot bell8 a1
H bell8
measure bell8
cz bell8 c21
cnot bell12 a1
H bell12
measure bell12
cz bell12 c31
H a1
S e50
H bell14
cnot bell14 bell15
cnot c40 bell15
measure bell15
cnot bell15 bell14
cnot bell14 e50
H bell16
cnot bell16 bell17
cnot c50 bell17
measure bell17
cnot bell17 bell16
cnot bell16 e50
T* e50
cnot bell14 e50
T* e50
H bell18
cnot bell18 bell19
cnot c51 bell19
measure bell19
cnot bell19 bell18
cnot bell18 e50
cnot bell16 e50
T* e50
cnot bell14 e50
T e50
cnot bell18 e50
cnot bell14 e50
H bell14
measure bell14
cz bell14 c40
H e50
S e51
H bell20
cnot bell20 bell21
cnot c41 bell21
measure bell21
cnot bell21 bell20
cnot bell20 e51
cnot bell16 e51
T* e51
cnot bell20 e51
T* e51
cnot bell18 e51
cnot bell16 e51
H bell16
measure bell16
cz bell16 c50
T* e51
cnot bell20 e51
T e51
cnot bell18 e51
H bell18
measure bell18
cz bell18 c51
cnot bell20 e51
H bell20
measure bell20
cz bell20 c41
H e51
S b0
H bell22
cnot bell22 bell23
cnot c60 bell23
measure bell23
cnot bell23 bell22
cnot bell22 b0
H bell24
cnot bell24 bell25
cnot c70 bell25
measure bell25
cnot bell25 bell24
cnot bell24 b0
T* b0
cnot bell22 b0
T* b0
H bell26
cnot bell26 bell27
cnot c71 bell27
measure bell27
cnot bell27 bell26
cnot bell26 b0
cnot bell24 b0
T* b0
cnot bell22 b0
T b0
cnot bell22 b0
H bell22
measure bell22
cz bell22 c60
cnot bell26 b0
H b0
S b1
H bell28
cnot bell28 bell29
cnot c61 bell29
measure bell29
cnot bell29 bell28
cnot bell28 b1
cnot bell24 b1
T* b1
cnot bell28 b1
T* b1
cnot bell26 b1
cnot bell24 b1
H bell24
measure bell24
cz bell24 c70
T* b1
cnot bell28 b1
T b1
cnot bell28 b1
H bell28
measure bell28
cz bell28 c61
cnot bell26 b1
H bell26
measure bell26
cz bell26 c71
H b1
S e30
H bell30
cnot bell30 bell31
cnot a0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 e30
T* e30
H bell32
cnot bell32 bell33
cnot e10 bell33
measure bell33
cnot bell33 bell32
cnot bell32 e30
T* e30
cnot bell30 e30
H bell34
cnot bell34 bell35
cnot a1 bell35
measure bell35
cnot bell35 bell34
cnot bell34 e30
T e30
cnot bell32 e30
H bell32
measure bell32
cz bell32 e10
T* e30
cnot bell34 e30
H e30
S e31
cnot bell30 e31
T* e31
H bell36
cnot bell36 bell37
cnot e11 bell37
measure bell37
cnot bell37 bell36
cnot bell36 e31
T* e31
cnot bell30 e31
H bell30
measure bell30
cz bell30 a0
cnot bell34 e31
T e31
cnot bell36 e31
H bell36
measure bell36
cz bell36 e11
T* e31
cnot bell34 e31
H bell34
measure bell34
cz bell34 a1
H e31
S b2
H bell38
cnot bell38 bell39
cnot b0 bell39
measure bell39
cnot bell39 bell38
cnot bell38 b2
T* b2
H bell40
cnot bell40 bell41
cnot e50 bell41
measure bell41
cnot bell41 bell40
cnot bell40 b2
T* b2
cnot bell38 b2
H bell42
cnot bell42 bell43
cnot b1 bell43
measure bell43
cnot bell43 bell42
cnot bell42 b2
T b2
cnot bell40 b2
H bell40
measure bell40
cz bell40 e50
T* b2
cnot bell42 b2
H b2
S b3
cnot bell38 b3
T* b3
H bell44
cnot bell44 bell45
cnot e51 bell45
measure bell45
cnot bell45 bell44
cnot bell44 b3
T* b3
cnot bell38 b3
H bell38
measure bell38
cz bell38 b0
cnot bell42 b3
T b3
cnot bell44 b3
H bell44
measure bell44
cz bell44 e51
T* b3
cnot bell42 b3
H bell42
measure bell42
cz bell42 b1
H b3
S e70
H bell46
cnot bell46 bell47
cnot b2 bell47
measure bell47
cnot bell47 bell46
cnot bell46 e70
T* e70
H bell48
cnot bell48 bell49
cnot e30 bell49
measure bell49
cnot bell49 bell48
cnot bell48 e70
T* e70
cnot bell46 e70
H bell50
cnot bell50 bell51
cnot b3 bell51
measure bell51
cnot bell51 bell50
cnot bell50 e70
T e70
cnot bell48 e70
H bell48
measure bell48
cz bell48 e30
T* e70
cnot bell50 e70
H e70
S e71
cnot bell46 e71
T* e71
H bell52
cnot bell52 bell53
cnot e31 bell53
measure bell53
cnot bell53 bell52
cnot bell52 e71
T* e71
cnot bell46 e71
H bell46
measure bell46
cz bell46 b2
cnot bell50 e71
T e71
cnot bell52 e71
H bell52
measure bell52
cz bell52 e31
T* e71
cnot bell50 e71
H bell50
measure bell50
cz bell50 b3
H e71
S c10
cnot c00 c10
T c10
cnot c01 c10
cnot c00 c10
T c10
S c11
cnot bell0 c11
T* c11
cnot bell4 c11
cnot bell0 c11
H bell0
measure bell0
cz bell0 c00
T* c11
S c30
cnot bell6 c30
T c30
cnot c30 c21
cnot bell6 c21
T c21
S c31
cnot bell6 c31
T* c31
cnot c30 c31
cnot c21 c31
T* c31
S c50
cnot c40 c50
T c50
cnot c50 c41
cnot c40 c41
T c41
S c51
cnot c40 c51
T* c51
cnot c50 c51
cnot c41 c51
T* c51
S c70
cnot c60 c70
T c70
cnot c70 c61
cnot c60 c61
T c61
S c71
cnot c60 c71
T* c71
cnot c70 c71
cnot c61 c71
T* c71
S a0
H bell54
cnot bell54 bell55
cnot a0 bell55
measure bell55
cnot bell55 bell54
cnot bell54 e10
T e10
S a1
cnot e10 a1
cnot bell54 a1
T* a1
cnot bell54 e11
T e11
cnot e10 e11
cnot a1 e11
T* e11
S b2
cnot b2 e30
T e30
S b3
cnot e30 b3
cnot b2 b3
T* b3
cnot b2 e31
T e31
cnot e30 e31
cnot b3 e31
T* e31
S b0
cnot b0 e50
T e50
S b1
cnot e50 b1
cnot b0 b1
T* b1
cnot b0 e51
T e51
cnot e50 e51
cnot b1 e51
T* e51
cnot e10 a1
cnot e30 b3
cnot e50 b1
cnot c30 c21
cnot c50 c41
cnot c70 c61
cnot c60 c70
cnot c60 c61
cnot c61 c71
cnot c41 c51
cnot c40 c51
cnot c40 c50
cnot c40 c41
cnot bell6 c21
cnot c21 c31
cnot bell6 c30
H bell6
measure bell6
cz bell6 c20
cnot c01 c10
cnot bell4 c11
H bell4
measure bell4
cz bell4 c01
cnot b2 b3
cnot b1 e51
cnot b3 e31
cnot b2 e30
cnot bell54 a1
cnot b0 e51
cnot b0 e50
cnot a1 e11
cnot bell54 e10
H bell54
measure bell54
cz bell54 a0
cnot b0 b1
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
