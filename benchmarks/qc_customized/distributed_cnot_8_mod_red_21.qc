# Hyperedge cut (ebits): 15

# Actual ebits used (Synthesis): 26
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
# Result (21.119ms):
#   Qubits: 63
#   H: 82
#   S: 1
#   T: 73
#   cnot: 178
#   cz: 26
#   measure: 52
#   reset: 52
#   Depth: 226
#   T depth: 59


# Result Circuit
.v x0 x1 c1 x2 c2 x3 c3 x4 c4 d4 z bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell6 bell7 bell8 bell9
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
cnot x2 c2
T c2
cnot bell0 c2
H bell0
measure bell0
cz bell0 x1
T* c2
cnot x2 c2
H c2
H c3
T c3
H bell2
cnot bell2 bell3
cnot c2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c3
T c3
H bell4
cnot bell4 bell5
cnot x3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c3
T c3
cnot bell2 c3
H bell2
measure bell2
cz bell2 c2
T c3
cnot bell4 c3
H bell4
measure bell4
cz bell4 x3
H c3
H d4
T d4
H bell6
cnot bell6 bell7
cnot c3 bell7
measure bell7
cnot bell7 bell6
cnot bell6 d4
T d4
H bell8
cnot bell8 bell9
cnot x4 bell9
measure bell9
cnot bell9 bell8
cnot bell8 d4
T* d4
cnot bell6 d4
H bell6
measure bell6
cz bell6 c3
T* d4
cnot bell8 d4
H bell8
measure bell8
cz bell8 x4
H d4
T* c3
cnot x4 c3
T c3
cnot x4 c3
H c3
H c4
T c4
H bell10
cnot bell10 bell11
cnot d4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c4
T* c4
H bell12
cnot bell12 bell13
cnot z bell13
measure bell13
cnot bell13 bell12
cnot bell12 c4
T c4
cnot bell10 c4
T* c4
cnot bell12 c4
H c4
H bell14
cnot bell14 bell15
cnot c3 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c2
T* c2
H bell16
cnot bell16 bell17
cnot x3 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c2
T* c2
cnot bell14 c2
H bell14
measure bell14
cz bell14 c3
cnot bell16 c2
H bell16
measure bell16
cz bell16 x3
H c2
H c1
T c1
H bell18
cnot bell18 bell19
cnot x0 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c1
H bell20
cnot bell20 bell21
cnot c4 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c1
T* c1
cnot x1 c1
cnot bell20 c1
T c1
cnot bell18 c1
H bell18
measure bell18
cz bell18 x0
cnot bell20 c1
H bell20
measure bell20
cz bell20 c4
T* c1
H bell22
cnot bell22 bell23
cnot c4 bell23
measure bell23
cnot bell23 bell22
cnot bell22 x3
H bell22
measure bell22
cz bell22 c4
H bell24
cnot bell24 bell25
cnot c4 bell25
measure bell25
cnot bell25 bell24
cnot bell24 x1
H bell24
measure bell24
cz bell24 c4
H bell26
cnot bell26 bell27
cnot c4 bell27
measure bell27
cnot bell27 bell26
cnot bell26 x0
H bell26
measure bell26
cz bell26 c4
cnot x1 c1
H c1
H bell28
cnot bell28 bell29
cnot c1 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c2
T c2
cnot x2 c2
T* c2
cnot bell28 c2
H bell30
cnot bell30 bell31
cnot x1 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c2
H bell32
cnot bell32 bell33
cnot c4 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c2
T* c2
cnot x2 c2
T c2
cnot bell32 c2
H bell32
measure bell32
cz bell32 c4
cnot bell30 c2
H c2
H bell34
cnot bell34 bell35
cnot c2 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c3
T c3
H bell36
cnot bell36 bell37
cnot x3 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c3
T* c3
cnot bell34 c3
T* c3
H bell38
cnot bell38 bell39
cnot c4 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c3
T* c3
cnot bell36 c3
cnot bell38 c3
H c3
T x4
H x4
T x4
cnot c3 x4
T x4
cnot bell38 x4
T* x4
cnot c3 x4
T* x4
cnot bell38 x4
H x4
T* c3
cnot bell38 c3
T c3
cnot bell38 c3
H bell38
measure bell38
cz bell38 c4
H c3
T* c3
cnot bell34 c3
T* c3
cnot bell36 c3
T c3
cnot bell34 c3
H bell34
measure bell34
cz bell34 c2
T c3
cnot bell36 c3
H bell36
measure bell36
cz bell36 x3
H c3
H bell40
cnot bell40 bell41
cnot c2 bell41
measure bell41
cnot bell41 bell40
cnot bell40 x3
H bell42
cnot bell42 bell43
cnot c4 bell43
measure bell43
cnot bell43 bell42
cnot bell42 x3
cnot bell40 x3
cnot bell42 x3
H x3
T* x3
cnot bell40 x3
T x3
cnot bell42 x3
T* x3
cnot bell40 x3
H bell40
measure bell40
cz bell40 c2
T x3
cnot bell42 x3
H bell42
measure bell42
cz bell42 c4
H x3
T* c2
H bell44
cnot bell44 bell45
cnot c4 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c2
T c2
cnot bell44 c2
H c2
T* c2
cnot bell28 c2
T* c2
cnot x2 c2
T c2
cnot bell28 c2
T c2
cnot x2 c2
H c2
cnot bell28 x2
cnot bell30 x2
cnot bell44 x2
cnot bell28 x2
cnot bell30 x2
H bell30
measure bell30
cz bell30 x1
cnot bell44 x2
H x2
T* x2
cnot bell28 x2
T* x2
cnot bell44 x2
T x2
cnot bell28 x2
H bell28
measure bell28
cz bell28 c1
T x2
cnot bell44 x2
H bell44
measure bell44
cz bell44 c4
H x2
T c1
H bell46
cnot bell46 bell47
cnot c4 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c1
T* c1
cnot bell46 c1
H c1
T* c1
H bell48
cnot bell48 bell49
cnot x0 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c1
T c1
cnot x1 c1
T* c1
cnot bell48 c1
T c1
cnot x1 c1
H c1
cnot bell46 x1
cnot bell48 x1
cnot bell46 x1
cnot bell48 x1
H x1
T* x1
cnot bell46 x1
T x1
cnot bell48 x1
T x1
cnot bell46 x1
H bell46
measure bell46
cz bell46 c4
T* x1
cnot bell48 x1
H bell48
measure bell48
cz bell48 x0
H x1
S* c4
H bell50
cnot bell50 bell51
cnot x0 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c4
T* c4
cnot bell50 c4
H bell50
measure bell50
cz bell50 x0
H c4
T* c4
cnot bell10 c4
T c4
cnot bell12 c4
T* c4
cnot bell10 c4
H bell10
measure bell10
cz bell10 d4
T c4
cnot bell12 c4
H bell12
measure bell12
cz bell12 z
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
END
