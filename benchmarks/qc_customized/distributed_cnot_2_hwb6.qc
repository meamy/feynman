# Hyperedge cut (ebits): 20

# Actual ebits used (Synthesis): 20
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
# Result (15.985ms):
#   Qubits: 47
#   H: 66
#   S: 4
#   T: 81
#   X: 5
#   Z: 4
#   cnot: 174
#   cz: 22
#   measure: 40
#   reset: 41
#   swap: 1
#   Depth: 211
#   T depth: 65


# Result Circuit
.v a b c d e f 0 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell5 bell6 bell7 bell8 bell9
.i a b c d e f
.o a b c d e f
BEGIN 
cnot c a
H c
T c
cnot a c
T c
cnot b c
T* c
cnot a c
T* c
cnot b c
H c
T b
cnot a b
T b
H bell0
cnot bell0 bell1
cnot f bell1
measure bell1
cnot bell1 bell0
cnot bell0 d
H bell0
measure bell0
cz bell0 f
H bell2
cnot bell2 bell3
cnot e bell3
measure bell3
cnot bell3 bell2
cnot bell2 f
H bell2
measure bell2
cz bell2 e
cnot a b
H b
T b
cnot a b
T b
cnot c b
T* b
cnot a b
T* b
cnot c b
H b
H f
T f
cnot a f
T f
cnot c f
T* f
cnot a f
T* f
cnot c f
H bell4
cnot bell4 bell5
cnot b bell5
measure bell5
cnot bell5 bell4
cnot bell4 d
T f
cnot b f
T f
H bell6
cnot bell6 bell7
cnot d bell7
measure bell7
cnot bell7 bell6
cnot bell6 f
T* f
cnot b f
T* f
cnot bell6 f
H bell6
measure bell6
cz bell6 d
H f
T d
cnot bell4 d
T d
H bell8
cnot bell8 bell9
cnot f bell9
measure bell9
cnot bell9 bell8
cnot bell8 e
H bell8
measure bell8
cz bell8 f
cnot bell4 e
cnot bell4 d
H bell4
measure bell4
cz bell4 b
swap a b
H d
T d
H bell10
cnot bell10 bell11
cnot b bell11
measure bell11
cnot bell11 bell10
cnot bell10 d
T d
H bell12
cnot bell12 bell13
cnot c bell13
measure bell13
cnot bell13 bell12
cnot bell12 d
T* d
cnot bell10 d
H bell10
measure bell10
cz bell10 b
T* d
cnot bell12 d
H bell12
measure bell12
cz bell12 c
H d
T* c
Z c
cnot b c
T* c
Z c
cnot b c
cnot b f
H c
T c
H bell14
cnot bell14 bell15
cnot e bell15
measure bell15
cnot bell15 bell14
cnot bell14 c
T c
cnot f c
T* c
cnot bell14 c
T* c
cnot f c
H c
H 0
T 0
H bell16
cnot bell16 bell17
cnot c bell17
measure bell17
cnot bell17 bell16
cnot bell16 0
T* 0
cnot e 0
T* 0
cnot bell16 0
T 0
cnot e 0
H 0
Z b
X b
H b
T b
H bell18
cnot bell18 bell19
cnot 0 bell19
measure bell19
cnot bell19 bell18
cnot bell18 b
T* b
cnot f b
T b
cnot bell18 b
H bell18
measure bell18
cz bell18 0
T* b
cnot f b
H b
T 0
H bell20
cnot bell20 bell21
cnot f bell21
measure bell21
cnot bell21 bell20
cnot bell20 0
T* 0
cnot bell20 0
H bell20
measure bell20
cz bell20 f
H 0
T* 0
cnot bell16 0
T 0
cnot e 0
T 0
cnot bell16 0
H bell16
measure bell16
cz bell16 c
T* 0
cnot e 0
H 0
cnot bell14 c
S f
cnot bell14 f
T f
T* a
cnot f c
cnot bell14 f
H bell14
measure bell14
cz bell14 e
cnot f a
H bell22
cnot bell22 bell23
cnot a bell23
measure bell23
cnot bell23 bell22
cnot bell22 d
H bell22
measure bell22
cz bell22 a
H f
T f
cnot b f
T* f
cnot c f
T f
cnot b f
T* f
cnot c f
H bell24
cnot bell24 bell25
cnot d bell25
measure bell25
cnot bell25 bell24
cnot bell24 b
H bell24
measure bell24
cz bell24 d
cnot d e
H bell26
cnot bell26 bell27
cnot e bell27
measure bell27
cnot bell27 bell26
cnot bell26 a
T f
cnot c f
T* f
cnot bell26 f
T f
cnot c f
T* f
cnot bell26 f
H f
H bell28
cnot bell28 bell29
cnot b bell29
measure bell29
cnot bell29 bell28
cnot bell28 d
T d
H bell30
cnot bell30 bell31
cnot c bell31
measure bell31
cnot bell31 bell30
cnot bell30 d
T* d
cnot e d
cnot bell30 d
H bell30
measure bell30
cz bell30 c
cnot bell28 d
T* d
cnot f c
cnot e d
cnot bell26 f
X d
H d
T d
cnot bell28 d
T d
cnot e d
T* d
cnot bell28 d
H bell28
measure bell28
cz bell28 b
T* d
cnot e d
H d
cnot c f
T* f
cnot bell26 f
S f
cnot bell26 f
cnot c f
H f
T f
cnot a f
T f
H bell32
cnot bell32 bell33
cnot d bell33
measure bell33
cnot bell33 bell32
cnot bell32 f
T* f
cnot a f
T* f
cnot bell32 f
H f
T* a
cnot bell32 a
T a
cnot bell32 a
cnot a c
H a
T a
cnot b a
T a
cnot bell26 a
T* a
cnot b a
T* a
cnot bell26 a
H a
S* b
cnot bell26 b
S b
cnot bell32 c
H bell32
measure bell32
cz bell32 d
cnot bell26 b
H bell26
measure bell26
cz bell26 e
X b
H b
T b
cnot a b
T* b
cnot c b
T b
cnot a b
T* b
cnot c b
H b
T a
T c
cnot a c
T* c
T d
T* e
Z e
cnot b a
H bell34
cnot bell34 bell35
cnot f bell35
measure bell35
cnot bell35 bell34
cnot bell34 d
cnot bell34 e
H bell34
measure bell34
cz bell34 f
cnot d e
H bell36
cnot bell36 bell37
cnot e bell37
measure bell37
cnot bell37 bell36
cnot c bell36
cnot b bell36
cnot a bell36
H bell38
cnot bell38 bell39
cnot bell36 bell39
measure bell39
cnot bell39 bell38
reset bell39
cnot e bell38
cnot bell38 e
H bell38
measure bell38
cz bell38 a
cz bell38 b
cz bell38 c
H bell36
measure bell36
cz bell36 e
cnot a c
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
END
