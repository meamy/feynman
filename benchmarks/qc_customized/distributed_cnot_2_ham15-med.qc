# Hyperedge cut (ebits): 24

# Actual ebits used (Synthesis): 24
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/ham15-med.qc):
#   Qubits: 17
#   H: 164
#   T: 574
#   cnot: 534
#   Depth: 667
#   T depth: 291
# Result (105.603ms):
#   Qubits: 65
#   H: 146
#   S: 33
#   T: 372
#   Z: 7
#   cnot: 523
#   cz: 24
#   measure: 48
#   reset: 48
#   swap: 1
#   Depth: 855
#   T depth: 282


# Result Circuit
.v a b c d e f g h i j k l m n o 0 1 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell5 bell6 bell7 bell8 bell9
.i a b c d e f g h i j k l m n o
.o a b c d e f g h i j k l m n o
BEGIN 
cnot o j
cnot n o
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H e
T e
H bell0
cnot bell0 bell1
cnot 0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 e
T* e
H bell2
cnot bell2 bell3
cnot o bell3
measure bell3
cnot bell3 bell2
cnot bell2 e
T e
cnot bell0 e
H bell0
measure bell0
cz bell0 0
T* e
cnot bell2 e
H bell2
measure bell2
cz bell2 o
H e
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
S l
cnot m l
S* l
T o
cnot o l
cnot m l
H o
T o
cnot m o
T* o
cnot n o
T o
cnot m o
T* o
cnot n o
H o
T* n
Z n
cnot m n
T* n
cnot m n
H n
T n
cnot l n
T* n
cnot o n
T n
cnot l n
T* n
cnot o n
H n
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H b
T b
H bell4
cnot bell4 bell5
cnot 0 bell5
measure bell5
cnot bell5 bell4
cnot bell4 b
T* b
H bell6
cnot bell6 bell7
cnot o bell7
measure bell7
cnot bell7 bell6
cnot bell6 b
T b
cnot bell4 b
H bell4
measure bell4
cz bell4 0
T* b
cnot bell6 b
H bell6
measure bell6
cz bell6 o
H b
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
cnot o k
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot l 0
T* 0
cnot m 0
H 0
S o
cnot l o
T* o
cnot l o
H o
T o
cnot 0 o
T* o
cnot n o
T o
cnot 0 o
T* o
cnot n o
H o
T 0
cnot n 0
T* 0
cnot n 0
H 0
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot l 0
T* 0
cnot m 0
H j
T j
cnot l j
T* j
cnot o j
T j
cnot l j
T* j
cnot o j
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H f
T f
H bell8
cnot bell8 bell9
cnot 0 bell9
measure bell9
cnot bell9 bell8
cnot bell8 f
T* f
H bell10
cnot bell10 bell11
cnot o bell11
measure bell11
cnot bell11 bell10
cnot bell10 f
T f
cnot bell8 f
H bell8
measure bell8
cz bell8 0
T* f
cnot bell10 f
H f
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H a
T a
cnot m a
T* a
cnot o a
T a
cnot m a
T* a
cnot o a
T a
cnot n a
T* a
cnot o a
T a
cnot n a
T* a
cnot o a
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
T a
cnot 0 a
T* a
cnot o a
T a
cnot 0 a
T* a
cnot o a
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
cnot o m
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H d
T d
H bell12
cnot bell12 bell13
cnot 0 bell13
measure bell13
cnot bell13 bell12
cnot bell12 d
T* d
cnot bell10 d
T d
cnot bell12 d
H bell12
measure bell12
cz bell12 0
T* d
cnot bell10 d
H d
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
T j
cnot m j
T* j
cnot o j
T j
cnot m j
T* j
cnot o j
H c
T c
H bell14
cnot bell14 bell15
cnot m bell15
measure bell15
cnot bell15 bell14
cnot bell14 c
T* c
cnot bell10 c
T c
cnot bell14 c
H bell14
measure bell14
cz bell14 m
T* c
cnot bell10 c
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
T c
H bell16
cnot bell16 bell17
cnot 0 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c
T* c
cnot bell10 c
T c
cnot bell16 c
H bell16
measure bell16
cz bell16 0
T* c
cnot bell10 c
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot l 0
T* 0
cnot m 0
H 0
Z n
cnot o n
T* n
cnot o n
H n
T n
cnot 0 n
T* n
cnot o n
T n
cnot 0 n
T* n
cnot o n
H n
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
H 0
T c
H bell18
cnot bell18 bell19
cnot 0 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c
T* c
cnot bell10 c
T c
cnot bell18 c
H bell18
measure bell18
cz bell18 0
T* c
cnot bell10 c
H c
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
H 0
cnot m l
S l
cnot o l
cnot m l
T* l
cnot o l
H l
T l
cnot 0 l
T* l
cnot o l
T l
cnot 0 l
T* l
cnot o l
H l
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
T a
cnot l a
T* a
cnot o a
T a
cnot l a
T* a
cnot o a
H a
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H g
T g
H bell20
cnot bell20 bell21
cnot 0 bell21
measure bell21
cnot bell21 bell20
cnot bell20 g
T* g
cnot bell10 g
T g
cnot bell20 g
H bell20
measure bell20
cz bell20 0
T* g
cnot bell10 g
H g
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
S* n
cnot m n
Z n
cnot m n
H n
T n
cnot l n
T* n
cnot o n
T n
cnot l n
T* n
cnot o n
H n
Z l
cnot m l
S* l
cnot o l
cnot m l
S* l
cnot o l
H l
T l
cnot n l
T* l
cnot o l
T l
cnot n l
T* l
cnot o l
H l
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H h
T h
H bell22
cnot bell22 bell23
cnot 0 bell23
measure bell23
cnot bell23 bell22
cnot bell22 h
T* h
cnot bell10 h
T h
cnot bell22 h
H bell22
measure bell22
cz bell22 0
T* h
cnot bell10 h
H bell10
measure bell10
cz bell10 o
H h
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
T 0
cnot l 0
T* 0
cnot n 0
T 0
cnot l 0
T* 0
cnot n 0
H 0
T* m
cnot l m
S* m
cnot o m
cnot l m
S m
cnot o m
H m
T m
cnot 0 m
T* m
cnot o m
T m
cnot 0 m
T* m
cnot o m
H m
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot l 0
T* 0
cnot n 0
T 0
cnot l 0
T* 0
cnot n 0
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
T j
cnot 0 j
T* j
cnot o j
T j
cnot 0 j
T* j
cnot o j
H j
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H k
T k
cnot 0 k
T* k
cnot o k
T k
cnot 0 k
T* k
cnot o k
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
Z o
cnot n o
T* o
cnot n o
H o
T o
cnot l o
T* o
cnot m o
T o
cnot l o
T* o
cnot m o
H o
T k
cnot l k
T* k
cnot n k
T k
cnot l k
T* k
cnot n k
H k
cnot o n
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
H i
T i
H bell24
cnot bell24 bell25
cnot 0 bell25
measure bell25
cnot bell25 bell24
cnot bell24 i
T* i
H bell26
cnot bell26 bell27
cnot o bell27
measure bell27
cnot bell27 bell26
cnot bell26 i
T i
cnot bell24 i
H bell24
measure bell24
cz bell24 0
T* i
cnot bell26 i
H bell26
measure bell26
cz bell26 o
H i
T 0
cnot o 0
T* 0
cnot o 0
H 0
T 0
cnot 1 0
T* 0
cnot n 0
T 0
cnot 1 0
T* 0
cnot n 0
H 0
S 1
cnot n 1
S* 1
cnot n 1
H 1
T 1
cnot l 1
T* 1
cnot m 1
T 1
cnot l 1
T* 1
cnot m 1
H 1
Z l
S n
T o
cnot n o
S o
cnot l o
T o
Z o
T* m
cnot l m
T m
cnot k j
cnot o l
cnot n o
cnot o m
swap m n
cnot l n
cnot k n
cnot k o
cnot j m
H bell28
cnot bell28 bell29
cnot m bell29
measure bell29
cnot bell29 bell28
cnot bell28 i
H bell28
measure bell28
cz bell28 m
H bell30
cnot bell30 bell31
cnot i bell31
measure bell31
cnot bell31 bell30
cnot bell30 m
cnot bell30 l
H bell30
measure bell30
cz bell30 i
H bell32
cnot bell32 bell33
cnot l bell33
measure bell33
cnot bell33 bell32
cnot bell32 h
H bell32
measure bell32
cz bell32 l
H bell34
cnot bell34 bell35
cnot h bell35
measure bell35
cnot bell35 bell34
cnot bell34 l
cnot j n
cnot bell34 k
H bell34
measure bell34
cz bell34 h
H bell36
cnot bell36 bell37
cnot k bell37
measure bell37
cnot bell37 bell36
cnot bell36 g
H bell36
measure bell36
cz bell36 k
H bell38
cnot bell38 bell39
cnot g bell39
measure bell39
cnot bell39 bell38
cnot bell38 j
H bell40
cnot bell40 bell41
cnot j bell41
measure bell41
cnot bell41 bell40
cnot bell40 f
H bell40
measure bell40
cz bell40 j
H bell42
cnot bell42 bell43
cnot f bell43
measure bell43
cnot bell43 bell42
cnot bell42 j
H bell42
measure bell42
cz bell42 f
cnot f i
cnot i e
cnot e i
cnot bell38 k
H bell38
measure bell38
cz bell38 g
cnot e h
cnot h d
cnot d g
cnot g c
cnot c g
cnot c f
cnot f b
cnot b f
cnot d h
cnot b e
H bell44
cnot bell44 bell45
cnot e bell45
measure bell45
cnot bell45 bell44
cnot bell44 a
H bell44
measure bell44
cz bell44 e
H bell46
cnot bell46 bell47
cnot a bell47
measure bell47
cnot bell47 bell46
cnot bell46 e
cnot bell46 d
H bell46
measure bell46
cz bell46 a
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
END
