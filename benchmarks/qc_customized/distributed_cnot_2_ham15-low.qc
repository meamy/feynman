# Hyperedge cut (ebits): 27

# Actual ebits used (Synthesis): 27
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/ham15-low.qc):
#   Qubits: 17
#   H: 46
#   T: 161
#   cnot: 236
#   Depth: 238
#   T depth: 85
# Result (45.107ms):
#   Qubits: 71
#   H: 92
#   S: 3
#   T: 113
#   cnot: 302
#   cz: 28
#   measure: 54
#   reset: 55
#   swap: 1
#   Depth: 319
#   T depth: 93


# Result Circuit
.v a b c d e f g h i j k l m n o 0 1 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell6 bell7 bell8 bell9
.i a b c d e f g h i j k l m n o
.o a b c d e f g h i j k l m n o
BEGIN 
H bell0
cnot bell0 bell1
cnot k bell1
measure bell1
cnot bell1 bell0
cnot bell0 a
cnot bell0 f
cnot k g
cnot bell0 h
H bell0
measure bell0
cz bell0 k
H bell2
cnot bell2 bell3
cnot m bell3
measure bell3
cnot bell3 bell2
cnot bell2 i
cnot m n
cnot n l
cnot l n
cnot i h
cnot i e
H i
T i
H bell4
cnot bell4 bell5
cnot l bell5
measure bell5
cnot bell5 bell4
cnot bell4 i
T* i
cnot bell2 i
T i
cnot bell4 i
H bell4
measure bell4
cz bell4 l
T* i
cnot bell2 i
H bell2
measure bell2
cz bell2 m
H i
T m
cnot l m
T* m
H bell6
cnot bell6 bell7
cnot o bell7
measure bell7
cnot bell7 bell6
cnot bell6 a
cnot i e
cnot o g
cnot i h
cnot bell6 i
H bell6
measure bell6
cz bell6 o
cnot o n
cnot l m
H bell8
cnot bell8 bell9
cnot m bell9
measure bell9
cnot bell9 bell8
cnot bell8 d
H bell8
measure bell8
cz bell8 m
H m
T m
cnot n m
T* m
cnot o m
T m
cnot n m
T* m
cnot o m
H m
T o
cnot n o
T* o
H bell10
cnot bell10 bell11
cnot m bell11
measure bell11
cnot bell11 bell10
cnot bell10 d
H bell10
measure bell10
cz bell10 m
cnot n o
cnot m n
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
T m
cnot m k
swap 0 1
H m
T m
cnot n m
T* m
cnot o m
T m
cnot n m
T* m
cnot o m
H m
H bell12
cnot bell12 bell13
cnot k bell13
measure bell13
cnot bell13 bell12
cnot bell12 e
cnot bell12 i
cnot bell12 j
H bell12
measure bell12
cz bell12 k
cnot m k
H bell14
cnot bell14 bell15
cnot k bell15
measure bell15
cnot bell15 bell14
cnot bell14 d
cnot k c
cnot bell14 b
H bell14
measure bell14
cz bell14 k
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
H k
T k
cnot 0 k
T* k
cnot o k
T k
cnot 0 k
T* k
cnot o k
H k
T 0
cnot o 0
T* 0
cnot o 0
H 0
T* 0
cnot 1 0
T 0
cnot n 0
T* 0
cnot 1 0
T 0
cnot n 0
H 1
T* 1
cnot l 1
T 1
cnot m 1
T* 1
cnot l 1
T 1
cnot m 1
H 1
H bell16
cnot bell16 bell17
cnot k bell17
measure bell17
cnot bell17 bell16
cnot bell16 b
cnot k c
cnot bell16 d
cnot bell16 e
cnot k g
cnot bell16 j
H bell16
measure bell16
cz bell16 k
cnot l k
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
H 0
T l
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
T* 0
cnot m 0
T 0
cnot n 0
T* 0
cnot m 0
T 0
cnot n 0
H bell18
cnot bell18 bell19
cnot k bell19
measure bell19
cnot bell19 bell18
cnot bell18 f
H bell18
measure bell18
cz bell18 k
H bell20
cnot bell20 bell21
cnot m bell21
measure bell21
cnot bell21 bell20
cnot bell20 h
H bell20
measure bell20
cz bell20 m
cnot n k
cnot l k
cnot l m
T 0
cnot m 0
T* 0
cnot n 0
T 0
cnot m 0
T* 0
cnot n 0
H 0
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
T* 0
cnot m 0
T 0
cnot n 0
T* 0
cnot m 0
T 0
cnot n 0
cnot n c
H bell22
cnot bell22 bell23
cnot n bell23
measure bell23
cnot bell23 bell22
cnot bell22 d
H bell24
cnot bell24 bell25
cnot l bell25
measure bell25
cnot bell25 bell24
cnot bell24 f
H bell24
measure bell24
cz bell24 l
cnot bell22 e
H bell22
measure bell22
cz bell22 n
cnot l m
H bell26
cnot bell26 bell27
cnot m bell27
measure bell27
cnot bell27 bell26
cnot bell26 j
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot l 0
T* 0
cnot m 0
H 0
S n
cnot m n
cnot l n
cnot o n
cnot m n
cnot l n
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
T* 0
cnot l 0
T 0
cnot m 0
T* 0
cnot l 0
T 0
cnot m 0
cnot n c
H bell28
cnot bell28 bell29
cnot n bell29
measure bell29
cnot bell29 bell28
cnot bell28 d
H bell28
measure bell28
cz bell28 n
cnot n k
H bell30
cnot bell30 bell31
cnot k bell31
measure bell31
cnot bell31 bell30
cnot bell30 i
cnot m c
cnot bell30 a
H bell30
measure bell30
cz bell30 k
cnot bell26 a
H bell26
measure bell26
cz bell26 m
H m
T m
cnot l m
T* m
cnot o m
T m
cnot l m
T* m
cnot o m
H m
cnot m c
cnot o g
H bell32
cnot bell32 bell33
cnot h bell33
measure bell33
cnot bell33 bell32
cnot m bell32
cnot o k
cnot o n
cnot k bell32
H bell34
cnot bell34 bell35
cnot bell32 bell35
measure bell35
cnot bell35 bell34
reset bell35
cnot h bell34
cnot bell34 h
H bell34
measure bell34
cz bell34 k
cz bell34 m
H bell32
measure bell32
cz bell32 h
H bell36
cnot bell36 bell37
cnot n bell37
measure bell37
cnot bell37 bell36
cnot bell36 e
H bell36
measure bell36
cz bell36 n
T 0
cnot l 0
T* 0
cnot m 0
T 0
cnot l 0
T* 0
cnot m 0
H 0
S* o
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
T* 0
cnot l 0
T 0
cnot m 0
T* 0
cnot l 0
T 0
cnot m 0
H 0
T l
cnot o g
cnot o k
cnot o l
cnot o m
H bell38
cnot bell38 bell39
cnot m bell39
measure bell39
cnot bell39 bell38
cnot bell38 e
cnot bell38 a
H bell38
measure bell38
cz bell38 m
H o
T o
cnot l o
T* o
cnot n o
T o
cnot l o
T* o
cnot n o
H o
T l
S n
cnot l n
T* n
cnot l m
cnot k g
H bell40
cnot bell40 bell41
cnot k bell41
measure bell41
cnot bell41 bell40
cnot bell40 j
H bell40
measure bell40
cz bell40 k
cnot o l
cnot o m
cnot l n
cnot l m
cnot n k
cnot k n
cnot n o
H bell42
cnot bell42 bell43
cnot j bell43
measure bell43
cnot bell43 bell42
cnot bell42 m
cnot j i
H bell44
cnot bell44 bell45
cnot i bell45
measure bell45
cnot bell45 bell44
cnot bell44 m
cnot bell44 l
H bell44
measure bell44
cz bell44 i
cnot i h
H bell46
cnot bell46 bell47
cnot h bell47
measure bell47
cnot bell47 bell46
cnot bell46 l
cnot bell42 n
H bell42
measure bell42
cz bell42 j
cnot bell46 k
cnot bell46 g
H bell46
measure bell46
cz bell46 h
H bell48
cnot bell48 bell49
cnot g bell49
measure bell49
cnot bell49 bell48
cnot bell48 j
H bell48
measure bell48
cz bell48 g
cnot j f
cnot f j
cnot f i
cnot i e
cnot e i
cnot g k
cnot e h
cnot h d
H bell50
cnot bell50 bell51
cnot d bell51
measure bell51
cnot bell51 bell50
cnot bell50 g
H bell50
measure bell50
cz bell50 d
cnot g c
cnot c g
H bell52
cnot bell52 bell53
cnot c bell53
measure bell53
cnot bell53 bell52
cnot bell52 f
H bell52
measure bell52
cz bell52 c
cnot f b
cnot b f
cnot d h
cnot b e
cnot e a
cnot a e
cnot a d
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
END
