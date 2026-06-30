# Hyperedge cut (ebits): 16

# Actual ebits used (Synthesis): 20
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/rc_adder_6.qc):
#   Qubits: 14
#   H: 22
#   T: 77
#   X: 8
#   cnot: 93
#   Depth: 93
#   T depth: 39
# Result (24.202ms):
#   Qubits: 54
#   H: 62
#   T: 47
#   cnot: 131
#   cz: 20
#   measure: 40
#   reset: 40
#   Depth: 134
#   T depth: 36


# Result Circuit
.v b0 a0 e b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell5 bell6 bell7 bell8 bell9
.i b0 a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z
.o b0 a0 e b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z
BEGIN 
H bell0
cnot bell0 bell1
cnot a5 bell1
measure bell1
cnot bell1 bell0
cnot bell0 b5
H bell0
measure bell0
cz bell0 a5
cnot a4 b4
cnot a3 b3
cnot a2 b2
H bell2
cnot bell2 bell3
cnot a1 bell3
measure bell3
cnot bell3 bell2
cnot bell2 e
H bell2
measure bell2
cz bell2 a1
cnot a1 b1
H e
T e
H bell4
cnot bell4 bell5
cnot a0 bell5
measure bell5
cnot bell5 bell4
cnot bell4 e
T* e
cnot b0 e
T e
cnot bell4 e
T* e
cnot b0 e
H e
H bell6
cnot bell6 bell7
cnot a2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 a1
H bell6
measure bell6
cz bell6 a2
H a1
T a1
cnot b1 a1
T* a1
H bell8
cnot bell8 bell9
cnot e bell9
measure bell9
cnot bell9 bell8
cnot bell8 a1
T a1
cnot b1 a1
T* a1
cnot bell8 a1
H a1
H bell10
cnot bell10 bell11
cnot a3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 a2
H bell10
measure bell10
cz bell10 a3
H a2
T a2
H bell12
cnot bell12 bell13
cnot a1 bell13
measure bell13
cnot bell13 bell12
cnot bell12 a2
T* a2
cnot b2 a2
T a2
cnot bell12 a2
T* a2
cnot b2 a2
H a2
H bell14
cnot bell14 bell15
cnot a4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 a3
H bell14
measure bell14
cz bell14 a4
H a3
T a3
H bell16
cnot bell16 bell17
cnot a2 bell17
measure bell17
cnot bell17 bell16
cnot bell16 a3
T* a3
cnot b3 a3
T a3
cnot bell16 a3
T* a3
cnot b3 a3
H a3
H bell18
cnot bell18 bell19
cnot a5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 a4
H bell18
measure bell18
cz bell18 a5
H a4
T a4
H bell20
cnot bell20 bell21
cnot a3 bell21
measure bell21
cnot bell21 bell20
cnot bell20 a4
T* a4
cnot b4 a4
T a4
cnot bell20 a4
T* a4
cnot b4 a4
H a4
H bell22
cnot bell22 bell23
cnot a5 bell23
measure bell23
cnot bell23 bell22
cnot bell22 z
H bell22
measure bell22
cz bell22 a5
H z
T z
H bell24
cnot bell24 bell25
cnot a4 bell25
measure bell25
cnot bell25 bell24
cnot bell24 z
T* z
cnot b5 z
T z
cnot bell24 z
H bell24
measure bell24
cz bell24 a4
T* z
cnot b5 z
H z
T a4
T b5
cnot bell8 b1
H bell26
cnot bell26 bell27
cnot a4 bell27
measure bell27
cnot bell27 bell26
cnot bell26 b5
H bell26
measure bell26
cz bell26 a4
cnot bell20 b4
cnot bell16 b3
cnot bell12 b2
H a4
T* a4
cnot bell20 a4
T a4
cnot b4 a4
T a4
cnot bell20 a4
H bell20
measure bell20
cz bell20 a3
T* a4
cnot b4 a4
H a4
H a3
T* a3
cnot bell16 a3
T a3
cnot b3 a3
T a3
cnot bell16 a3
H bell16
measure bell16
cz bell16 a2
T* a3
cnot b3 a3
H a3
H bell28
cnot bell28 bell29
cnot a5 bell29
measure bell29
cnot bell29 bell28
cnot bell28 a4
H bell28
measure bell28
cz bell28 a5
H a2
T* a2
cnot bell12 a2
T a2
cnot b2 a2
T a2
cnot bell12 a2
H bell12
measure bell12
cz bell12 a1
T* a2
cnot b2 a2
H a2
H bell30
cnot bell30 bell31
cnot a4 bell31
measure bell31
cnot bell31 bell30
cnot bell30 a3
H bell30
measure bell30
cz bell30 a4
H a1
T* a1
cnot b1 a1
T* a1
cnot bell8 a1
T a1
cnot b1 a1
T a1
cnot bell8 a1
H bell8
measure bell8
cz bell8 e
H a1
H bell32
cnot bell32 bell33
cnot a3 bell33
measure bell33
cnot bell33 bell32
cnot bell32 a2
H bell32
measure bell32
cz bell32 a3
H e
T* e
cnot bell4 e
T e
cnot b0 e
T* e
cnot bell4 e
T e
cnot b0 e
H e
cnot bell4 b0
H bell4
measure bell4
cz bell4 a0
T* b5
H bell34
cnot bell34 bell35
cnot a2 bell35
measure bell35
cnot bell35 bell34
cnot bell34 a1
H bell34
measure bell34
cz bell34 a2
H bell36
cnot bell36 bell37
cnot a5 bell37
measure bell37
cnot bell37 bell36
cnot bell36 b5
H bell36
measure bell36
cz bell36 a5
cnot a4 b4
cnot a3 b3
cnot a2 b2
H bell38
cnot bell38 bell39
cnot a1 bell39
measure bell39
cnot bell39 bell38
cnot bell38 e
H bell38
measure bell38
cz bell38 a1
cnot a1 b1
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
