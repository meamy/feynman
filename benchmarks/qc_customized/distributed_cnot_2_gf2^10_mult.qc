# Hyperedge cut (ebits): 21

# Actual ebits used (Synthesis): 21
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^10_mult.qc):
#   Qubits: 30
#   H: 38
#   T: 700
#   cnot: 609
#   Depth: 246
#   T depth: 119
# Result (87.386ms):
#   Qubits: 72
#   H: 80
#   S: 25
#   T: 410
#   Z: 6
#   cnot: 711
#   cz: 21
#   measure: 42
#   reset: 42
#   Depth: 334
#   T depth: 109


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell5 bell6 bell7 bell8 bell9
.i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c9
.o a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
BEGIN 
H c0
H c1
H c2
H c3
H c4
H c5
H c6
H c7
H c8
T c0
H bell0
cnot bell0 bell1
cnot a9 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
cnot b1 c0
T c0
cnot bell0 c0
T* c0
H bell2
cnot bell2 bell3
cnot a8 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
cnot b1 c0
T* c0
H bell4
cnot bell4 bell5
cnot b2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
T c0
cnot bell2 c0
T* c0
H bell6
cnot bell6 bell7
cnot a7 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
cnot bell4 c0
T* c0
H bell8
cnot bell8 bell9
cnot b3 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
T c0
cnot bell6 c0
T* c0
H bell10
cnot bell10 bell11
cnot a6 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
cnot bell8 c0
T* c0
H bell12
cnot bell12 bell13
cnot b4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
T c0
cnot bell10 c0
T* c0
H bell14
cnot bell14 bell15
cnot a5 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
cnot bell12 c0
T* c0
H bell16
cnot bell16 bell17
cnot b5 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
T c0
cnot bell14 c0
T* c0
H bell18
cnot bell18 bell19
cnot a4 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c0
cnot bell16 c0
T* c0
H bell20
cnot bell20 bell21
cnot b6 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c0
T c0
cnot bell18 c0
T* c0
H bell22
cnot bell22 bell23
cnot a3 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c0
cnot bell20 c0
T* c0
H bell24
cnot bell24 bell25
cnot b7 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c0
T c0
cnot bell22 c0
T* c0
cnot a2 c0
cnot bell24 c0
T* c0
H bell26
cnot bell26 bell27
cnot b8 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c0
T c0
cnot a2 c0
T* c0
cnot a1 c0
cnot bell26 c0
T* c0
H bell28
cnot bell28 bell29
cnot b9 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c0
T c0
cnot a1 c0
T* c0
cnot bell28 c0
H c0
cnot bell0 c1
T* c1
cnot bell4 c1
T c1
cnot bell0 c1
T* c1
cnot bell2 c1
cnot bell4 c1
T* c1
cnot bell8 c1
T c1
cnot bell2 c1
T* c1
cnot bell6 c1
cnot bell8 c1
T* c1
cnot bell12 c1
T c1
cnot bell6 c1
T* c1
cnot bell10 c1
cnot bell12 c1
T* c1
cnot bell16 c1
T c1
cnot bell10 c1
T* c1
cnot bell14 c1
cnot bell16 c1
T* c1
cnot bell20 c1
T c1
cnot bell14 c1
T* c1
cnot bell18 c1
cnot bell20 c1
T* c1
cnot bell24 c1
T c1
cnot bell18 c1
T* c1
cnot bell22 c1
cnot bell24 c1
T* c1
cnot bell26 c1
T c1
cnot bell22 c1
T* c1
cnot a2 c1
cnot bell26 c1
T* c1
cnot bell28 c1
T c1
cnot a2 c1
T* c1
cnot bell28 c1
H c1
T* c2
cnot bell0 c2
T* c2
cnot bell8 c2
T c2
cnot bell0 c2
T* c2
cnot bell2 c2
cnot bell8 c2
T* c2
cnot bell12 c2
T c2
cnot bell2 c2
T* c2
cnot bell6 c2
cnot bell12 c2
T* c2
cnot bell16 c2
T c2
cnot bell6 c2
T* c2
cnot bell10 c2
cnot bell16 c2
T* c2
cnot bell20 c2
T c2
cnot bell10 c2
T* c2
cnot bell14 c2
cnot bell20 c2
T* c2
cnot bell24 c2
T c2
cnot bell14 c2
T* c2
cnot bell18 c2
cnot bell24 c2
T* c2
cnot bell26 c2
T c2
cnot bell18 c2
T* c2
cnot bell22 c2
cnot bell26 c2
T* c2
cnot bell28 c2
T c2
cnot bell22 c2
T* c2
cnot bell28 c2
H c2
S* c3
cnot bell0 c3
T* c3
cnot bell12 c3
T c3
cnot bell0 c3
T* c3
cnot bell2 c3
cnot bell12 c3
T* c3
cnot bell16 c3
T c3
cnot bell2 c3
T* c3
cnot bell6 c3
cnot bell16 c3
T* c3
cnot bell20 c3
T c3
cnot bell6 c3
T* c3
cnot bell10 c3
cnot bell20 c3
T* c3
cnot bell24 c3
T c3
cnot bell10 c3
T* c3
cnot bell14 c3
cnot bell24 c3
T* c3
cnot bell26 c3
T c3
cnot bell14 c3
T* c3
cnot bell18 c3
cnot bell26 c3
T* c3
cnot bell28 c3
T c3
cnot bell18 c3
T* c3
cnot bell28 c3
H c3
T c4
Z c4
cnot bell0 c4
T* c4
cnot bell16 c4
T c4
cnot bell0 c4
T* c4
cnot bell2 c4
cnot bell16 c4
T* c4
cnot bell20 c4
T c4
cnot bell2 c4
T* c4
cnot bell6 c4
cnot bell20 c4
T* c4
cnot bell24 c4
T c4
cnot bell6 c4
T* c4
cnot bell10 c4
cnot bell24 c4
T* c4
cnot bell26 c4
T c4
cnot bell10 c4
T* c4
cnot bell14 c4
cnot bell26 c4
T* c4
cnot bell28 c4
T c4
cnot bell14 c4
T* c4
cnot bell28 c4
H c4
Z c5
cnot bell0 c5
T* c5
cnot bell20 c5
T c5
cnot bell0 c5
T* c5
cnot bell2 c5
cnot bell20 c5
T* c5
cnot bell24 c5
T c5
cnot bell2 c5
T* c5
cnot bell6 c5
cnot bell24 c5
T* c5
cnot bell26 c5
T c5
cnot bell6 c5
T* c5
cnot bell10 c5
cnot bell26 c5
T* c5
cnot bell28 c5
T c5
cnot bell10 c5
T* c5
cnot bell28 c5
H c5
T* c6
Z c6
cnot bell0 c6
T* c6
cnot bell24 c6
T c6
cnot bell0 c6
T* c6
cnot bell2 c6
cnot bell24 c6
T* c6
cnot bell26 c6
T c6
cnot bell2 c6
T* c6
cnot bell6 c6
cnot bell26 c6
T* c6
cnot bell28 c6
T c6
cnot bell6 c6
T* c6
cnot bell28 c6
H c6
S c7
cnot bell0 c7
T* c7
cnot bell26 c7
T c7
cnot bell0 c7
T* c7
cnot bell2 c7
cnot bell26 c7
T* c7
cnot bell28 c7
T c7
cnot bell2 c7
T* c7
cnot bell28 c7
H c7
T c8
cnot bell0 c8
T* c8
cnot bell28 c8
T c8
cnot bell0 c8
T* c8
cnot bell28 c8
H c8
cnot c7 c0
cnot c8 c1
cnot c6 c9
cnot c5 c8
cnot c4 c7
cnot c3 c6
cnot c2 c5
cnot c1 c4
cnot c0 c3
H c0
H c1
H c2
H c3
H c4
H c5
H c6
H c7
H c8
H c9
T c0
cnot a0 c0
T* c0
cnot b0 c0
T c0
cnot a0 c0
T* c0
cnot b0 c0
H c0
S c1
cnot a1 c1
T* c1
cnot b0 c1
T c1
cnot a1 c1
T* c1
cnot a0 c1
cnot b0 c1
T* c1
cnot b1 c1
T c1
cnot a0 c1
T* c1
cnot b1 c1
H c1
T* c2
Z c2
cnot a2 c2
T* c2
cnot b0 c2
T c2
cnot a2 c2
T* c2
cnot a1 c2
cnot b0 c2
T* c2
cnot b1 c2
T c2
cnot a1 c2
T* c2
cnot a0 c2
cnot b1 c2
T* c2
cnot bell4 c2
T c2
cnot a0 c2
T* c2
cnot bell4 c2
H c2
Z c3
cnot bell22 c3
T* c3
cnot b0 c3
T c3
cnot bell22 c3
T* c3
cnot a2 c3
cnot b0 c3
T* c3
cnot b1 c3
T c3
cnot a2 c3
T* c3
cnot a1 c3
cnot b1 c3
T* c3
cnot bell4 c3
T c3
cnot a1 c3
T* c3
cnot a0 c3
cnot bell4 c3
T* c3
cnot bell8 c3
T c3
cnot a0 c3
T* c3
cnot bell8 c3
H c3
T c4
Z c4
cnot bell18 c4
T* c4
cnot b0 c4
T c4
cnot bell18 c4
T* c4
cnot bell22 c4
cnot b0 c4
T* c4
cnot b1 c4
T c4
cnot bell22 c4
T* c4
cnot a2 c4
cnot b1 c4
T* c4
cnot bell4 c4
T c4
cnot a2 c4
T* c4
cnot a1 c4
cnot bell4 c4
T* c4
cnot bell8 c4
T c4
cnot a1 c4
T* c4
cnot a0 c4
cnot bell8 c4
T* c4
cnot bell12 c4
T c4
cnot a0 c4
T* c4
cnot bell12 c4
H c4
S* c5
cnot bell14 c5
T* c5
cnot b0 c5
T c5
cnot bell14 c5
T* c5
cnot bell18 c5
cnot b0 c5
T* c5
cnot b1 c5
T c5
cnot bell18 c5
T* c5
cnot bell22 c5
cnot b1 c5
T* c5
cnot bell4 c5
T c5
cnot bell22 c5
T* c5
cnot a2 c5
cnot bell4 c5
T* c5
cnot bell8 c5
T c5
cnot a2 c5
T* c5
cnot a1 c5
cnot bell8 c5
T* c5
cnot bell12 c5
T c5
cnot a1 c5
T* c5
cnot a0 c5
cnot bell12 c5
T* c5
cnot bell16 c5
T c5
cnot a0 c5
T* c5
cnot bell16 c5
H c5
T* c6
cnot bell10 c6
T* c6
cnot b0 c6
T c6
cnot bell10 c6
T* c6
cnot bell14 c6
cnot b0 c6
T* c6
cnot b1 c6
T c6
cnot bell14 c6
T* c6
cnot bell18 c6
cnot b1 c6
T* c6
cnot bell4 c6
T c6
cnot bell18 c6
T* c6
cnot bell22 c6
cnot bell4 c6
T* c6
cnot bell8 c6
T c6
cnot bell22 c6
T* c6
cnot a2 c6
cnot bell8 c6
T* c6
cnot bell12 c6
T c6
cnot a2 c6
T* c6
cnot a1 c6
cnot bell12 c6
T* c6
cnot bell16 c6
T c6
cnot a1 c6
T* c6
cnot a0 c6
cnot bell16 c6
T* c6
cnot bell20 c6
T c6
cnot a0 c6
T* c6
cnot bell20 c6
H c6
cnot bell6 c7
T* c7
cnot b0 c7
T c7
cnot bell6 c7
T* c7
cnot bell10 c7
cnot b0 c7
T* c7
cnot b1 c7
T c7
cnot bell10 c7
T* c7
cnot bell14 c7
cnot b1 c7
T* c7
cnot bell4 c7
T c7
cnot bell14 c7
T* c7
cnot bell18 c7
cnot bell4 c7
T* c7
cnot bell8 c7
T c7
cnot bell18 c7
T* c7
cnot bell22 c7
cnot bell8 c7
T* c7
cnot bell12 c7
T c7
cnot bell22 c7
T* c7
cnot a2 c7
cnot bell12 c7
T* c7
cnot bell16 c7
T c7
cnot a2 c7
T* c7
cnot a1 c7
cnot bell16 c7
T* c7
cnot bell20 c7
T c7
cnot a1 c7
T* c7
cnot a0 c7
cnot bell20 c7
T* c7
cnot bell24 c7
T c7
cnot a0 c7
T* c7
cnot bell24 c7
H c7
T c8
cnot bell2 c8
T* c8
cnot b0 c8
T c8
cnot bell2 c8
T* c8
cnot bell6 c8
cnot b0 c8
T* c8
cnot b1 c8
T c8
cnot bell6 c8
T* c8
cnot bell10 c8
cnot b1 c8
T* c8
cnot bell4 c8
T c8
cnot bell10 c8
T* c8
cnot bell14 c8
cnot bell4 c8
T* c8
cnot bell8 c8
T c8
cnot bell14 c8
T* c8
cnot bell18 c8
cnot bell8 c8
T* c8
cnot bell12 c8
T c8
cnot bell18 c8
T* c8
cnot bell22 c8
cnot bell12 c8
T* c8
cnot bell16 c8
T c8
cnot bell22 c8
T* c8
cnot a2 c8
cnot bell16 c8
T* c8
cnot bell20 c8
T c8
cnot a2 c8
T* c8
cnot a1 c8
cnot bell20 c8
T* c8
cnot bell24 c8
T c8
cnot a1 c8
T* c8
cnot a0 c8
cnot bell24 c8
T* c8
cnot bell26 c8
T c8
cnot a0 c8
T* c8
cnot bell26 c8
H c8
S c9
cnot bell0 c9
T* c9
cnot b0 c9
T c9
cnot bell0 c9
H bell0
measure bell0
cz bell0 a9
T* c9
cnot bell2 c9
cnot b0 c9
T* c9
cnot b1 c9
T c9
cnot bell2 c9
H bell2
measure bell2
cz bell2 a8
T* c9
cnot bell6 c9
cnot b1 c9
T* c9
cnot bell4 c9
T c9
cnot bell6 c9
H bell6
measure bell6
cz bell6 a7
T* c9
cnot bell10 c9
cnot bell4 c9
H bell4
measure bell4
cz bell4 b2
T* c9
cnot bell8 c9
T c9
cnot bell10 c9
H bell10
measure bell10
cz bell10 a6
T* c9
cnot bell14 c9
cnot bell8 c9
H bell8
measure bell8
cz bell8 b3
T* c9
cnot bell12 c9
T c9
cnot bell14 c9
H bell14
measure bell14
cz bell14 a5
T* c9
cnot bell18 c9
cnot bell12 c9
H bell12
measure bell12
cz bell12 b4
T* c9
cnot bell16 c9
T c9
cnot bell18 c9
H bell18
measure bell18
cz bell18 a4
T* c9
cnot bell22 c9
cnot bell16 c9
H bell16
measure bell16
cz bell16 b5
T* c9
cnot bell20 c9
T c9
cnot bell22 c9
H bell22
measure bell22
cz bell22 a3
T* c9
cnot a2 c9
cnot bell20 c9
H bell20
measure bell20
cz bell20 b6
T* c9
cnot bell24 c9
T c9
cnot a2 c9
T* c9
cnot a1 c9
cnot bell24 c9
H bell24
measure bell24
cz bell24 b7
T* c9
cnot bell26 c9
T c9
cnot a1 c9
T* c9
cnot a0 c9
cnot bell26 c9
H bell26
measure bell26
cz bell26 b8
T* c9
cnot bell28 c9
T c9
cnot a0 c9
T* c9
cnot bell28 c9
H bell28
measure bell28
cz bell28 b9
H c9
S a0
S a1
S b0
cnot a0 b0
T* b0
cnot a1 b0
cnot a0 b0
T* b0
S b1
cnot a0 b1
T* b1
cnot a1 b1
cnot a0 b1
T* b1
S a2
cnot b0 a2
cnot a1 a2
T* a2
cnot b1 a2
cnot b0 a2
T* a2
S b2
H bell30
cnot bell30 bell31
cnot a0 bell31
measure bell31
cnot bell31 bell30
cnot bell30 b2
T* b2
H bell32
cnot bell32 bell33
cnot a1 bell33
measure bell33
cnot bell33 bell32
cnot bell32 b2
cnot bell30 b2
T* b2
H bell34
cnot bell34 bell35
cnot b1 bell35
measure bell35
cnot bell35 bell34
cnot bell34 b2
H bell36
cnot bell36 bell37
cnot a2 bell37
measure bell37
cnot bell37 bell36
cnot bell36 b2
T* b2
S a3
H bell38
cnot bell38 bell39
cnot b0 bell39
measure bell39
cnot bell39 bell38
cnot bell38 a3
cnot bell32 a3
T* a3
cnot bell34 a3
cnot bell38 a3
T* a3
cnot b2 a3
cnot bell36 a3
T* a3
S b3
cnot bell30 b3
T* b3
cnot bell32 b3
cnot bell30 b3
T* b3
cnot bell34 b3
cnot bell36 b3
T* b3
cnot b2 b3
cnot a3 b3
T* b3
S a4
cnot bell38 a4
cnot bell32 a4
T* a4
cnot bell34 a4
cnot bell38 a4
T* a4
cnot b2 a4
cnot bell36 a4
T* a4
cnot b3 a4
cnot a3 a4
T* a4
S b4
cnot bell30 b4
T* b4
cnot bell32 b4
cnot bell30 b4
T* b4
cnot bell34 b4
cnot bell36 b4
T* b4
cnot b2 b4
cnot a3 b4
T* b4
cnot b3 b4
cnot a4 b4
T* b4
S a5
cnot bell38 a5
cnot bell32 a5
T* a5
cnot bell34 a5
cnot bell38 a5
T* a5
cnot b2 a5
cnot bell36 a5
T* a5
cnot b3 a5
cnot a3 a5
T* a5
cnot b4 a5
cnot a4 a5
T* a5
S b5
cnot bell30 b5
T* b5
cnot bell32 b5
cnot bell30 b5
T* b5
cnot bell34 b5
cnot bell36 b5
T* b5
cnot b2 b5
cnot a3 b5
T* b5
cnot b3 b5
cnot a4 b5
T* b5
cnot b4 b5
cnot a5 b5
T* b5
S a6
cnot bell38 a6
cnot bell32 a6
T* a6
cnot bell34 a6
cnot bell38 a6
T* a6
cnot b2 a6
cnot bell36 a6
T* a6
cnot b3 a6
cnot a3 a6
T* a6
cnot b4 a6
cnot a4 a6
T* a6
cnot b5 a6
cnot a5 a6
T* a6
S b6
cnot bell30 b6
T* b6
cnot bell32 b6
cnot bell30 b6
T* b6
cnot bell34 b6
cnot bell36 b6
T* b6
cnot b2 b6
cnot a3 b6
T* b6
cnot b3 b6
cnot a4 b6
T* b6
cnot b4 b6
cnot a5 b6
T* b6
cnot b5 b6
cnot a6 b6
T* b6
S a7
cnot bell38 a7
cnot bell32 a7
T* a7
cnot bell34 a7
cnot bell38 a7
T* a7
cnot b2 a7
cnot bell36 a7
T* a7
cnot b3 a7
cnot a3 a7
T* a7
cnot b4 a7
cnot a4 a7
T* a7
cnot b5 a7
cnot a5 a7
T* a7
cnot b6 a7
cnot a6 a7
T* a7
S b7
cnot bell30 b7
T* b7
cnot bell32 b7
cnot bell30 b7
T* b7
cnot bell34 b7
cnot bell36 b7
T* b7
cnot b2 b7
cnot a3 b7
T* b7
cnot b3 b7
cnot a4 b7
T* b7
cnot b4 b7
cnot a5 b7
T* b7
cnot b5 b7
cnot a6 b7
T* b7
cnot b6 b7
cnot a7 b7
T* b7
S a8
cnot bell38 a8
cnot bell32 a8
T* a8
cnot bell34 a8
cnot bell38 a8
T* a8
cnot b2 a8
cnot bell36 a8
T* a8
cnot b3 a8
cnot a3 a8
T* a8
cnot b4 a8
cnot a4 a8
T* a8
cnot b5 a8
cnot a5 a8
T* a8
cnot b6 a8
cnot a6 a8
T* a8
cnot b7 a8
cnot a7 a8
T* a8
S b8
cnot bell30 b8
T* b8
cnot bell32 b8
cnot bell30 b8
T* b8
cnot bell34 b8
cnot bell36 b8
T* b8
cnot b2 b8
cnot a3 b8
T* b8
cnot b3 b8
cnot a4 b8
T* b8
cnot b4 b8
cnot a5 b8
T* b8
cnot b5 b8
cnot a6 b8
T* b8
cnot b6 b8
cnot a7 b8
T* b8
cnot b7 b8
cnot a8 b8
T* b8
S a9
cnot bell38 a9
cnot bell32 a9
T* a9
cnot bell34 a9
cnot bell38 a9
H bell38
measure bell38
cz bell38 b0
T* a9
cnot b2 a9
cnot bell36 a9
T* a9
cnot b3 a9
cnot a3 a9
T* a9
cnot b4 a9
cnot a4 a9
T* a9
cnot b5 a9
cnot a5 a9
T* a9
cnot b6 a9
cnot a6 a9
T* a9
cnot b7 a9
cnot a7 a9
T* a9
cnot b8 a9
cnot a8 a9
T* a9
S b9
cnot bell30 b9
T* b9
cnot bell32 b9
H bell32
measure bell32
cz bell32 a1
cnot bell30 b9
H bell30
measure bell30
cz bell30 a0
T* b9
cnot bell34 b9
H bell34
measure bell34
cz bell34 b1
cnot bell36 b9
H bell36
measure bell36
cz bell36 a2
T* b9
cnot b2 b9
cnot a3 b9
T* b9
cnot b3 b9
cnot a4 b9
T* b9
cnot b4 b9
cnot a5 b9
T* b9
cnot b5 b9
cnot a6 b9
T* b9
cnot b6 b9
cnot a7 b9
T* b9
cnot b7 b9
cnot a8 b9
T* b9
cnot b8 b9
cnot a9 b9
T* b9
cnot b1 a2
cnot b2 a3
cnot b3 a4
cnot b4 a5
cnot b5 a6
cnot b6 a7
cnot b7 a8
cnot b8 a9
cnot a9 b9
cnot a7 a8
cnot a6 a8
cnot a6 a7
cnot a8 b9
cnot a8 b8
cnot a7 b7
cnot a6 b6
cnot a8 a9
cnot a4 a5
cnot a3 a5
cnot a3 a4
cnot a5 b9
cnot a5 b8
cnot a5 b7
cnot a5 b6
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a5 a9
cnot a5 a8
cnot a5 a7
cnot a5 a6
cnot a1 a2
H bell40
cnot bell40 bell41
cnot a2 bell41
measure bell41
cnot bell41 bell40
cnot bell40 b9
cnot bell40 b8
cnot bell40 b7
cnot bell40 b6
cnot bell40 b5
cnot bell40 b4
cnot bell40 b3
cnot bell40 b2
cnot a1 b1
cnot a1 b0
cnot bell40 a9
cnot bell40 a8
cnot bell40 a7
cnot bell40 a6
cnot bell40 a5
cnot bell40 a4
cnot bell40 a3
H bell40
measure bell40
cz bell40 a2
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
END
