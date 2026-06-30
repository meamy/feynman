# Hyperedge cut (ebits): 36

# Actual ebits used (Synthesis): 36
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^16_mult.qc):
#   Qubits: 48
#   H: 62
#   T: 1792
#   cnot: 1581
#   Depth: 415
#   T depth: 197
# Result (411.178ms):
#   Qubits: 120
#   H: 134
#   S: 8
#   T: 1040
#   Z: 12
#   cnot: 1799
#   cz: 36
#   measure: 72
#   reset: 72
#   swap: 1
#   Depth: 1500
#   T depth: 585


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell8 bell9
.i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
.o c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
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
H c9
H c10
H c11
H c12
H c13
H c14
T* c0
H bell0
cnot bell0 bell1
cnot a15 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
H bell2
cnot bell2 bell3
cnot b1 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
T c0
cnot bell0 c0
T* c0
H bell4
cnot bell4 bell5
cnot a6 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
cnot bell2 c0
T* c0
cnot b10 c0
T c0
cnot bell4 c0
T* c0
H bell6
cnot bell6 bell7
cnot a5 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
cnot b10 c0
T* c0
cnot b11 c0
T c0
cnot bell6 c0
T* c0
H bell8
cnot bell8 bell9
cnot a4 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
cnot b11 c0
T* c0
cnot b12 c0
T c0
cnot bell8 c0
T* c0
H bell10
cnot bell10 bell11
cnot a3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
cnot b12 c0
T* c0
H bell12
cnot bell12 bell13
cnot b13 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
T c0
cnot bell10 c0
T* c0
H bell14
cnot bell14 bell15
cnot a2 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
cnot bell12 c0
T* c0
H bell16
cnot bell16 bell17
cnot b14 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
T c0
cnot bell14 c0
T* c0
cnot a1 c0
cnot bell16 c0
T* c0
H bell18
cnot bell18 bell19
cnot b15 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c0
T c0
cnot a1 c0
T* c0
H bell20
cnot bell20 bell21
cnot a14 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c0
cnot bell18 c0
T* c0
H bell22
cnot bell22 bell23
cnot b2 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c0
T c0
cnot bell20 c0
T* c0
cnot a13 c0
cnot bell22 c0
T* c0
H bell24
cnot bell24 bell25
cnot b3 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c0
T c0
cnot a13 c0
T* c0
cnot a12 c0
cnot bell24 c0
T* c0
H bell26
cnot bell26 bell27
cnot b4 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c0
T c0
cnot a12 c0
T* c0
cnot a11 c0
cnot bell26 c0
T* c0
H bell28
cnot bell28 bell29
cnot b5 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c0
T c0
cnot a11 c0
T* c0
H bell30
cnot bell30 bell31
cnot a10 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c0
cnot bell28 c0
T* c0
H bell32
cnot bell32 bell33
cnot b6 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c0
T c0
cnot bell30 c0
T* c0
H bell34
cnot bell34 bell35
cnot a9 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c0
cnot bell32 c0
T* c0
H bell36
cnot bell36 bell37
cnot b7 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c0
T c0
cnot bell34 c0
T* c0
H bell38
cnot bell38 bell39
cnot a8 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c0
cnot bell36 c0
T* c0
H bell40
cnot bell40 bell41
cnot b8 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c0
T c0
cnot bell38 c0
T* c0
H bell42
cnot bell42 bell43
cnot a7 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c0
cnot bell40 c0
T* c0
H bell44
cnot bell44 bell45
cnot b9 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c0
T c0
cnot bell42 c0
T* c0
cnot bell44 c0
H c0
S* c1
cnot bell42 c1
T* c1
cnot b10 c1
T c1
cnot bell42 c1
T* c1
cnot bell4 c1
cnot b10 c1
T* c1
cnot b11 c1
T c1
cnot bell4 c1
T* c1
cnot bell6 c1
cnot b11 c1
T* c1
cnot b12 c1
T c1
cnot bell6 c1
T* c1
cnot bell8 c1
cnot b12 c1
T* c1
cnot bell12 c1
T c1
cnot bell8 c1
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
cnot bell18 c1
T c1
cnot bell14 c1
T* c1
cnot bell0 c1
cnot bell18 c1
T* c1
cnot bell22 c1
T c1
cnot bell0 c1
T* c1
cnot bell20 c1
cnot bell22 c1
T* c1
cnot bell24 c1
T c1
cnot bell20 c1
T* c1
cnot a13 c1
cnot bell24 c1
T* c1
cnot bell26 c1
T c1
cnot a13 c1
T* c1
cnot a12 c1
cnot bell26 c1
T* c1
cnot bell28 c1
T c1
cnot a12 c1
T* c1
cnot a11 c1
cnot bell28 c1
T* c1
cnot bell32 c1
T c1
cnot a11 c1
T* c1
cnot bell30 c1
cnot bell32 c1
T* c1
cnot bell36 c1
T c1
cnot bell30 c1
T* c1
cnot bell34 c1
cnot bell36 c1
T* c1
cnot bell40 c1
T c1
cnot bell34 c1
T* c1
cnot bell38 c1
cnot bell40 c1
T* c1
cnot bell44 c1
T c1
cnot bell38 c1
T* c1
cnot bell44 c1
H c1
T c2
Z c2
cnot bell38 c2
T* c2
cnot b10 c2
T c2
cnot bell38 c2
T* c2
cnot bell42 c2
cnot b10 c2
T* c2
cnot b11 c2
T c2
cnot bell42 c2
T* c2
cnot bell4 c2
cnot b11 c2
T* c2
cnot b12 c2
T c2
cnot bell4 c2
T* c2
cnot bell6 c2
cnot b12 c2
T* c2
cnot bell12 c2
T c2
cnot bell6 c2
T* c2
cnot bell8 c2
cnot bell12 c2
T* c2
cnot bell16 c2
T c2
cnot bell8 c2
T* c2
cnot bell10 c2
cnot bell16 c2
T* c2
cnot bell18 c2
T c2
cnot bell10 c2
T* c2
cnot bell0 c2
cnot bell18 c2
T* c2
cnot bell24 c2
T c2
cnot bell0 c2
T* c2
cnot bell20 c2
cnot bell24 c2
T* c2
cnot bell26 c2
T c2
cnot bell20 c2
T* c2
cnot a13 c2
cnot bell26 c2
T* c2
cnot bell28 c2
T c2
cnot a13 c2
T* c2
cnot a12 c2
cnot bell28 c2
T* c2
cnot bell32 c2
T c2
cnot a12 c2
T* c2
cnot a11 c2
cnot bell32 c2
T* c2
cnot bell36 c2
T c2
cnot a11 c2
T* c2
cnot bell30 c2
cnot bell36 c2
T* c2
cnot bell40 c2
T c2
cnot bell30 c2
T* c2
cnot bell34 c2
cnot bell40 c2
T* c2
cnot bell44 c2
T c2
cnot bell34 c2
T* c2
cnot bell44 c2
H c2
Z c3
cnot bell34 c3
T* c3
cnot b10 c3
T c3
cnot bell34 c3
T* c3
cnot bell38 c3
cnot b10 c3
T* c3
cnot b11 c3
T c3
cnot bell38 c3
T* c3
cnot bell42 c3
cnot b11 c3
T* c3
cnot b12 c3
T c3
cnot bell42 c3
T* c3
cnot bell4 c3
cnot b12 c3
T* c3
cnot bell12 c3
T c3
cnot bell4 c3
T* c3
cnot bell6 c3
cnot bell12 c3
T* c3
cnot bell16 c3
T c3
cnot bell6 c3
T* c3
cnot bell8 c3
cnot bell16 c3
T* c3
cnot bell18 c3
T c3
cnot bell8 c3
T* c3
cnot bell0 c3
cnot bell18 c3
T* c3
cnot bell26 c3
T c3
cnot bell0 c3
T* c3
cnot bell20 c3
cnot bell26 c3
T* c3
cnot bell28 c3
T c3
cnot bell20 c3
T* c3
cnot a13 c3
cnot bell28 c3
T* c3
cnot bell32 c3
T c3
cnot a13 c3
T* c3
cnot a12 c3
cnot bell32 c3
T* c3
cnot bell36 c3
T c3
cnot a12 c3
T* c3
cnot a11 c3
cnot bell36 c3
T* c3
cnot bell40 c3
T c3
cnot a11 c3
T* c3
cnot bell30 c3
cnot bell40 c3
T* c3
cnot bell44 c3
T c3
cnot bell30 c3
T* c3
cnot bell44 c3
H c3
T* c4
Z c4
cnot bell30 c4
T* c4
cnot b10 c4
T c4
cnot bell30 c4
T* c4
cnot bell34 c4
cnot b10 c4
T* c4
cnot b11 c4
T c4
cnot bell34 c4
T* c4
cnot bell38 c4
cnot b11 c4
T* c4
cnot b12 c4
T c4
cnot bell38 c4
T* c4
cnot bell42 c4
cnot b12 c4
T* c4
cnot bell12 c4
T c4
cnot bell42 c4
T* c4
cnot bell4 c4
cnot bell12 c4
T* c4
cnot bell16 c4
T c4
cnot bell4 c4
T* c4
cnot bell6 c4
cnot bell16 c4
T* c4
cnot bell18 c4
T c4
cnot bell6 c4
T* c4
cnot bell0 c4
cnot bell18 c4
T* c4
cnot bell28 c4
T c4
cnot bell0 c4
T* c4
cnot bell20 c4
cnot bell28 c4
T* c4
cnot bell32 c4
T c4
cnot bell20 c4
T* c4
cnot a13 c4
cnot bell32 c4
T* c4
cnot bell36 c4
T c4
cnot a13 c4
T* c4
cnot a12 c4
cnot bell36 c4
T* c4
cnot bell40 c4
T c4
cnot a12 c4
T* c4
cnot a11 c4
cnot bell40 c4
T* c4
cnot bell44 c4
T c4
cnot a11 c4
T* c4
cnot bell44 c4
H c4
S c5
cnot a11 c5
T* c5
cnot b10 c5
T c5
cnot a11 c5
T* c5
cnot bell30 c5
cnot b10 c5
T* c5
cnot b11 c5
T c5
cnot bell30 c5
T* c5
cnot bell34 c5
cnot b11 c5
T* c5
cnot b12 c5
T c5
cnot bell34 c5
T* c5
cnot bell38 c5
cnot b12 c5
T* c5
cnot bell12 c5
T c5
cnot bell38 c5
T* c5
cnot bell42 c5
cnot bell12 c5
T* c5
cnot bell16 c5
T c5
cnot bell42 c5
T* c5
cnot bell4 c5
cnot bell16 c5
T* c5
cnot bell18 c5
T c5
cnot bell4 c5
T* c5
cnot bell0 c5
cnot bell18 c5
T* c5
cnot bell32 c5
T c5
cnot bell0 c5
T* c5
cnot bell20 c5
cnot bell32 c5
T* c5
cnot bell36 c5
T c5
cnot bell20 c5
T* c5
cnot a13 c5
cnot bell36 c5
T* c5
cnot bell40 c5
T c5
cnot a13 c5
T* c5
cnot a12 c5
cnot bell40 c5
T* c5
cnot bell44 c5
T c5
cnot a12 c5
T* c5
cnot bell44 c5
H c5
T c6
cnot a12 c6
T* c6
cnot b10 c6
T c6
cnot a12 c6
T* c6
cnot a11 c6
cnot b10 c6
T* c6
cnot b11 c6
T c6
cnot a11 c6
T* c6
cnot bell30 c6
cnot b11 c6
T* c6
cnot b12 c6
T c6
cnot bell30 c6
T* c6
cnot bell34 c6
cnot b12 c6
T* c6
cnot bell12 c6
T c6
cnot bell34 c6
T* c6
cnot bell38 c6
cnot bell12 c6
T* c6
cnot bell16 c6
T c6
cnot bell38 c6
T* c6
cnot bell42 c6
cnot bell16 c6
T* c6
cnot bell18 c6
T c6
cnot bell42 c6
T* c6
cnot bell0 c6
cnot bell18 c6
T* c6
cnot bell36 c6
T c6
cnot bell0 c6
T* c6
cnot bell20 c6
cnot bell36 c6
T* c6
cnot bell40 c6
T c6
cnot bell20 c6
T* c6
cnot a13 c6
cnot bell40 c6
T* c6
cnot bell44 c6
T c6
cnot a13 c6
T* c6
cnot bell44 c6
H c6
cnot a13 c7
T* c7
cnot b10 c7
T c7
cnot a13 c7
T* c7
cnot a12 c7
cnot b10 c7
T* c7
cnot b11 c7
T c7
cnot a12 c7
T* c7
cnot a11 c7
cnot b11 c7
T* c7
cnot b12 c7
T c7
cnot a11 c7
T* c7
cnot bell30 c7
cnot b12 c7
T* c7
cnot bell12 c7
T c7
cnot bell30 c7
T* c7
cnot bell34 c7
cnot bell12 c7
T* c7
cnot bell16 c7
T c7
cnot bell34 c7
T* c7
cnot bell38 c7
cnot bell16 c7
T* c7
cnot bell18 c7
T c7
cnot bell38 c7
T* c7
cnot bell0 c7
cnot bell18 c7
T* c7
cnot bell40 c7
T c7
cnot bell0 c7
T* c7
cnot bell20 c7
cnot bell40 c7
T* c7
cnot bell44 c7
T c7
cnot bell20 c7
T* c7
cnot bell44 c7
H c7
T* c8
cnot bell20 c8
T* c8
cnot b10 c8
T c8
cnot bell20 c8
T* c8
cnot a13 c8
cnot b10 c8
T* c8
cnot b11 c8
T c8
cnot a13 c8
T* c8
cnot a12 c8
cnot b11 c8
T* c8
cnot b12 c8
T c8
cnot a12 c8
T* c8
cnot a11 c8
cnot b12 c8
T* c8
cnot bell12 c8
T c8
cnot a11 c8
T* c8
cnot bell30 c8
cnot bell12 c8
T* c8
cnot bell16 c8
T c8
cnot bell30 c8
T* c8
cnot bell34 c8
cnot bell16 c8
T* c8
cnot bell18 c8
T c8
cnot bell34 c8
T* c8
cnot bell0 c8
cnot bell18 c8
T* c8
cnot bell44 c8
T c8
cnot bell0 c8
T* c8
cnot bell44 c8
H c8
S* c9
cnot bell0 c9
T* c9
cnot b10 c9
T c9
cnot bell0 c9
T* c9
cnot bell20 c9
cnot b10 c9
T* c9
cnot b11 c9
T c9
cnot bell20 c9
T* c9
cnot a13 c9
cnot b11 c9
T* c9
cnot b12 c9
T c9
cnot a13 c9
T* c9
cnot a12 c9
cnot b12 c9
T* c9
cnot bell12 c9
T c9
cnot a12 c9
T* c9
cnot a11 c9
cnot bell12 c9
T* c9
cnot bell16 c9
T c9
cnot a11 c9
T* c9
cnot bell30 c9
cnot bell16 c9
T* c9
cnot bell18 c9
T c9
cnot bell30 c9
T* c9
cnot bell18 c9
H c9
T c10
Z c10
cnot bell0 c10
T* c10
cnot b11 c10
T c10
cnot bell0 c10
T* c10
cnot bell20 c10
cnot b11 c10
T* c10
cnot b12 c10
T c10
cnot bell20 c10
T* c10
cnot a13 c10
cnot b12 c10
T* c10
cnot bell12 c10
T c10
cnot a13 c10
T* c10
cnot a12 c10
cnot bell12 c10
T* c10
cnot bell16 c10
T c10
cnot a12 c10
T* c10
cnot a11 c10
cnot bell16 c10
T* c10
cnot bell18 c10
T c10
cnot a11 c10
T* c10
cnot bell18 c10
H c10
Z c11
cnot bell0 c11
T* c11
cnot b12 c11
T c11
cnot bell0 c11
T* c11
cnot bell20 c11
cnot b12 c11
T* c11
cnot bell12 c11
T c11
cnot bell20 c11
T* c11
cnot a13 c11
cnot bell12 c11
T* c11
cnot bell16 c11
T c11
cnot a13 c11
T* c11
cnot a12 c11
cnot bell16 c11
T* c11
cnot bell18 c11
T c11
cnot a12 c11
T* c11
cnot bell18 c11
H c11
T* c12
Z c12
cnot bell0 c12
T* c12
cnot bell12 c12
T c12
cnot bell0 c12
T* c12
cnot bell20 c12
cnot bell12 c12
T* c12
cnot bell16 c12
T c12
cnot bell20 c12
T* c12
cnot a13 c12
cnot bell16 c12
T* c12
cnot bell18 c12
T c12
cnot a13 c12
T* c12
cnot bell18 c12
H c12
S c13
cnot bell0 c13
T* c13
cnot bell16 c13
T c13
cnot bell0 c13
T* c13
cnot bell20 c13
cnot bell16 c13
T* c13
cnot bell18 c13
T c13
cnot bell20 c13
T* c13
cnot bell18 c13
H c13
T c14
cnot bell0 c14
T* c14
cnot bell18 c14
T c14
cnot bell0 c14
T* c14
cnot bell18 c14
H c14
cnot c11 c0
cnot c13 c0
cnot c14 c0
cnot c12 c1
cnot c14 c1
cnot c5 c10
cnot c6 c11
cnot c7 c10
cnot c9 c11
cnot c8 c10
cnot c8 c11
cnot c2 c13
cnot c3 c14
cnot c5 c12
cnot c8 c12
cnot c9 c12
cnot c5 c3
cnot c6 c3
cnot c7 c2
cnot c9 c2
cnot c9 c3
cnot c7 c9
cnot c6 c8
cnot c5 c8
cnot c5 c7
cnot c4 c7
cnot c4 c6
cnot c6 c9
cnot c3 c5
cnot c8 c2
cnot c2 c5
cnot c8 c15
swap c15 c8
cnot c2 c7
cnot c2 c4
cnot c3 c14
cnot c14 c5
cnot c14 c3
cnot c2 c13
cnot c13 c5
cnot c13 c15
cnot c12 c15
cnot c12 c14
cnot c3 c8
cnot c13 c7
cnot c3 c6
cnot c13 c4
cnot c13 c2
cnot c11 c13
cnot c10 c13
cnot c1 c6
cnot c1 c4
cnot c1 c3
cnot c10 c15
cnot c11 c14
cnot c10 c12
cnot c0 c5
cnot c0 c3
cnot c0 c2
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
H c10
H c11
H c12
H c13
H c14
H c15
T c0
H bell46
cnot bell46 bell47
cnot a0 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c0
T* c0
cnot b0 c0
T c0
cnot bell46 c0
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
cnot bell46 c1
cnot b0 c1
T* c1
cnot bell2 c1
T c1
cnot bell46 c1
T* c1
cnot bell2 c1
H c1
T* c2
Z c2
cnot bell14 c2
T* c2
cnot b0 c2
T c2
cnot bell14 c2
T* c2
cnot a1 c2
cnot b0 c2
T* c2
cnot bell2 c2
T c2
cnot a1 c2
T* c2
cnot bell46 c2
cnot bell2 c2
T* c2
cnot bell22 c2
T c2
cnot bell46 c2
T* c2
cnot bell22 c2
H c2
Z c3
cnot bell10 c3
T* c3
cnot b0 c3
T c3
cnot bell10 c3
T* c3
cnot bell14 c3
cnot b0 c3
T* c3
cnot bell2 c3
T c3
cnot bell14 c3
T* c3
cnot a1 c3
cnot bell2 c3
T* c3
cnot bell22 c3
T c3
cnot a1 c3
T* c3
cnot bell46 c3
cnot bell22 c3
T* c3
cnot bell24 c3
T c3
cnot bell46 c3
T* c3
cnot bell24 c3
H c3
T c4
Z c4
cnot bell8 c4
T* c4
cnot b0 c4
T c4
cnot bell8 c4
T* c4
cnot bell10 c4
cnot b0 c4
T* c4
cnot bell2 c4
T c4
cnot bell10 c4
T* c4
cnot bell14 c4
cnot bell2 c4
T* c4
cnot bell22 c4
T c4
cnot bell14 c4
T* c4
cnot a1 c4
cnot bell22 c4
T* c4
cnot bell24 c4
T c4
cnot a1 c4
T* c4
cnot bell46 c4
cnot bell24 c4
T* c4
cnot bell26 c4
T c4
cnot bell46 c4
T* c4
cnot bell26 c4
H c4
S* c5
cnot bell6 c5
T* c5
cnot b0 c5
T c5
cnot bell6 c5
T* c5
cnot bell8 c5
cnot b0 c5
T* c5
cnot bell2 c5
T c5
cnot bell8 c5
T* c5
cnot bell10 c5
cnot bell2 c5
T* c5
cnot bell22 c5
T c5
cnot bell10 c5
T* c5
cnot bell14 c5
cnot bell22 c5
T* c5
cnot bell24 c5
T c5
cnot bell14 c5
T* c5
cnot a1 c5
cnot bell24 c5
T* c5
cnot bell26 c5
T c5
cnot a1 c5
T* c5
cnot bell46 c5
cnot bell26 c5
T* c5
cnot bell28 c5
T c5
cnot bell46 c5
T* c5
cnot bell28 c5
H c5
T* c6
cnot bell4 c6
T* c6
cnot b0 c6
T c6
cnot bell4 c6
T* c6
cnot bell6 c6
cnot b0 c6
T* c6
cnot bell2 c6
T c6
cnot bell6 c6
T* c6
cnot bell8 c6
cnot bell2 c6
T* c6
cnot bell22 c6
T c6
cnot bell8 c6
T* c6
cnot bell10 c6
cnot bell22 c6
T* c6
cnot bell24 c6
T c6
cnot bell10 c6
T* c6
cnot bell14 c6
cnot bell24 c6
T* c6
cnot bell26 c6
T c6
cnot bell14 c6
T* c6
cnot a1 c6
cnot bell26 c6
T* c6
cnot bell28 c6
T c6
cnot a1 c6
T* c6
cnot bell46 c6
cnot bell28 c6
T* c6
cnot bell32 c6
T c6
cnot bell46 c6
T* c6
cnot bell32 c6
H c6
cnot bell42 c7
T* c7
cnot b0 c7
T c7
cnot bell42 c7
T* c7
cnot bell4 c7
cnot b0 c7
T* c7
cnot bell2 c7
T c7
cnot bell4 c7
T* c7
cnot bell6 c7
cnot bell2 c7
T* c7
cnot bell22 c7
T c7
cnot bell6 c7
T* c7
cnot bell8 c7
cnot bell22 c7
T* c7
cnot bell24 c7
T c7
cnot bell8 c7
T* c7
cnot bell10 c7
cnot bell24 c7
T* c7
cnot bell26 c7
T c7
cnot bell10 c7
T* c7
cnot bell14 c7
cnot bell26 c7
T* c7
cnot bell28 c7
T c7
cnot bell14 c7
T* c7
cnot a1 c7
cnot bell28 c7
T* c7
cnot bell32 c7
T c7
cnot a1 c7
T* c7
cnot bell46 c7
cnot bell32 c7
T* c7
cnot bell36 c7
T c7
cnot bell46 c7
T* c7
cnot bell36 c7
H c7
T c8
cnot bell38 c8
T* c8
cnot b0 c8
T c8
cnot bell38 c8
T* c8
cnot bell42 c8
cnot b0 c8
T* c8
cnot bell2 c8
T c8
cnot bell42 c8
T* c8
cnot bell4 c8
cnot bell2 c8
T* c8
cnot bell22 c8
T c8
cnot bell4 c8
T* c8
cnot bell6 c8
cnot bell22 c8
T* c8
cnot bell24 c8
T c8
cnot bell6 c8
T* c8
cnot bell8 c8
cnot bell24 c8
T* c8
cnot bell26 c8
T c8
cnot bell8 c8
T* c8
cnot bell10 c8
cnot bell26 c8
T* c8
cnot bell28 c8
T c8
cnot bell10 c8
T* c8
cnot bell14 c8
cnot bell28 c8
T* c8
cnot bell32 c8
T c8
cnot bell14 c8
T* c8
cnot a1 c8
cnot bell32 c8
T* c8
cnot bell36 c8
T c8
cnot a1 c8
T* c8
cnot bell46 c8
cnot bell36 c8
T* c8
cnot bell40 c8
T c8
cnot bell46 c8
T* c8
cnot bell40 c8
H c8
S c9
cnot bell34 c9
T* c9
cnot b0 c9
T c9
cnot bell34 c9
T* c9
cnot bell38 c9
cnot b0 c9
T* c9
cnot bell2 c9
T c9
cnot bell38 c9
T* c9
cnot bell42 c9
cnot bell2 c9
T* c9
cnot bell22 c9
T c9
cnot bell42 c9
T* c9
cnot bell4 c9
cnot bell22 c9
T* c9
cnot bell24 c9
T c9
cnot bell4 c9
T* c9
cnot bell6 c9
cnot bell24 c9
T* c9
cnot bell26 c9
T c9
cnot bell6 c9
T* c9
cnot bell8 c9
cnot bell26 c9
T* c9
cnot bell28 c9
T c9
cnot bell8 c9
T* c9
cnot bell10 c9
cnot bell28 c9
T* c9
cnot bell32 c9
T c9
cnot bell10 c9
T* c9
cnot bell14 c9
cnot bell32 c9
T* c9
cnot bell36 c9
T c9
cnot bell14 c9
T* c9
cnot a1 c9
cnot bell36 c9
T* c9
cnot bell40 c9
T c9
cnot a1 c9
T* c9
cnot bell46 c9
cnot bell40 c9
T* c9
cnot bell44 c9
T c9
cnot bell46 c9
T* c9
cnot bell44 c9
H c9
T* c10
Z c10
cnot bell30 c10
T* c10
cnot b0 c10
T c10
cnot bell30 c10
T* c10
cnot bell34 c10
cnot b0 c10
T* c10
cnot bell2 c10
T c10
cnot bell34 c10
T* c10
cnot bell46 c10
cnot bell2 c10
T* c10
cnot b10 c10
T c10
cnot bell46 c10
T* c10
cnot bell38 c10
cnot b10 c10
T* c10
cnot bell22 c10
T c10
cnot bell38 c10
T* c10
cnot bell42 c10
cnot bell22 c10
T* c10
cnot bell24 c10
T c10
cnot bell42 c10
T* c10
cnot bell4 c10
cnot bell24 c10
T* c10
cnot bell26 c10
T c10
cnot bell4 c10
T* c10
cnot bell6 c10
cnot bell26 c10
T* c10
cnot bell28 c10
T c10
cnot bell6 c10
T* c10
cnot bell8 c10
cnot bell28 c10
T* c10
cnot bell32 c10
T c10
cnot bell8 c10
T* c10
cnot bell10 c10
cnot bell32 c10
T* c10
cnot bell36 c10
T c10
cnot bell10 c10
T* c10
cnot bell14 c10
cnot bell36 c10
T* c10
cnot bell40 c10
T c10
cnot bell14 c10
T* c10
cnot a1 c10
cnot bell40 c10
T* c10
cnot bell44 c10
T c10
cnot a1 c10
T* c10
cnot bell44 c10
H c10
Z c11
cnot a11 c11
T* c11
cnot b0 c11
T c11
cnot a11 c11
T* c11
cnot bell30 c11
cnot b0 c11
T* c11
cnot bell2 c11
T c11
cnot bell30 c11
T* c11
cnot a1 c11
cnot bell2 c11
T* c11
cnot b10 c11
T c11
cnot a1 c11
T* c11
cnot bell46 c11
cnot b10 c11
T* c11
cnot b11 c11
T c11
cnot bell46 c11
T* c11
cnot bell34 c11
cnot b11 c11
T* c11
cnot bell22 c11
T c11
cnot bell34 c11
T* c11
cnot bell38 c11
cnot bell22 c11
T* c11
cnot bell24 c11
T c11
cnot bell38 c11
T* c11
cnot bell42 c11
cnot bell24 c11
T* c11
cnot bell26 c11
T c11
cnot bell42 c11
T* c11
cnot bell4 c11
cnot bell26 c11
T* c11
cnot bell28 c11
T c11
cnot bell4 c11
T* c11
cnot bell6 c11
cnot bell28 c11
T* c11
cnot bell32 c11
T c11
cnot bell6 c11
T* c11
cnot bell8 c11
cnot bell32 c11
T* c11
cnot bell36 c11
T c11
cnot bell8 c11
T* c11
cnot bell10 c11
cnot bell36 c11
T* c11
cnot bell40 c11
T c11
cnot bell10 c11
T* c11
cnot bell14 c11
cnot bell40 c11
T* c11
cnot bell44 c11
T c11
cnot bell14 c11
T* c11
cnot bell44 c11
H c11
T c12
Z c12
cnot a12 c12
T* c12
cnot b0 c12
T c12
cnot a12 c12
T* c12
cnot a11 c12
cnot b0 c12
T* c12
cnot bell2 c12
T c12
cnot a11 c12
T* c12
cnot bell14 c12
cnot bell2 c12
T* c12
cnot b10 c12
T c12
cnot bell14 c12
T* c12
cnot a1 c12
cnot b10 c12
T* c12
cnot b11 c12
T c12
cnot a1 c12
T* c12
cnot bell46 c12
cnot b11 c12
T* c12
cnot b12 c12
T c12
cnot bell46 c12
T* c12
cnot bell30 c12
cnot b12 c12
T* c12
cnot bell22 c12
T c12
cnot bell30 c12
T* c12
cnot bell34 c12
cnot bell22 c12
T* c12
cnot bell24 c12
T c12
cnot bell34 c12
T* c12
cnot bell38 c12
cnot bell24 c12
T* c12
cnot bell26 c12
T c12
cnot bell38 c12
T* c12
cnot bell42 c12
cnot bell26 c12
T* c12
cnot bell28 c12
T c12
cnot bell42 c12
T* c12
cnot bell4 c12
cnot bell28 c12
T* c12
cnot bell32 c12
T c12
cnot bell4 c12
T* c12
cnot bell6 c12
cnot bell32 c12
T* c12
cnot bell36 c12
T c12
cnot bell6 c12
T* c12
cnot bell8 c12
cnot bell36 c12
T* c12
cnot bell40 c12
T c12
cnot bell8 c12
T* c12
cnot bell10 c12
cnot bell40 c12
T* c12
cnot bell44 c12
T c12
cnot bell10 c12
T* c12
cnot bell44 c12
H c12
S* c13
cnot a13 c13
T* c13
cnot b0 c13
T c13
cnot a13 c13
T* c13
cnot a12 c13
cnot b0 c13
T* c13
cnot bell2 c13
T c13
cnot a12 c13
T* c13
cnot bell10 c13
cnot bell2 c13
T* c13
cnot b10 c13
T c13
cnot bell10 c13
T* c13
cnot bell14 c13
cnot b10 c13
T* c13
cnot b11 c13
T c13
cnot bell14 c13
T* c13
cnot a1 c13
cnot b11 c13
T* c13
cnot b12 c13
T c13
cnot a1 c13
T* c13
cnot bell46 c13
cnot b12 c13
T* c13
cnot bell12 c13
T c13
cnot bell46 c13
T* c13
cnot a11 c13
cnot bell12 c13
T* c13
cnot bell22 c13
T c13
cnot a11 c13
T* c13
cnot bell30 c13
cnot bell22 c13
T* c13
cnot bell24 c13
T c13
cnot bell30 c13
T* c13
cnot bell34 c13
cnot bell24 c13
T* c13
cnot bell26 c13
T c13
cnot bell34 c13
T* c13
cnot bell38 c13
cnot bell26 c13
T* c13
cnot bell28 c13
T c13
cnot bell38 c13
T* c13
cnot bell42 c13
cnot bell28 c13
T* c13
cnot bell32 c13
T c13
cnot bell42 c13
T* c13
cnot bell4 c13
cnot bell32 c13
T* c13
cnot bell36 c13
T c13
cnot bell4 c13
T* c13
cnot bell6 c13
cnot bell36 c13
T* c13
cnot bell40 c13
T c13
cnot bell6 c13
T* c13
cnot bell8 c13
cnot bell40 c13
T* c13
cnot bell44 c13
T c13
cnot bell8 c13
T* c13
cnot bell44 c13
H c13
T* c14
cnot bell20 c14
T* c14
cnot b0 c14
T c14
cnot bell20 c14
T* c14
cnot a13 c14
cnot b0 c14
T* c14
cnot bell2 c14
T c14
cnot a13 c14
T* c14
cnot bell8 c14
cnot bell2 c14
T* c14
cnot b10 c14
T c14
cnot bell8 c14
T* c14
cnot bell10 c14
cnot b10 c14
T* c14
cnot b11 c14
T c14
cnot bell10 c14
T* c14
cnot bell14 c14
cnot b11 c14
T* c14
cnot b12 c14
T c14
cnot bell14 c14
T* c14
cnot a1 c14
cnot b12 c14
T* c14
cnot bell12 c14
T c14
cnot a1 c14
T* c14
cnot bell46 c14
cnot bell12 c14
T* c14
cnot bell16 c14
T c14
cnot bell46 c14
T* c14
cnot a12 c14
cnot bell16 c14
T* c14
cnot bell22 c14
T c14
cnot a12 c14
T* c14
cnot a11 c14
cnot bell22 c14
T* c14
cnot bell24 c14
T c14
cnot a11 c14
T* c14
cnot bell30 c14
cnot bell24 c14
T* c14
cnot bell26 c14
T c14
cnot bell30 c14
T* c14
cnot bell34 c14
cnot bell26 c14
T* c14
cnot bell28 c14
T c14
cnot bell34 c14
T* c14
cnot bell38 c14
cnot bell28 c14
T* c14
cnot bell32 c14
T c14
cnot bell38 c14
T* c14
cnot bell42 c14
cnot bell32 c14
T* c14
cnot bell36 c14
T c14
cnot bell42 c14
T* c14
cnot bell4 c14
cnot bell36 c14
T* c14
cnot bell40 c14
T c14
cnot bell4 c14
T* c14
cnot bell6 c14
cnot bell40 c14
T* c14
cnot bell44 c14
T c14
cnot bell6 c14
T* c14
cnot bell44 c14
H c14
cnot bell0 c15
T* c15
cnot b0 c15
T c15
cnot bell0 c15
H bell0
measure bell0
cz bell0 a15
T* c15
cnot bell20 c15
cnot b0 c15
T* c15
cnot bell2 c15
T c15
cnot bell20 c15
H bell20
measure bell20
cz bell20 a14
T* c15
cnot bell6 c15
cnot bell2 c15
H bell2
measure bell2
cz bell2 b1
T* c15
cnot b10 c15
T c15
cnot bell6 c15
H bell6
measure bell6
cz bell6 a5
T* c15
cnot bell8 c15
cnot b10 c15
T* c15
cnot b11 c15
T c15
cnot bell8 c15
H bell8
measure bell8
cz bell8 a4
T* c15
cnot bell10 c15
cnot b11 c15
T* c15
cnot b12 c15
T c15
cnot bell10 c15
H bell10
measure bell10
cz bell10 a3
T* c15
cnot bell14 c15
cnot b12 c15
T* c15
cnot bell12 c15
T c15
cnot bell14 c15
H bell14
measure bell14
cz bell14 a2
T* c15
cnot a1 c15
cnot bell12 c15
H bell12
measure bell12
cz bell12 b13
T* c15
cnot bell16 c15
T c15
cnot a1 c15
T* c15
cnot bell46 c15
cnot bell16 c15
H bell16
measure bell16
cz bell16 b14
T* c15
cnot bell18 c15
T c15
cnot bell46 c15
T* c15
cnot a13 c15
cnot bell18 c15
H bell18
measure bell18
cz bell18 b15
T* c15
cnot bell22 c15
T c15
cnot a13 c15
T* c15
cnot a12 c15
cnot bell22 c15
H bell22
measure bell22
cz bell22 b2
T* c15
cnot bell24 c15
T c15
cnot a12 c15
T* c15
cnot a11 c15
cnot bell24 c15
H bell24
measure bell24
cz bell24 b3
T* c15
cnot bell26 c15
T c15
cnot a11 c15
T* c15
cnot bell30 c15
cnot bell26 c15
H bell26
measure bell26
cz bell26 b4
T* c15
cnot bell28 c15
T c15
cnot bell30 c15
H bell30
measure bell30
cz bell30 a10
T* c15
cnot bell34 c15
cnot bell28 c15
H bell28
measure bell28
cz bell28 b5
T* c15
cnot bell32 c15
T c15
cnot bell34 c15
H bell34
measure bell34
cz bell34 a9
T* c15
cnot bell38 c15
cnot bell32 c15
H bell32
measure bell32
cz bell32 b6
T* c15
cnot bell36 c15
T c15
cnot bell38 c15
H bell38
measure bell38
cz bell38 a8
T* c15
cnot bell42 c15
cnot bell36 c15
H bell36
measure bell36
cz bell36 b7
T* c15
cnot bell40 c15
T c15
cnot bell42 c15
H bell42
measure bell42
cz bell42 a7
T* c15
cnot bell4 c15
cnot bell40 c15
H bell40
measure bell40
cz bell40 b8
T* c15
cnot bell44 c15
T c15
cnot bell4 c15
H bell4
measure bell4
cz bell4 a6
T* c15
cnot bell44 c15
H bell44
measure bell44
cz bell44 b9
H c15
cnot bell46 b0
T* b0
cnot a1 b0
cnot bell46 b0
T* b0
cnot a0 b1
T* b1
H bell48
cnot bell48 bell49
cnot a1 bell49
measure bell49
cnot bell49 bell48
cnot bell48 b1
cnot a0 b1
T* b1
H bell50
cnot bell50 bell51
cnot b0 bell51
measure bell51
cnot bell51 bell50
cnot bell50 a10
cnot bell48 a10
T* a10
cnot b1 a10
cnot bell50 a10
T* a10
cnot bell46 b10
T* b10
cnot a1 b10
cnot bell46 b10
T* b10
H bell52
cnot bell52 bell53
cnot b1 bell53
measure bell53
cnot bell53 bell52
cnot bell52 b10
H bell54
cnot bell54 bell55
cnot a10 bell55
measure bell55
cnot bell55 bell54
cnot bell54 b10
T* b10
cnot b0 a11
cnot a1 a11
T* a11
cnot bell52 a11
cnot b0 a11
T* a11
cnot b10 a11
cnot bell54 a11
T* a11
cnot bell46 b11
T* b11
cnot a1 b11
cnot bell46 b11
T* b11
cnot bell52 b11
cnot bell54 b11
T* b11
cnot b10 b11
cnot a11 b11
T* b11
cnot b0 a12
cnot a1 a12
T* a12
cnot bell52 a12
cnot b0 a12
T* a12
cnot b10 a12
cnot bell54 a12
T* a12
cnot b11 a12
cnot a11 a12
T* a12
cnot bell46 b12
T* b12
cnot a1 b12
cnot bell46 b12
H bell46
measure bell46
cz bell46 a0
T* b12
cnot bell52 b12
cnot bell54 b12
T* b12
cnot b10 b12
cnot a11 b12
T* b12
cnot b11 b12
cnot a12 b12
T* b12
cnot b0 a13
cnot a1 a13
T* a13
cnot bell52 a13
H bell52
measure bell52
cz bell52 b1
cnot b0 a13
T* a13
cnot b10 a13
cnot bell54 a13
H bell54
measure bell54
cz bell54 a10
T* a13
cnot b11 a13
cnot a11 a13
T* a13
cnot b12 a13
cnot a12 a13
T* a13
cnot a0 b13
T* b13
cnot bell48 b13
cnot a0 b13
T* b13
cnot b1 b13
cnot a10 b13
T* b13
H bell56
cnot bell56 bell57
cnot b10 bell57
measure bell57
cnot bell57 bell56
cnot bell56 b13
H bell58
cnot bell58 bell59
cnot a11 bell59
measure bell59
cnot bell59 bell58
cnot bell58 b13
T* b13
H bell60
cnot bell60 bell61
cnot b11 bell61
measure bell61
cnot bell61 bell60
cnot bell60 b13
H bell62
cnot bell62 bell63
cnot a12 bell63
measure bell63
cnot bell63 bell62
cnot bell62 b13
T* b13
H bell64
cnot bell64 bell65
cnot b12 bell65
measure bell65
cnot bell65 bell64
cnot bell64 b13
H bell66
cnot bell66 bell67
cnot a13 bell67
measure bell67
cnot bell67 bell66
cnot bell66 b13
T* b13
cnot bell50 a14
cnot bell48 a14
T* a14
cnot b1 a14
cnot bell50 a14
T* a14
cnot bell56 a14
cnot a10 a14
T* a14
cnot bell60 a14
cnot bell58 a14
T* a14
cnot bell64 a14
cnot bell62 a14
T* a14
cnot b13 a14
cnot bell66 a14
T* a14
cnot a0 b14
T* b14
cnot bell48 b14
cnot a0 b14
T* b14
cnot b1 b14
cnot a10 b14
T* b14
cnot bell56 b14
cnot bell58 b14
T* b14
cnot bell60 b14
cnot bell62 b14
T* b14
cnot bell64 b14
cnot bell66 b14
T* b14
cnot b13 b14
cnot a14 b14
T* b14
cnot bell50 a15
cnot bell48 a15
T* a15
cnot b1 a15
cnot bell50 a15
T* a15
cnot bell56 a15
cnot a10 a15
T* a15
cnot bell60 a15
cnot bell58 a15
T* a15
cnot bell64 a15
cnot bell62 a15
T* a15
cnot b13 a15
cnot bell66 a15
T* a15
cnot b14 a15
cnot a14 a15
T* a15
cnot a0 b15
T* b15
cnot bell48 b15
cnot a0 b15
T* b15
cnot b1 b15
cnot a10 b15
T* b15
cnot bell56 b15
cnot bell58 b15
T* b15
cnot bell60 b15
cnot bell62 b15
T* b15
cnot bell64 b15
cnot bell66 b15
T* b15
cnot b13 b15
cnot a14 b15
T* b15
cnot b14 b15
cnot a15 b15
T* b15
cnot bell50 a2
cnot bell48 a2
T* a2
cnot b1 a2
cnot bell50 a2
T* a2
cnot bell56 a2
cnot a10 a2
T* a2
cnot bell60 a2
cnot bell58 a2
T* a2
cnot bell64 a2
cnot bell62 a2
T* a2
cnot b13 a2
cnot bell66 a2
T* a2
cnot b14 a2
cnot a14 a2
T* a2
cnot b15 a2
cnot a15 a2
T* a2
cnot a0 b2
T* b2
cnot bell48 b2
cnot a0 b2
T* b2
cnot b1 b2
cnot a10 b2
T* b2
cnot bell56 b2
cnot bell58 b2
T* b2
cnot bell60 b2
cnot bell62 b2
T* b2
cnot bell64 b2
cnot bell66 b2
T* b2
cnot b13 b2
cnot a14 b2
T* b2
cnot b14 b2
cnot a15 b2
T* b2
cnot b15 b2
cnot a2 b2
T* b2
cnot bell50 a3
cnot bell48 a3
T* a3
cnot b1 a3
cnot bell50 a3
T* a3
cnot bell56 a3
cnot a10 a3
T* a3
cnot bell60 a3
cnot bell58 a3
T* a3
cnot bell64 a3
cnot bell62 a3
T* a3
cnot b13 a3
cnot bell66 a3
T* a3
cnot b14 a3
cnot a14 a3
T* a3
cnot b15 a3
cnot a15 a3
T* a3
cnot b2 a3
cnot a2 a3
T* a3
cnot a0 b3
T* b3
cnot bell48 b3
cnot a0 b3
T* b3
cnot b1 b3
cnot a10 b3
T* b3
cnot bell56 b3
cnot bell58 b3
T* b3
cnot bell60 b3
cnot bell62 b3
T* b3
cnot bell64 b3
cnot bell66 b3
T* b3
cnot b13 b3
cnot a14 b3
T* b3
cnot b14 b3
cnot a15 b3
T* b3
cnot b15 b3
cnot a2 b3
T* b3
cnot b2 b3
cnot a3 b3
T* b3
cnot bell50 a4
cnot bell48 a4
T* a4
cnot b1 a4
cnot bell50 a4
T* a4
cnot bell56 a4
cnot a10 a4
T* a4
cnot bell60 a4
cnot bell58 a4
T* a4
cnot bell64 a4
cnot bell62 a4
T* a4
cnot b13 a4
cnot bell66 a4
T* a4
cnot b14 a4
cnot a14 a4
T* a4
cnot b15 a4
cnot a15 a4
T* a4
cnot b2 a4
cnot a2 a4
T* a4
cnot b3 a4
cnot a3 a4
T* a4
cnot a0 b4
T* b4
cnot bell48 b4
cnot a0 b4
T* b4
cnot b1 b4
cnot a10 b4
T* b4
cnot bell56 b4
cnot bell58 b4
T* b4
cnot bell60 b4
cnot bell62 b4
T* b4
cnot bell64 b4
cnot bell66 b4
T* b4
cnot b13 b4
cnot a14 b4
T* b4
cnot b14 b4
cnot a15 b4
T* b4
cnot b15 b4
cnot a2 b4
T* b4
cnot b2 b4
cnot a3 b4
T* b4
cnot b3 b4
cnot a4 b4
T* b4
cnot bell50 a5
cnot bell48 a5
T* a5
cnot b1 a5
cnot bell50 a5
T* a5
cnot bell56 a5
cnot a10 a5
T* a5
cnot bell60 a5
cnot bell58 a5
T* a5
cnot bell64 a5
cnot bell62 a5
T* a5
cnot b13 a5
cnot bell66 a5
T* a5
cnot b14 a5
cnot a14 a5
T* a5
cnot b15 a5
cnot a15 a5
T* a5
cnot b2 a5
cnot a2 a5
T* a5
cnot b3 a5
cnot a3 a5
T* a5
cnot b4 a5
cnot a4 a5
T* a5
cnot a0 b5
T* b5
cnot bell48 b5
cnot a0 b5
T* b5
cnot b1 b5
cnot a10 b5
T* b5
cnot bell56 b5
cnot bell58 b5
T* b5
cnot bell60 b5
cnot bell62 b5
T* b5
cnot bell64 b5
cnot bell66 b5
T* b5
cnot b13 b5
cnot a14 b5
T* b5
cnot b14 b5
cnot a15 b5
T* b5
cnot b15 b5
cnot a2 b5
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
cnot bell50 a6
cnot bell48 a6
T* a6
cnot b1 a6
cnot bell50 a6
T* a6
cnot bell56 a6
cnot a10 a6
T* a6
cnot bell60 a6
cnot bell58 a6
T* a6
cnot bell64 a6
cnot bell62 a6
T* a6
cnot b13 a6
cnot bell66 a6
T* a6
cnot b14 a6
cnot a14 a6
T* a6
cnot b15 a6
cnot a15 a6
T* a6
cnot b2 a6
cnot a2 a6
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
cnot a0 b6
T* b6
cnot bell48 b6
cnot a0 b6
T* b6
cnot b1 b6
cnot a10 b6
T* b6
cnot bell56 b6
cnot bell58 b6
T* b6
cnot bell60 b6
cnot bell62 b6
T* b6
cnot bell64 b6
cnot bell66 b6
T* b6
cnot b13 b6
cnot a14 b6
T* b6
cnot b14 b6
cnot a15 b6
T* b6
cnot b15 b6
cnot a2 b6
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
cnot bell50 a7
cnot bell48 a7
T* a7
cnot b1 a7
cnot bell50 a7
T* a7
cnot bell56 a7
cnot a10 a7
T* a7
cnot bell60 a7
cnot bell58 a7
T* a7
cnot bell64 a7
cnot bell62 a7
T* a7
cnot b13 a7
cnot bell66 a7
T* a7
cnot b14 a7
cnot a14 a7
T* a7
cnot b15 a7
cnot a15 a7
T* a7
cnot b2 a7
cnot a2 a7
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
cnot a0 b7
T* b7
cnot bell48 b7
cnot a0 b7
T* b7
cnot b1 b7
cnot a10 b7
T* b7
cnot bell56 b7
cnot bell58 b7
T* b7
cnot bell60 b7
cnot bell62 b7
T* b7
cnot bell64 b7
cnot bell66 b7
T* b7
cnot b13 b7
cnot a14 b7
T* b7
cnot b14 b7
cnot a15 b7
T* b7
cnot b15 b7
cnot a2 b7
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
cnot bell50 a8
cnot bell48 a8
T* a8
cnot b1 a8
cnot bell50 a8
T* a8
cnot bell56 a8
cnot a10 a8
T* a8
cnot bell60 a8
cnot bell58 a8
T* a8
cnot bell64 a8
cnot bell62 a8
T* a8
cnot b13 a8
cnot bell66 a8
T* a8
cnot b14 a8
cnot a14 a8
T* a8
cnot b15 a8
cnot a15 a8
T* a8
cnot b2 a8
cnot a2 a8
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
cnot a0 b8
T* b8
cnot bell48 b8
cnot a0 b8
T* b8
cnot b1 b8
cnot a10 b8
T* b8
cnot bell56 b8
cnot bell58 b8
T* b8
cnot bell60 b8
cnot bell62 b8
T* b8
cnot bell64 b8
cnot bell66 b8
T* b8
cnot b13 b8
cnot a14 b8
T* b8
cnot b14 b8
cnot a15 b8
T* b8
cnot b15 b8
cnot a2 b8
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
cnot bell50 a9
cnot bell48 a9
T* a9
cnot b1 a9
cnot bell50 a9
H bell50
measure bell50
cz bell50 b0
T* a9
cnot bell56 a9
cnot a10 a9
T* a9
cnot bell60 a9
cnot bell58 a9
T* a9
cnot bell64 a9
cnot bell62 a9
T* a9
cnot b13 a9
cnot bell66 a9
T* a9
cnot b14 a9
cnot a14 a9
T* a9
cnot b15 a9
cnot a15 a9
T* a9
cnot b2 a9
cnot a2 a9
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
cnot a0 b9
T* b9
cnot bell48 b9
cnot a0 b9
T* b9
cnot b1 b9
cnot a10 b9
T* b9
cnot bell56 b9
H bell56
measure bell56
cz bell56 b10
cnot bell58 b9
H bell58
measure bell58
cz bell58 a11
T* b9
cnot bell60 b9
H bell60
measure bell60
cz bell60 b11
cnot bell62 b9
H bell62
measure bell62
cz bell62 a12
T* b9
cnot bell64 b9
H bell64
measure bell64
cz bell64 b12
cnot bell66 b9
H bell66
measure bell66
cz bell66 a13
T* b9
cnot b13 b9
cnot a14 b9
T* b9
cnot b14 b9
cnot a15 b9
T* b9
cnot b15 b9
cnot a2 b9
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
cnot b1 a10
cnot b10 a11
cnot b11 a12
cnot b12 a13
cnot b13 a14
cnot b14 a15
cnot b15 a2
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
cnot a15 a2
cnot a14 a2
cnot a14 a15
cnot a2 b9
cnot a2 b8
cnot a2 b7
cnot a2 b6
cnot a2 b5
cnot a2 b4
cnot a2 b3
cnot a2 b2
cnot a15 b15
cnot a14 b14
cnot a2 a9
cnot a2 a8
cnot a2 a7
cnot a2 a6
cnot a2 a5
cnot a2 a4
cnot a2 a3
cnot a12 a13
cnot a11 a13
cnot a11 a12
H bell68
cnot bell68 bell69
cnot a13 bell69
measure bell69
cnot bell69 bell68
cnot bell68 b9
cnot bell68 b8
cnot bell68 b7
cnot bell68 b6
cnot bell68 b5
cnot bell68 b4
cnot bell68 b3
cnot bell68 b2
cnot bell68 b15
cnot bell68 b14
cnot bell68 b13
cnot a12 b12
cnot a11 b11
cnot bell68 a9
cnot bell68 a8
cnot bell68 a7
cnot bell68 a6
cnot bell68 a5
cnot bell68 a4
cnot bell68 a3
cnot bell68 a2
cnot bell68 a15
cnot bell68 a14
H bell68
measure bell68
cz bell68 a13
cnot bell48 a10
cnot a10 b9
cnot a10 b8
cnot a10 b7
cnot a10 b6
cnot a10 b5
cnot a10 b4
cnot a10 b3
cnot a10 b2
cnot a10 b15
cnot a10 b14
cnot a10 b13
H bell70
cnot bell70 bell71
cnot a10 bell71
measure bell71
cnot bell71 bell70
cnot bell70 b12
cnot bell70 b11
cnot bell70 b10
cnot bell48 b1
H bell48
measure bell48
cz bell48 a1
cnot a1 b0
cnot a10 a9
cnot a10 a8
cnot a10 a7
cnot a10 a6
cnot a10 a5
cnot a10 a4
cnot a10 a3
cnot a10 a2
cnot a10 a15
cnot a10 a14
cnot bell70 a13
cnot bell70 a12
cnot bell70 a11
H bell70
measure bell70
cz bell70 a10
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
reset bell68
reset bell69
reset bell70
reset bell71
END
