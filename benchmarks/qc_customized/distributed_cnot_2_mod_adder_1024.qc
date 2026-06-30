# Hyperedge cut (ebits): 48

# Actual ebits used (Synthesis): 48
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_adder_1024.qc):
#   Qubits: 28
#   H: 570
#   T: 1995
#   cnot: 1720
#   Depth: 2218
#   T depth: 981
# Result (788.947ms):
#   Qubits: 124
#   H: 426
#   T: 1259
#   cnot: 1404
#   cz: 48
#   measure: 96
#   reset: 107
#   swap: 8
#   Depth: 2325
#   T depth: 863


# Result Circuit
.v x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 0 1 2 3 4 5 6 7 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell40 bell41 bell42 bell43 bell44 bell45 bell46 bell47 bell48 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95
.i x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
.o x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
BEGIN 
H bell0
cnot bell0 bell1
cnot x10 bell1
measure bell1
cnot bell1 bell0
cnot bell0 x20
H bell0
measure bell0
cz bell0 x10
H x20
T x20
cnot x19 x20
T* x20
H bell2
cnot bell2 bell3
cnot x9 bell3
measure bell3
cnot bell3 bell2
cnot bell2 x20
T x20
cnot x19 x20
T* x20
cnot bell2 x20
swap 0 1
cnot bell2 x19
H 0
T 0
cnot x18 0
T* 0
cnot x8 0
T 0
cnot x18 0
T* 0
cnot x8 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot x18 0
T 0
cnot x8 0
T* 0
cnot x18 0
T 0
cnot x8 0
cnot bell2 x19
T x19
cnot bell2 x19
H bell2
measure bell2
cz bell2 x9
H x19
T x19
cnot x18 x19
T* x19
cnot x8 x19
T x19
cnot x18 x19
T* x19
cnot x8 x19
H x19
cnot x8 x18
H 1
T 1
cnot x17 1
T* 1
cnot x7 1
T 1
cnot x17 1
T* 1
cnot x7 1
swap 2 6
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot x17 1
T 1
cnot x7 1
T* 1
cnot x17 1
T 1
cnot x7 1
T 0
cnot x17 0
T* 0
cnot x7 0
T 0
cnot x17 0
T* 0
cnot x7 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
swap 2 7
H 0
T* 0
cnot x17 0
T 0
cnot x7 0
T* 0
cnot x17 0
T 0
cnot x7 0
swap 2 6
cnot x8 x18
T x18
cnot x8 x18
H x18
T x18
cnot x17 x18
T* x18
cnot x7 x18
T x18
cnot x17 x18
T* x18
cnot x7 x18
H x18
cnot x7 x17
H 2
T 2
cnot x16 2
T* 2
H bell4
cnot bell4 bell5
cnot x6 bell5
measure bell5
cnot bell5 bell4
cnot bell4 2
T 2
cnot x16 2
T* 2
cnot bell4 2
H 2
T 1
cnot 2 1
T* 1
cnot x17 1
T 1
cnot 2 1
T* 1
cnot x17 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot x17 1
T* 1
cnot 2 1
T 1
cnot x17 1
H 2
T* 2
cnot x16 2
T 2
cnot bell4 2
T* 2
cnot x16 2
T 2
cnot bell4 2
T 1
cnot x16 1
T* 1
cnot bell4 1
T 1
cnot x16 1
T* 1
cnot bell4 1
swap 3 5
H 1
T 0
cnot 1 0
T* 0
cnot x17 0
T 0
cnot 1 0
T* 0
cnot x17 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot x17 0
T* 0
cnot 1 0
T 0
cnot x17 0
H 1
T* 1
cnot x16 1
T 1
cnot bell4 1
T* 1
cnot x16 1
T 1
cnot bell4 1
T 0
cnot x16 0
T* 0
cnot bell4 0
T 0
cnot x16 0
T* 0
cnot bell4 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
H x18
T 0
cnot x17 0
T* 0
cnot x17 0
swap 3 6
H 0
T* 0
cnot x16 0
T 0
cnot bell4 0
T* 0
cnot x16 0
T 0
cnot bell4 0
swap 3 5
cnot x7 x17
T x17
cnot x7 x17
H x17
T x17
cnot x16 x17
T* x17
cnot bell4 x17
T x17
cnot x16 x17
T* x17
cnot bell4 x17
H x17
cnot bell4 x16
H 3
T 3
cnot x15 3
T* 3
cnot x5 3
T 3
cnot x15 3
T* 3
cnot x5 3
H 3
T 2
cnot 3 2
T* 2
cnot x16 2
T 2
cnot 3 2
T* 2
cnot x16 2
H 2
T 1
cnot 2 1
T* 1
cnot x17 1
T 1
cnot 2 1
T* 1
cnot x17 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot x17 1
T* 1
cnot 2 1
T 1
cnot x17 1
H 2
T* 2
cnot 3 2
T 2
cnot x16 2
T* 2
cnot 3 2
T 2
cnot x16 2
H 3
T* 3
cnot x15 3
T 3
cnot x5 3
T* 3
cnot x15 3
T 3
cnot x5 3
T 2
cnot x15 2
T* 2
cnot x5 2
T 2
cnot x15 2
T* 2
cnot x5 2
H 2
T 1
cnot 2 1
T* 1
cnot x16 1
T 1
cnot 2 1
T* 1
cnot x16 1
H 1
T 0
cnot 1 0
T* 0
cnot x17 0
T 0
cnot 1 0
T* 0
cnot x17 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot x17 0
T* 0
cnot 1 0
T 0
cnot x17 0
H 1
T* 1
cnot 2 1
T 1
cnot x16 1
T* 1
cnot 2 1
T 1
cnot x16 1
H 2
T* 2
cnot x15 2
T 2
cnot x5 2
T* 2
cnot x15 2
T 2
cnot x5 2
T 1
cnot x15 1
T* 1
cnot x5 1
T 1
cnot x15 1
T* 1
cnot x5 1
H 1
T 0
cnot 1 0
T* 0
cnot x16 0
T 0
cnot 1 0
T* 0
cnot x16 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
H x18
T 0
cnot x17 0
T* 0
cnot x17 0
H 0
T* 0
cnot 1 0
T 0
cnot x16 0
T* 0
cnot 1 0
T 0
cnot x16 0
H 1
T* 1
cnot x15 1
T 1
cnot x5 1
T* 1
cnot x15 1
T 1
cnot x5 1
T 0
cnot x15 0
T* 0
cnot x5 0
T 0
cnot x15 0
T* 0
cnot x5 0
H 0
T x17
H x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
H x17
T 0
cnot x16 0
T* 0
cnot x16 0
swap 4 5
H 0
T* 0
cnot x15 0
T 0
cnot x5 0
T* 0
cnot x15 0
T 0
cnot x5 0
H bell6
cnot bell6 bell7
cnot x16 bell7
measure bell7
cnot bell7 bell6
cnot x6 bell6
H bell8
cnot bell8 bell9
cnot bell6 bell9
measure bell9
cnot bell9 bell8
reset bell9
cnot x16 bell8
cnot bell8 x16
H bell8
measure bell8
cz bell8 x6
H bell6
measure bell6
cz bell6 x16
T x16
cnot bell4 x16
H bell4
measure bell4
cz bell4 x6
H x16
T x16
cnot x15 x16
T* x16
cnot x5 x16
T x16
cnot x15 x16
T* x16
cnot x5 x16
H x16
cnot x5 x15
H 4
T 4
H bell10
cnot bell10 bell11
cnot x14 bell11
measure bell11
cnot bell11 bell10
cnot bell10 4
T* 4
H bell12
cnot bell12 bell13
cnot x4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 4
T 4
cnot bell10 4
T* 4
cnot bell12 4
H 4
T 3
cnot 4 3
T* 3
cnot x15 3
T 3
cnot 4 3
T* 3
cnot x15 3
H 3
T 2
cnot 3 2
T* 2
cnot x16 2
T 2
cnot 3 2
T* 2
cnot x16 2
H 2
T 1
cnot 2 1
T* 1
cnot x17 1
T 1
cnot 2 1
T* 1
cnot x17 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot x17 1
T* 1
cnot 2 1
T 1
cnot x17 1
H 2
T* 2
cnot 3 2
T 2
cnot x16 2
T* 2
cnot 3 2
T 2
cnot x16 2
H 3
T* 3
cnot 4 3
T 3
cnot x15 3
T* 3
cnot 4 3
T 3
cnot x15 3
H 4
T* 4
cnot bell10 4
T 4
cnot bell12 4
T* 4
cnot bell10 4
T 4
cnot bell12 4
T 3
cnot bell10 3
T* 3
cnot bell12 3
T 3
cnot bell10 3
T* 3
cnot bell12 3
H 3
T 2
cnot 3 2
T* 2
cnot x15 2
T 2
cnot 3 2
T* 2
cnot x15 2
H 2
T 1
cnot 2 1
T* 1
cnot x16 1
T 1
cnot 2 1
T* 1
cnot x16 1
H 1
T 0
cnot 1 0
T* 0
cnot x17 0
T 0
cnot 1 0
T* 0
cnot x17 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot x17 0
T* 0
cnot 1 0
T 0
cnot x17 0
H 1
T* 1
cnot 2 1
T 1
cnot x16 1
T* 1
cnot 2 1
T 1
cnot x16 1
H 2
T* 2
cnot 3 2
T 2
cnot x15 2
T* 2
cnot 3 2
T 2
cnot x15 2
H 3
T* 3
cnot bell10 3
T 3
cnot bell12 3
T* 3
cnot bell10 3
T 3
cnot bell12 3
T 2
cnot bell10 2
T* 2
cnot bell12 2
T 2
cnot bell10 2
T* 2
cnot bell12 2
H 2
T 1
cnot 2 1
T* 1
cnot x15 1
T 1
cnot 2 1
T* 1
cnot x15 1
H 1
T 0
cnot 1 0
T* 0
cnot x16 0
T 0
cnot 1 0
T* 0
cnot x16 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
H x18
T 0
cnot x17 0
T* 0
cnot x17 0
H 0
T* 0
cnot 1 0
T 0
cnot x16 0
T* 0
cnot 1 0
T 0
cnot x16 0
H 1
T* 1
cnot 2 1
T 1
cnot x15 1
T* 1
cnot 2 1
T 1
cnot x15 1
H 2
T* 2
cnot bell10 2
T 2
cnot bell12 2
T* 2
cnot bell10 2
T 2
cnot bell12 2
T 1
cnot bell10 1
T* 1
cnot bell12 1
T 1
cnot bell10 1
T* 1
cnot bell12 1
H 1
T 0
cnot 1 0
T* 0
cnot x15 0
T 0
cnot 1 0
T* 0
cnot x15 0
H 0
T x17
H x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
H x17
T 0
cnot x16 0
T* 0
cnot x16 0
H 0
T* 0
cnot 1 0
T 0
cnot x15 0
T* 0
cnot 1 0
T 0
cnot x15 0
H 1
T* 1
cnot bell10 1
T 1
cnot bell12 1
T* 1
cnot bell10 1
T 1
cnot bell12 1
T 0
cnot bell10 0
T* 0
cnot bell12 0
T 0
cnot bell10 0
T* 0
cnot bell12 0
H 0
T x16
H x16
T x16
cnot 0 x16
T* x16
cnot x15 x16
T x16
cnot 0 x16
T* x16
cnot x15 x16
H x16
T 0
cnot x15 0
T* 0
cnot x15 0
H 0
T* 0
cnot bell10 0
T 0
cnot bell12 0
T* 0
cnot bell10 0
T 0
cnot bell12 0
cnot x5 x15
T x15
cnot x5 x15
H x15
T x15
cnot bell10 x15
T* x15
cnot bell12 x15
T x15
cnot bell10 x15
H bell10
measure bell10
cz bell10 x14
T* x15
cnot bell12 x15
H bell12
measure bell12
cz bell12 x4
H x15
cnot x4 x14
H 5
T 5
cnot x13 5
T* 5
cnot x3 5
T 5
cnot x13 5
T* 5
cnot x3 5
H 5
T 4
H bell14
cnot bell14 bell15
cnot 5 bell15
measure bell15
cnot bell15 bell14
cnot bell14 4
T* 4
H bell16
cnot bell16 bell17
cnot x14 bell17
measure bell17
cnot bell17 bell16
cnot bell16 4
T 4
cnot bell14 4
T* 4
cnot bell16 4
H 4
T 3
cnot 4 3
T* 3
cnot x15 3
T 3
cnot 4 3
T* 3
cnot x15 3
H 3
T 2
cnot 3 2
T* 2
cnot x16 2
T 2
cnot 3 2
T* 2
cnot x16 2
H 2
T 1
cnot 2 1
T* 1
cnot x17 1
T 1
cnot 2 1
T* 1
cnot x17 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot x17 1
T* 1
cnot 2 1
T 1
cnot x17 1
H 2
T* 2
cnot 3 2
T 2
cnot x16 2
T* 2
cnot 3 2
T 2
cnot x16 2
H 3
T* 3
cnot 4 3
T 3
cnot x15 3
T* 3
cnot 4 3
T 3
cnot x15 3
H 4
T* 4
cnot bell14 4
T 4
cnot bell16 4
T* 4
cnot bell14 4
H bell14
measure bell14
cz bell14 5
T 4
cnot bell16 4
H 5
T* 5
cnot x13 5
T 5
cnot x3 5
T* 5
cnot x13 5
T 5
cnot x3 5
T 4
H bell18
cnot bell18 bell19
cnot x13 bell19
measure bell19
cnot bell19 bell18
cnot bell18 4
T* 4
H bell20
cnot bell20 bell21
cnot x3 bell21
measure bell21
cnot bell21 bell20
cnot bell20 4
T 4
cnot bell18 4
T* 4
cnot bell20 4
H 4
T 3
cnot 4 3
T* 3
cnot bell16 3
T 3
cnot 4 3
T* 3
cnot bell16 3
H 3
T 2
cnot 3 2
T* 2
cnot x15 2
T 2
cnot 3 2
T* 2
cnot x15 2
H 2
T 1
cnot 2 1
T* 1
cnot x16 1
T 1
cnot 2 1
T* 1
cnot x16 1
H 1
T 0
cnot 1 0
T* 0
cnot x17 0
T 0
cnot 1 0
T* 0
cnot x17 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot x17 0
T* 0
cnot 1 0
T 0
cnot x17 0
H 1
T* 1
cnot 2 1
T 1
cnot x16 1
T* 1
cnot 2 1
T 1
cnot x16 1
H 2
T* 2
cnot 3 2
T 2
cnot x15 2
T* 2
cnot 3 2
T 2
cnot x15 2
H 3
T* 3
cnot 4 3
T 3
cnot bell16 3
T* 3
cnot 4 3
T 3
cnot bell16 3
H 4
T* 4
cnot bell18 4
T 4
cnot bell20 4
T* 4
cnot bell18 4
T 4
cnot bell20 4
T 3
cnot bell18 3
T* 3
cnot bell20 3
T 3
cnot bell18 3
T* 3
cnot bell20 3
H 3
T 2
cnot 3 2
T* 2
cnot bell16 2
T 2
cnot 3 2
T* 2
cnot bell16 2
H 2
T 1
cnot 2 1
T* 1
cnot x15 1
T 1
cnot 2 1
T* 1
cnot x15 1
H 1
T 0
cnot 1 0
T* 0
cnot x16 0
T 0
cnot 1 0
T* 0
cnot x16 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
H x18
T 0
cnot x17 0
T* 0
cnot x17 0
H 0
T* 0
cnot 1 0
T 0
cnot x16 0
T* 0
cnot 1 0
T 0
cnot x16 0
H 1
T* 1
cnot 2 1
T 1
cnot x15 1
T* 1
cnot 2 1
T 1
cnot x15 1
H 2
T* 2
cnot 3 2
T 2
cnot bell16 2
T* 2
cnot 3 2
T 2
cnot bell16 2
H 3
T* 3
cnot bell18 3
T 3
cnot bell20 3
T* 3
cnot bell18 3
T 3
cnot bell20 3
T 2
cnot bell18 2
T* 2
cnot bell20 2
T 2
cnot bell18 2
T* 2
cnot bell20 2
H 2
T 1
cnot 2 1
T* 1
cnot bell16 1
T 1
cnot 2 1
T* 1
cnot bell16 1
H 1
T 0
cnot 1 0
T* 0
cnot x15 0
T 0
cnot 1 0
T* 0
cnot x15 0
H 0
T x17
H x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
H x17
T 0
cnot x16 0
T* 0
cnot x16 0
H 0
T* 0
cnot 1 0
T 0
cnot x15 0
T* 0
cnot 1 0
T 0
cnot x15 0
H 1
T* 1
cnot 2 1
T 1
cnot bell16 1
T* 1
cnot 2 1
T 1
cnot bell16 1
H 2
T* 2
cnot bell18 2
T 2
cnot bell20 2
T* 2
cnot bell18 2
T 2
cnot bell20 2
T 1
cnot bell18 1
T* 1
cnot bell20 1
T 1
cnot bell18 1
T* 1
cnot bell20 1
H 1
T 0
cnot 1 0
T* 0
cnot bell16 0
T 0
cnot 1 0
T* 0
cnot bell16 0
H 0
T x16
H x16
T x16
cnot 0 x16
T* x16
cnot x15 x16
T x16
cnot 0 x16
T* x16
cnot x15 x16
H x16
T 0
cnot x15 0
T* 0
cnot x15 0
H 0
T* 0
cnot 1 0
T 0
cnot bell16 0
T* 0
cnot 1 0
T 0
cnot bell16 0
H 1
T* 1
cnot bell18 1
T 1
cnot bell20 1
T* 1
cnot bell18 1
T 1
cnot bell20 1
T 0
cnot bell18 0
T* 0
cnot bell20 0
T 0
cnot bell18 0
T* 0
cnot bell20 0
H 0
T x15
H x15
T x15
cnot 0 x15
T* x15
cnot bell16 x15
T x15
cnot 0 x15
T* x15
cnot bell16 x15
H x15
T 0
cnot bell16 0
T* 0
cnot bell16 0
H bell16
measure bell16
cz bell16 x14
H 0
T* 0
cnot bell18 0
T 0
cnot bell20 0
T* 0
cnot bell18 0
H bell18
measure bell18
cz bell18 x13
T 0
cnot bell20 0
H bell20
measure bell20
cz bell20 x3
cnot x4 x14
T x14
cnot x4 x14
H x14
T x14
cnot x13 x14
T* x14
cnot x3 x14
T x14
cnot x13 x14
T* x14
cnot x3 x14
H x14
cnot x3 x13
H 6
T 6
cnot x12 6
T* 6
cnot x2 6
T 6
cnot x12 6
T* 6
cnot x2 6
H 6
T 5
cnot 6 5
T* 5
cnot x13 5
T 5
cnot 6 5
T* 5
cnot x13 5
H 5
T 4
H bell22
cnot bell22 bell23
cnot 5 bell23
measure bell23
cnot bell23 bell22
cnot bell22 4
T* 4
H bell24
cnot bell24 bell25
cnot x14 bell25
measure bell25
cnot bell25 bell24
cnot bell24 4
T 4
cnot bell22 4
T* 4
cnot bell24 4
H 4
T 3
cnot 4 3
T* 3
cnot x15 3
T 3
cnot 4 3
T* 3
cnot x15 3
H 3
T 2
cnot 3 2
T* 2
cnot x16 2
T 2
cnot 3 2
T* 2
cnot x16 2
H 2
T 1
cnot 2 1
T* 1
cnot x17 1
T 1
cnot 2 1
T* 1
cnot x17 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot x17 1
T* 1
cnot 2 1
T 1
cnot x17 1
H 2
T* 2
cnot 3 2
T 2
cnot x16 2
T* 2
cnot 3 2
T 2
cnot x16 2
H 3
T* 3
cnot 4 3
T 3
cnot x15 3
T* 3
cnot 4 3
T 3
cnot x15 3
H 4
T* 4
cnot bell22 4
T 4
cnot bell24 4
T* 4
cnot bell22 4
H bell22
measure bell22
cz bell22 5
T 4
cnot bell24 4
H 5
T* 5
cnot 6 5
T 5
cnot x13 5
T* 5
cnot 6 5
T 5
cnot x13 5
H 6
T* 6
cnot x12 6
T 6
cnot x2 6
T* 6
cnot x12 6
T 6
cnot x2 6
T 5
cnot x12 5
T* 5
cnot x2 5
T 5
cnot x12 5
T* 5
cnot x2 5
H 5
T 4
H bell26
cnot bell26 bell27
cnot 5 bell27
measure bell27
cnot bell27 bell26
cnot bell26 4
T* 4
H bell28
cnot bell28 bell29
cnot x13 bell29
measure bell29
cnot bell29 bell28
cnot bell28 4
T 4
cnot bell26 4
T* 4
cnot bell28 4
H 4
T 3
cnot 4 3
T* 3
cnot bell24 3
T 3
cnot 4 3
T* 3
cnot bell24 3
H 3
T 2
cnot 3 2
T* 2
cnot x15 2
T 2
cnot 3 2
T* 2
cnot x15 2
H 2
T 1
cnot 2 1
T* 1
cnot x16 1
T 1
cnot 2 1
T* 1
cnot x16 1
H 1
T 0
cnot 1 0
T* 0
cnot x17 0
T 0
cnot 1 0
T* 0
cnot x17 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot x17 0
T* 0
cnot 1 0
T 0
cnot x17 0
H 1
T* 1
cnot 2 1
T 1
cnot x16 1
T* 1
cnot 2 1
T 1
cnot x16 1
H 2
T* 2
cnot 3 2
T 2
cnot x15 2
T* 2
cnot 3 2
T 2
cnot x15 2
H 3
T* 3
cnot 4 3
T 3
cnot bell24 3
T* 3
cnot 4 3
T 3
cnot bell24 3
H 4
T* 4
cnot bell26 4
T 4
cnot bell28 4
T* 4
cnot bell26 4
H bell26
measure bell26
cz bell26 5
T 4
cnot bell28 4
H 5
T* 5
cnot x12 5
T 5
cnot x2 5
T* 5
cnot x12 5
T 5
cnot x2 5
T 4
H bell30
cnot bell30 bell31
cnot x12 bell31
measure bell31
cnot bell31 bell30
cnot bell30 4
T* 4
H bell32
cnot bell32 bell33
cnot x2 bell33
measure bell33
cnot bell33 bell32
cnot bell32 4
T 4
cnot bell30 4
T* 4
cnot bell32 4
H 4
T 3
cnot 4 3
T* 3
cnot bell28 3
T 3
cnot 4 3
T* 3
cnot bell28 3
H 3
T 2
cnot 3 2
T* 2
cnot bell24 2
T 2
cnot 3 2
T* 2
cnot bell24 2
H 2
T 1
cnot 2 1
T* 1
cnot x15 1
T 1
cnot 2 1
T* 1
cnot x15 1
H 1
T 0
cnot 1 0
T* 0
cnot x16 0
T 0
cnot 1 0
T* 0
cnot x16 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
H x18
T 0
cnot x17 0
T* 0
cnot x17 0
H 0
T* 0
cnot 1 0
T 0
cnot x16 0
T* 0
cnot 1 0
T 0
cnot x16 0
H 1
T* 1
cnot 2 1
T 1
cnot x15 1
T* 1
cnot 2 1
T 1
cnot x15 1
H 2
T* 2
cnot 3 2
T 2
cnot bell24 2
T* 2
cnot 3 2
T 2
cnot bell24 2
H 3
T* 3
cnot 4 3
T 3
cnot bell28 3
T* 3
cnot 4 3
T 3
cnot bell28 3
H 4
T* 4
cnot bell30 4
T 4
cnot bell32 4
T* 4
cnot bell30 4
T 4
cnot bell32 4
T 3
cnot bell30 3
T* 3
cnot bell32 3
T 3
cnot bell30 3
T* 3
cnot bell32 3
H 3
T 2
cnot 3 2
T* 2
cnot bell28 2
T 2
cnot 3 2
T* 2
cnot bell28 2
H 2
T 1
cnot 2 1
T* 1
cnot bell24 1
T 1
cnot 2 1
T* 1
cnot bell24 1
H 1
T 0
cnot 1 0
T* 0
cnot x15 0
T 0
cnot 1 0
T* 0
cnot x15 0
H 0
T x17
H x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
H x17
T 0
cnot x16 0
T* 0
cnot x16 0
H 0
T* 0
cnot 1 0
T 0
cnot x15 0
T* 0
cnot 1 0
T 0
cnot x15 0
H 1
T* 1
cnot 2 1
T 1
cnot bell24 1
T* 1
cnot 2 1
T 1
cnot bell24 1
H 2
T* 2
cnot 3 2
T 2
cnot bell28 2
T* 2
cnot 3 2
T 2
cnot bell28 2
H 3
T* 3
cnot bell30 3
T 3
cnot bell32 3
T* 3
cnot bell30 3
T 3
cnot bell32 3
T 2
cnot bell30 2
T* 2
cnot bell32 2
T 2
cnot bell30 2
T* 2
cnot bell32 2
H 2
T 1
cnot 2 1
T* 1
cnot bell28 1
T 1
cnot 2 1
T* 1
cnot bell28 1
H 1
T 0
cnot 1 0
T* 0
cnot bell24 0
T 0
cnot 1 0
T* 0
cnot bell24 0
H 0
T x16
H x16
T x16
cnot 0 x16
T* x16
cnot x15 x16
T x16
cnot 0 x16
T* x16
cnot x15 x16
H x16
T 0
cnot x15 0
T* 0
cnot x15 0
H 0
T* 0
cnot 1 0
T 0
cnot bell24 0
T* 0
cnot 1 0
T 0
cnot bell24 0
H 1
T* 1
cnot 2 1
T 1
H bell34
cnot bell34 bell35
cnot 1 bell35
measure bell35
cnot bell35 bell34
cnot x13 bell34
H bell36
cnot bell36 bell37
cnot bell34 bell37
measure bell37
cnot bell37 bell36
reset bell37
cnot 1 bell36
cnot bell36 1
H bell36
measure bell36
cz bell36 x13
H bell34
measure bell34
cz bell34 1
T* 1
cnot 2 1
T 1
cnot bell28 1
H 2
T* 2
cnot bell30 2
T 2
cnot bell32 2
T* 2
cnot bell30 2
T 2
cnot bell32 2
T 1
cnot bell30 1
T* 1
cnot bell32 1
T 1
cnot bell30 1
T* 1
cnot bell32 1
H 1
T 0
cnot 1 0
T* 0
cnot bell28 0
T 0
cnot 1 0
T* 0
cnot bell28 0
H 0
T x15
H x15
T x15
cnot 0 x15
T* x15
cnot bell24 x15
T x15
cnot 0 x15
T* x15
cnot bell24 x15
H x15
T 0
cnot bell24 0
T* 0
cnot bell24 0
H bell24
measure bell24
cz bell24 x14
H 0
T* 0
cnot 1 0
T 0
cnot bell28 0
T* 0
cnot 1 0
T 0
cnot bell28 0
H 1
T* 1
cnot bell30 1
T 1
cnot bell32 1
T* 1
cnot bell30 1
T 1
cnot bell32 1
T 0
H bell38
cnot bell38 bell39
cnot 0 bell39
measure bell39
cnot bell39 bell38
cnot x12 bell38
H bell40
cnot bell40 bell41
cnot bell38 bell41
measure bell41
cnot bell41 bell40
reset bell41
cnot 0 bell40
cnot bell40 0
H bell40
measure bell40
cz bell40 x12
H bell38
measure bell38
cz bell38 0
T* 0
cnot bell32 0
T 0
cnot bell30 0
T* 0
cnot bell32 0
H 0
T x14
H x14
T x14
H bell42
cnot bell42 bell43
cnot 0 bell43
measure bell43
cnot bell43 bell42
cnot bell42 x14
T* x14
cnot x13 x14
T x14
cnot bell42 x14
H bell42
measure bell42
cz bell42 0
T* x14
cnot x13 x14
H x14
T 0
cnot bell28 0
T* 0
cnot bell28 0
H bell28
measure bell28
cz bell28 x13
H 0
T* 0
cnot bell30 0
H bell30
measure bell30
cz bell30 x12
T 0
cnot bell32 0
T* 0
H bell44
cnot bell44 bell45
cnot 0 bell45
measure bell45
cnot bell45 bell44
cnot x12 bell44
H bell46
cnot bell46 bell47
cnot bell44 bell47
measure bell47
cnot bell47 bell46
reset bell47
cnot 0 bell46
cnot bell46 0
H bell46
measure bell46
cz bell46 x12
H bell44
measure bell44
cz bell44 0
T 0
cnot bell32 0
H bell32
measure bell32
cz bell32 x2
cnot x3 x13
T x13
cnot x3 x13
H x13
T x13
cnot x12 x13
T* x13
cnot x2 x13
T x13
cnot x12 x13
T* x13
cnot x2 x13
H x13
cnot x2 x12
H 7
T 7
cnot x1 7
T* 7
cnot x11 7
T 7
cnot x1 7
T* 7
cnot x11 7
H 7
T 6
cnot 7 6
T* 6
cnot x12 6
T 6
cnot 7 6
T* 6
cnot x12 6
H 6
T 5
cnot 6 5
T* 5
cnot x13 5
T 5
cnot 6 5
T* 5
cnot x13 5
H 5
T 4
H bell48
cnot bell48 bell49
cnot 5 bell49
measure bell49
cnot bell49 bell48
cnot bell48 4
T* 4
H bell50
cnot bell50 bell51
cnot x14 bell51
measure bell51
cnot bell51 bell50
cnot bell50 4
T 4
cnot bell48 4
T* 4
cnot bell50 4
H 4
T 3
cnot 4 3
T* 3
cnot x15 3
T 3
cnot 4 3
T* 3
cnot x15 3
H 3
T 2
cnot 3 2
T* 2
cnot x16 2
T 2
cnot 3 2
T* 2
cnot x16 2
H 2
T 1
cnot 2 1
T* 1
cnot x17 1
T 1
cnot 2 1
T* 1
cnot x17 1
H 1
T 0
cnot 1 0
T* 0
cnot x18 0
T 0
cnot 1 0
T* 0
cnot x18 0
H 0
T x20
cnot 0 x20
T* x20
cnot x19 x20
T x20
cnot 0 x20
T* x20
cnot x19 x20
H x20
T 0
cnot x19 0
T* 0
cnot x19 0
H 0
T* 0
cnot 1 0
T 0
cnot x18 0
T* 0
cnot 1 0
T 0
cnot x18 0
H 1
T* 1
cnot 2 1
T 1
cnot x17 1
T* 1
cnot 2 1
T 1
cnot x17 1
H 2
T* 2
cnot 3 2
T 2
cnot x16 2
T* 2
cnot 3 2
T 2
cnot x16 2
H 3
T* 3
cnot 4 3
T 3
cnot x15 3
T* 3
cnot 4 3
T 3
cnot x15 3
H 4
T* 4
cnot bell48 4
T 4
cnot bell50 4
T* 4
cnot bell48 4
H bell48
measure bell48
cz bell48 5
T 4
cnot bell50 4
H 5
T* 5
cnot 6 5
T 5
cnot x13 5
T* 5
cnot 6 5
T 5
cnot x13 5
H 6
T* 6
cnot 7 6
T 6
cnot x12 6
T* 6
cnot 7 6
T 6
cnot x12 6
H 7
T* 7
cnot x1 7
T 7
cnot x11 7
T* 7
cnot x1 7
T 7
cnot x11 7
H 7
T 6
cnot x1 6
T* 6
cnot x11 6
T 6
cnot x1 6
T* 6
cnot x11 6
H 6
T 5
cnot 6 5
T* 5
cnot x12 5
T 5
cnot 6 5
T* 5
cnot x12 5
H 5
T 4
H bell52
cnot bell52 bell53
cnot 5 bell53
measure bell53
cnot bell53 bell52
cnot bell52 4
T* 4
H bell54
cnot bell54 bell55
cnot x13 bell55
measure bell55
cnot bell55 bell54
cnot bell54 4
T 4
cnot bell52 4
T* 4
cnot bell54 4
H 4
T 3
cnot 4 3
T* 3
cnot bell50 3
T 3
cnot 4 3
T* 3
cnot bell50 3
H 3
T 2
cnot 3 2
T* 2
cnot x15 2
T 2
cnot 3 2
T* 2
cnot x15 2
H 2
T 1
cnot 2 1
T* 1
cnot x16 1
T 1
cnot 2 1
T* 1
cnot x16 1
H 1
T 0
cnot 1 0
T* 0
cnot x17 0
T 0
cnot 1 0
T* 0
cnot x17 0
H 0
T x19
H x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
T x19
cnot 0 x19
T* x19
cnot x18 x19
H x19
T 0
cnot x18 0
T* 0
cnot x18 0
H 0
T* 0
cnot 1 0
T 0
cnot x17 0
T* 0
cnot 1 0
T 0
cnot x17 0
H 1
T* 1
cnot 2 1
T 1
cnot x16 1
T* 1
cnot 2 1
T 1
cnot x16 1
H 2
T* 2
cnot 3 2
T 2
cnot x15 2
T* 2
cnot 3 2
T 2
cnot x15 2
H 3
T* 3
cnot 4 3
T 3
cnot bell50 3
T* 3
cnot 4 3
T 3
cnot bell50 3
H 4
T* 4
cnot bell52 4
T 4
cnot bell54 4
T* 4
cnot bell52 4
H bell52
measure bell52
cz bell52 5
T 4
cnot bell54 4
H 5
T* 5
cnot 6 5
T 5
cnot x12 5
T* 5
cnot 6 5
T 5
cnot x12 5
H 6
T* 6
cnot x1 6
T 6
cnot x11 6
T* 6
cnot x1 6
T 6
cnot x11 6
H 6
T 5
cnot x1 5
T* 5
cnot x11 5
T 5
cnot x1 5
T* 5
cnot x11 5
H 5
T 4
H bell56
cnot bell56 bell57
cnot 5 bell57
measure bell57
cnot bell57 bell56
cnot bell56 4
T* 4
H bell58
cnot bell58 bell59
cnot x12 bell59
measure bell59
cnot bell59 bell58
cnot bell58 4
T 4
cnot bell56 4
T* 4
cnot bell58 4
H 4
T 3
cnot 4 3
T* 3
cnot bell54 3
T 3
cnot 4 3
T* 3
cnot bell54 3
H 3
T 2
cnot 3 2
T* 2
cnot bell50 2
T 2
cnot 3 2
T* 2
cnot bell50 2
H 2
T 1
cnot 2 1
T* 1
cnot x15 1
T 1
cnot 2 1
T* 1
cnot x15 1
H 1
T 0
cnot 1 0
T* 0
cnot x16 0
T 0
cnot 1 0
T* 0
cnot x16 0
H 0
T x18
H x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
T x18
cnot 0 x18
T* x18
cnot x17 x18
H x18
T 0
cnot x17 0
T* 0
cnot x17 0
H 0
T* 0
cnot 1 0
T 0
cnot x16 0
T* 0
cnot 1 0
T 0
cnot x16 0
H 1
T* 1
cnot 2 1
T 1
cnot x15 1
T* 1
cnot 2 1
T 1
cnot x15 1
H 2
T* 2
cnot 3 2
T 2
cnot bell50 2
T* 2
cnot 3 2
T 2
cnot bell50 2
H 3
T* 3
cnot 4 3
T 3
cnot bell54 3
T* 3
cnot 4 3
T 3
cnot bell54 3
H 4
T* 4
cnot bell56 4
T 4
cnot bell58 4
T* 4
cnot bell56 4
H bell56
measure bell56
cz bell56 5
T 4
cnot bell58 4
H 5
T* 5
cnot x1 5
T 5
cnot x11 5
T* 5
cnot x1 5
T 5
cnot x11 5
H 5
T 4
H bell60
cnot bell60 bell61
cnot x1 bell61
measure bell61
cnot bell61 bell60
cnot bell60 4
T* 4
H bell62
cnot bell62 bell63
cnot x11 bell63
measure bell63
cnot bell63 bell62
cnot bell62 4
T 4
cnot bell60 4
T* 4
cnot bell62 4
H 4
T 3
cnot 4 3
T* 3
cnot bell58 3
T 3
cnot 4 3
T* 3
cnot bell58 3
H 3
T 2
cnot 3 2
T* 2
cnot bell54 2
T 2
cnot 3 2
T* 2
cnot bell54 2
H 2
T 1
cnot 2 1
T* 1
cnot bell50 1
T 1
cnot 2 1
T* 1
cnot bell50 1
H 1
T 0
cnot 1 0
T* 0
cnot x15 0
T 0
cnot 1 0
T* 0
cnot x15 0
H 0
T x17
H x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
T x17
cnot 0 x17
T* x17
cnot x16 x17
H x17
T 0
cnot x16 0
T* 0
cnot x16 0
H 0
T* 0
cnot 1 0
T 0
cnot x15 0
T* 0
cnot 1 0
T 0
cnot x15 0
H 1
T* 1
cnot 2 1
T 1
cnot bell50 1
T* 1
cnot 2 1
T 1
cnot bell50 1
H 2
T* 2
cnot 3 2
T 2
cnot bell54 2
T* 2
cnot 3 2
T 2
cnot bell54 2
H 3
T* 3
cnot 4 3
T 3
cnot bell58 3
T* 3
cnot 4 3
T 3
cnot bell58 3
H 4
T* 4
cnot bell60 4
T 4
cnot bell62 4
T* 4
cnot bell60 4
T 4
cnot bell62 4
H 4
T 3
cnot bell60 3
T* 3
cnot bell62 3
T 3
cnot bell60 3
T* 3
cnot bell62 3
H 3
T 2
cnot 3 2
T* 2
cnot bell58 2
T 2
cnot 3 2
T* 2
cnot bell58 2
H 2
T 1
cnot 2 1
T* 1
cnot bell54 1
T 1
cnot 2 1
T* 1
cnot bell54 1
H 1
T 0
cnot 1 0
T* 0
cnot bell50 0
T 0
cnot 1 0
T* 0
cnot bell50 0
H 0
T x16
H x16
T x16
cnot 0 x16
T* x16
cnot x15 x16
T x16
cnot 0 x16
T* x16
cnot x15 x16
H x16
T 0
cnot x15 0
T* 0
cnot x15 0
H 0
T* 0
cnot 1 0
T 0
cnot bell50 0
T* 0
cnot 1 0
T 0
cnot bell50 0
H 1
T* 1
cnot 2 1
T 1
cnot bell54 1
T* 1
cnot 2 1
T 1
cnot bell54 1
H 2
T* 2
cnot 3 2
T 2
cnot bell58 2
T* 2
cnot 3 2
T 2
cnot bell58 2
H 3
T* 3
cnot bell60 3
T 3
cnot bell62 3
T* 3
cnot bell60 3
T 3
cnot bell62 3
H 3
T 2
cnot bell60 2
T* 2
cnot bell62 2
T 2
cnot bell60 2
T* 2
cnot bell62 2
H 2
T 1
cnot 2 1
T* 1
cnot bell58 1
T 1
cnot 2 1
T* 1
cnot bell58 1
H 1
T 0
cnot 1 0
T* 0
cnot bell54 0
T 0
cnot 1 0
T* 0
cnot bell54 0
H 0
T x15
H x15
T x15
cnot 0 x15
T* x15
cnot bell50 x15
T x15
cnot 0 x15
T* x15
cnot bell50 x15
H x15
T 0
cnot bell50 0
T* 0
cnot bell50 0
H bell50
measure bell50
cz bell50 x14
H 0
T* 0
cnot 1 0
T 0
cnot bell54 0
T* 0
cnot 1 0
T 0
cnot bell54 0
H 1
T* 1
cnot 2 1
T 1
cnot bell58 1
T* 1
cnot 2 1
T 1
cnot bell58 1
H 2
T* 2
cnot bell60 2
T 2
cnot bell62 2
T* 2
cnot bell60 2
T 2
cnot bell62 2
H 2
T 1
cnot bell60 1
T* 1
cnot bell62 1
T 1
cnot bell60 1
T* 1
cnot bell62 1
H 1
T 0
cnot 1 0
T* 0
cnot bell58 0
T 0
cnot 1 0
T* 0
H bell64
cnot bell64 bell65
cnot 0 bell65
measure bell65
cnot bell65 bell64
cnot x12 bell64
H bell66
cnot bell66 bell67
cnot bell64 bell67
measure bell67
cnot bell67 bell66
reset bell67
cnot 0 bell66
cnot bell66 0
H bell66
measure bell66
cz bell66 x12
H bell64
measure bell64
cz bell64 0
H 0
T x14
H x14
T x14
H bell68
cnot bell68 bell69
cnot 0 bell69
measure bell69
cnot bell69 bell68
cnot bell68 x14
T* x14
cnot x13 x14
T x14
cnot bell68 x14
H bell68
measure bell68
cz bell68 0
T* x14
cnot x13 x14
H x14
T 0
cnot bell54 0
T* 0
cnot bell54 0
H bell54
measure bell54
cz bell54 x13
H 0
T* 0
cnot 1 0
T 0
H bell70
cnot bell70 bell71
cnot 0 bell71
measure bell71
cnot bell71 bell70
cnot x12 bell70
H bell72
cnot bell72 bell73
cnot bell70 bell73
measure bell73
cnot bell73 bell72
reset bell73
cnot 0 bell72
cnot bell72 0
H bell72
measure bell72
cz bell72 x12
H bell70
measure bell70
cz bell70 0
T* 0
cnot 1 0
T 0
cnot bell58 0
H 1
T* 1
cnot bell60 1
T 1
cnot bell62 1
T* 1
cnot bell60 1
T 1
cnot bell62 1
H 1
T 0
H bell74
cnot bell74 bell75
cnot 0 bell75
measure bell75
cnot bell75 bell74
cnot x1 bell74
H bell76
cnot bell76 bell77
cnot bell74 bell77
measure bell77
cnot bell77 bell76
reset bell77
cnot 0 bell76
cnot bell76 0
H bell76
measure bell76
cz bell76 x1
H bell74
measure bell74
cz bell74 0
T* 0
H bell78
cnot bell78 bell79
cnot 0 bell79
measure bell79
cnot bell79 bell78
cnot x11 bell78
H bell80
cnot bell80 bell81
cnot bell78 bell81
measure bell81
cnot bell81 bell80
reset bell81
cnot 0 bell80
cnot bell80 0
H bell80
measure bell80
cz bell80 x11
H bell78
measure bell78
cz bell78 0
T 0
H bell82
cnot bell82 bell83
cnot 0 bell83
measure bell83
cnot bell83 bell82
cnot x1 bell82
H bell84
cnot bell84 bell85
cnot bell82 bell85
measure bell85
cnot bell85 bell84
reset bell85
cnot 0 bell84
cnot bell84 0
H bell84
measure bell84
cz bell84 x1
H bell82
measure bell82
cz bell82 0
T* 0
cnot bell62 0
H 0
T x13
H x13
T x13
H bell86
cnot bell86 bell87
cnot 0 bell87
measure bell87
cnot bell87 bell86
cnot bell86 x13
T* x13
cnot x12 x13
T x13
cnot bell86 x13
H bell86
measure bell86
cz bell86 0
T* x13
cnot x12 x13
H x13
T 0
cnot bell58 0
T* 0
cnot bell58 0
H bell58
measure bell58
cz bell58 x12
H 0
T* 0
H bell88
cnot bell88 bell89
cnot 0 bell89
measure bell89
cnot bell89 bell88
cnot x1 bell88
H bell90
cnot bell90 bell91
cnot bell88 bell91
measure bell91
cnot bell91 bell90
reset bell91
cnot 0 bell90
cnot bell90 0
H bell90
measure bell90
cz bell90 x1
H bell88
measure bell88
cz bell88 0
T 0
H bell92
cnot bell92 bell93
cnot 0 bell93
measure bell93
cnot bell93 bell92
cnot x11 bell92
H bell94
cnot bell94 bell95
cnot bell92 bell95
measure bell95
cnot bell95 bell94
reset bell95
cnot 0 bell94
cnot bell94 0
H bell94
measure bell94
cz bell94 x11
H bell92
measure bell92
cz bell92 0
T* 0
cnot bell60 0
H bell60
measure bell60
cz bell60 x1
T 0
cnot bell62 0
H bell62
measure bell62
cz bell62 x11
H 0
cnot x2 x12
T x12
cnot x2 x12
H x12
T x12
cnot x1 x12
T* x12
cnot x11 x12
T x12
cnot x1 x12
T* x12
cnot x11 x12
H x12
T x1
T x11
cnot x1 x11
T* x11
T x2
T x3
T x4
T x5
T x6
T x7
T x8
T x9
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
reset bell72
reset bell73
reset bell74
reset bell75
reset bell76
reset bell77
reset bell78
reset bell79
reset bell80
reset bell81
reset bell82
reset bell83
reset bell84
reset bell85
reset bell86
reset bell87
reset bell88
reset bell89
reset bell90
reset bell91
reset bell92
reset bell93
reset bell94
reset bell95
END
