# Hyperedge cut (ebits): 11

# Actual ebits used (Synthesis): 20
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_mult_55.qc):
#   Qubits: 9
#   H: 14
#   T: 49
#   X: 8
#   cnot: 48
#   Depth: 43
#   T depth: 19
# Result (12.473ms):
#   Qubits: 49
#   H: 54
#   S: 1
#   T: 35
#   cnot: 100
#   cz: 20
#   measure: 40
#   reset: 40
#   swap: 3
#   Depth: 91
#   T depth: 20


# Result Circuit
.v x0 x1 x2 y0 y1 y2 y3 y4 y5 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell18 bell19 bell2 bell20 bell21 bell22 bell23 bell24 bell25 bell26 bell27 bell28 bell29 bell3 bell30 bell31 bell32 bell33 bell34 bell35 bell36 bell37 bell38 bell39 bell4 bell5 bell6 bell7 bell8 bell9
.i x0 x1 x2
.o x0 x1 x2 y0 y1 y2 y3 y4 y5
BEGIN 
H y4
T y4
H bell0
cnot bell0 bell1
cnot x0 bell1
measure bell1
cnot bell1 bell0
cnot bell0 y4
T* y4
H bell2
cnot bell2 bell3
cnot x2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 y4
T* y4
cnot bell0 y4
H bell0
measure bell0
cz bell0 x0
T y4
cnot bell2 y4
H bell2
measure bell2
cz bell2 x2
H y4
H y3
H y5
T y5
H bell4
cnot bell4 bell5
cnot x0 bell5
measure bell5
cnot bell5 bell4
cnot bell4 y5
T y5
H bell6
cnot bell6 bell7
cnot x2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 y5
T* y5
cnot bell4 y5
T* y5
cnot bell6 y5
H y5
T y3
H bell8
cnot bell8 bell9
cnot x1 bell9
measure bell9
cnot bell9 bell8
cnot bell8 y3
T* y3
H bell10
cnot bell10 bell11
cnot y4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 y3
T y3
cnot bell8 y3
T* y3
cnot bell10 y3
H bell10
measure bell10
cz bell10 y4
swap y0 y1
H y3
H bell12
cnot bell12 bell13
cnot y3 bell13
measure bell13
cnot bell13 bell12
cnot bell12 y0
H bell12
measure bell12
cz bell12 y3
H bell14
cnot bell14 bell15
cnot y3 bell15
measure bell15
cnot bell15 bell14
cnot bell14 y1
H bell14
measure bell14
cz bell14 y3
H bell16
cnot bell16 bell17
cnot y5 bell17
measure bell17
cnot bell17 bell16
cnot bell16 y4
H bell16
measure bell16
cz bell16 y5
swap y2 y3
swap y1 y3
H y0
H y3
T y3
cnot bell8 y3
T y3
H bell18
cnot bell18 bell19
cnot y5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 y3
T* y3
cnot bell8 y3
H bell8
measure bell8
cz bell8 x1
T* y3
cnot bell18 y3
H bell18
measure bell18
cz bell18 y5
H y3
T* y0
H bell20
cnot bell20 bell21
cnot x1 bell21
measure bell21
cnot bell21 bell20
cnot bell20 y0
T* y0
H bell22
cnot bell22 bell23
cnot y4 bell23
measure bell23
cnot bell23 bell22
cnot bell22 y0
T* y0
cnot bell20 y0
H bell20
measure bell20
cz bell20 x1
T* y0
cnot bell22 y0
H bell22
measure bell22
cz bell22 y4
H y0
T y5
H bell24
cnot bell24 bell25
cnot x1 bell25
measure bell25
cnot bell25 bell24
cnot bell24 y5
T y5
H bell26
cnot bell26 bell27
cnot y4 bell27
measure bell27
cnot bell27 bell26
cnot bell26 y5
T* y5
cnot bell24 y5
H bell24
measure bell24
cz bell24 x1
T y5
H bell28
cnot bell28 bell29
cnot y3 bell29
measure bell29
cnot bell29 bell28
cnot bell28 y1
H bell28
measure bell28
cz bell28 y3
cnot bell26 y5
H bell26
measure bell26
cz bell26 y4
H bell30
cnot bell30 bell31
cnot y2 bell31
measure bell31
cnot bell31 bell30
cnot bell30 y5
H bell30
measure bell30
cz bell30 y2
H y2
H y5
T* y5
cnot bell4 y5
T* y5
cnot bell6 y5
T y5
cnot bell4 y5
H bell4
measure bell4
cz bell4 x0
T y5
cnot bell6 y5
H bell6
measure bell6
cz bell6 x2
H y5
T* y2
H bell32
cnot bell32 bell33
cnot x1 bell33
measure bell33
cnot bell33 bell32
cnot bell32 y2
T y2
H bell34
cnot bell34 bell35
cnot y4 bell35
measure bell35
cnot bell35 bell34
cnot bell34 y2
T y2
cnot bell32 y2
H bell32
measure bell32
cz bell32 x1
T* y2
cnot bell34 y2
H bell34
measure bell34
cz bell34 y4
H y2
T x0
T* x2
H bell36
cnot bell36 bell37
cnot x0 bell37
measure bell37
cnot bell37 bell36
cnot bell36 x2
T x2
S y4
H bell38
cnot bell38 bell39
cnot y2 bell39
measure bell39
cnot bell39 bell38
cnot bell38 y5
H bell38
measure bell38
cz bell38 y2
cnot bell36 x2
H bell36
measure bell36
cz bell36 x0
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
