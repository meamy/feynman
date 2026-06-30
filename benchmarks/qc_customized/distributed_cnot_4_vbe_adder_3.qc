# Hyperedge cut (ebits): 5

# Actual ebits used (Synthesis): 6
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/vbe_adder_3.qc):
#   Qubits: 10
#   H: 10
#   T: 70
#   cnot: 70
#   Depth: 70
#   T depth: 29
# Result (12.936ms):
#   Qubits: 22
#   H: 22
#   S: 6
#   T: 24
#   cnot: 64
#   cz: 6
#   measure: 12
#   reset: 12
#   Depth: 81
#   T depth: 17


# Result Circuit
.v 0 1 2 3 4 5 6 7 8 9 bell0 bell1 bell10 bell11 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i 0 1 2 3 4 5 6 7 8 9
.o 0 1 2 3 4 5 6 7 8 9
BEGIN 
H 3
H 6
H 9
H bell0
cnot bell0 bell1
cnot 1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 3
T* 3
cnot 2 3
S 3
cnot bell0 3
T* 3
cnot 0 3
cnot bell0 3
T* 3
cnot 2 3
cnot bell0 3
T 3
cnot 0 3
cnot bell0 2
H 3
cnot 4 6
T* 6
cnot 5 6
S 6
cnot 4 6
T* 6
H bell2
cnot bell2 bell3
cnot 3 bell3
measure bell3
cnot bell3 bell2
cnot bell2 6
cnot 4 6
T* 6
cnot 5 6
cnot 4 6
T 6
cnot 4 5
cnot bell2 6
H 6
H bell4
cnot bell4 bell5
cnot 7 bell5
measure bell5
cnot bell5 bell4
cnot bell4 9
T* 9
cnot 8 9
S 9
cnot bell4 9
T* 9
H bell6
cnot bell6 bell7
cnot 6 bell7
measure bell7
cnot bell7 bell6
cnot bell6 9
cnot bell4 9
T* 9
cnot 8 9
cnot bell4 9
T 9
cnot bell4 8
H bell4
measure bell4
cz bell4 7
cnot bell6 8
cnot bell6 9
H bell6
measure bell6
cz bell6 6
H 9
T* 6
H bell8
cnot bell8 bell9
cnot 8 bell9
measure bell9
cnot bell9 bell8
cnot bell8 6
S* 6
H bell10
cnot bell10 bell11
cnot 7 bell11
measure bell11
cnot bell11 bell10
cnot bell10 6
T 6
cnot bell8 6
H bell8
measure bell8
cz bell8 8
cnot bell10 6
H bell10
measure bell10
cz bell10 7
H 6
cnot bell2 6
T* 6
cnot 5 6
T 6
cnot bell2 6
S* 6
cnot 4 6
T 6
cnot 5 6
T 6
cnot 4 6
cnot bell2 5
H bell2
measure bell2
cz bell2 3
H 6
H 3
cnot 0 3
T* 3
cnot 2 3
T 3
cnot 0 3
S* 3
cnot bell0 3
T 3
cnot 2 3
T 3
cnot bell0 3
H bell0
measure bell0
cz bell0 1
H 3
T 7
T 8
cnot 0 2
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
END
