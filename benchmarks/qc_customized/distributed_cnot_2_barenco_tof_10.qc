# Hyperedge cut (ebits): 5

# Actual ebits used (Synthesis): 5
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_10.qc):
#   Qubits: 19
#   H: 34
#   T: 224
#   cnot: 192
#   Depth: 241
#   T depth: 97
# Result (35.473ms):
#   Qubits: 29
#   H: 44
#   T: 100
#   cnot: 159
#   cz: 5
#   measure: 10
#   reset: 10
#   Depth: 254
#   T depth: 81


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 bell0 bell1 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
.o 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
BEGIN 
H 19
T 18
cnot 10 18
T* 18
cnot 19 18
T 18
cnot 10 18
T* 18
cnot 19 18
H 18
T 17
cnot 18 17
T* 17
cnot 9 17
T 17
cnot 18 17
T* 17
cnot 9 17
H 17
T 16
cnot 17 16
T* 16
cnot 8 16
T 16
cnot 17 16
T* 16
cnot 8 16
H 16
T 15
cnot 16 15
T* 15
cnot 7 15
T 15
cnot 16 15
T* 15
cnot 7 15
H 15
T 14
H bell0
cnot bell0 bell1
cnot 15 bell1
measure bell1
cnot bell1 bell0
cnot bell0 14
T* 14
cnot 6 14
T 14
cnot bell0 14
H bell0
measure bell0
cz bell0 15
T* 14
cnot 6 14
H 14
T 13
cnot 14 13
T* 13
cnot 5 13
T 13
cnot 14 13
T* 13
cnot 5 13
H 13
T 12
cnot 13 12
T* 12
cnot 4 12
T 12
cnot 13 12
T* 12
cnot 4 12
H 12
T 11
cnot 12 11
T* 11
cnot 3 11
T 11
cnot 12 11
T* 11
cnot 3 11
H 11
T 11
cnot 1 11
T* 11
cnot 2 11
T 11
cnot 1 11
T* 11
cnot 2 11
H 11
cnot 11 12
T 12
cnot 3 12
T* 12
cnot 11 12
cnot 3 12
H 12
cnot 12 13
T 13
cnot 4 13
T* 13
cnot 12 13
cnot 4 13
H 13
cnot 13 14
T 14
cnot 5 14
T* 14
cnot 13 14
cnot 5 14
H 14
H bell2
cnot bell2 bell3
cnot 14 bell3
measure bell3
cnot bell3 bell2
cnot bell2 15
T 15
H bell4
cnot bell4 bell5
cnot 6 bell5
measure bell5
cnot bell5 bell4
cnot bell4 15
T* 15
cnot bell2 15
H bell2
measure bell2
cz bell2 14
cnot bell4 15
H 15
cnot 15 16
T 16
cnot 7 16
T* 16
cnot 15 16
cnot 7 16
H 16
cnot 16 17
T 17
cnot 8 17
T* 17
cnot 16 17
cnot 8 17
H 17
cnot 17 18
T 18
cnot 9 18
T* 18
cnot 17 18
cnot 9 18
H 18
cnot 10 19
cnot 18 19
T* 19
cnot 10 19
T 19
cnot 18 19
H 19
T* 18
cnot 10 18
T 18
cnot 10 18
H 18
cnot 18 17
T* 17
cnot 9 17
T 17
cnot 18 17
cnot 9 17
H 17
cnot 17 16
T* 16
cnot 8 16
T 16
cnot 17 16
cnot 8 16
H 16
cnot 16 15
T* 15
cnot 7 15
T 15
cnot 16 15
cnot 7 15
H 15
H bell6
cnot bell6 bell7
cnot 15 bell7
measure bell7
cnot bell7 bell6
cnot bell6 14
T* 14
cnot 6 14
T 14
cnot bell6 14
H bell6
measure bell6
cz bell6 15
cnot 6 14
H 14
cnot 14 13
T* 13
cnot 5 13
T 13
cnot 14 13
cnot 5 13
H 13
cnot 13 12
T* 12
cnot 4 12
T 12
cnot 13 12
cnot 4 12
H 12
cnot 12 11
T* 11
cnot 3 11
T 11
cnot 12 11
cnot 3 11
H 11
T* 11
cnot 1 11
T 11
cnot 2 11
T* 11
cnot 1 11
T 11
cnot 2 11
H 11
cnot 11 12
T 12
cnot 3 12
T* 12
cnot 11 12
cnot 3 12
H 12
cnot 12 13
T 13
cnot 4 13
T* 13
cnot 12 13
cnot 4 13
H 13
cnot 13 14
T 14
cnot 5 14
T* 14
cnot 13 14
cnot 5 14
H 14
H bell8
cnot bell8 bell9
cnot 14 bell9
measure bell9
cnot bell9 bell8
cnot bell8 15
T 15
cnot bell4 15
T* 15
cnot bell8 15
H bell8
measure bell8
cz bell8 14
cnot bell4 15
H bell4
measure bell4
cz bell4 6
H 15
cnot 15 16
T 16
cnot 7 16
T* 16
cnot 15 16
cnot 7 16
H 16
cnot 16 17
T 17
cnot 8 17
T* 17
cnot 16 17
cnot 8 17
H 17
cnot 17 18
T 18
cnot 9 18
T* 18
cnot 17 18
cnot 9 18
H 18
T* 11
cnot 11 3
T 3
T* 12
cnot 12 4
T 4
T* 13
cnot 13 5
T 5
T* 14
cnot 14 6
T 6
T* 15
cnot 15 7
T 7
T* 16
cnot 16 8
T 8
T* 17
cnot 17 9
T 9
cnot 17 9
cnot 16 8
cnot 15 7
cnot 14 6
cnot 13 5
cnot 12 4
cnot 11 3
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
END
