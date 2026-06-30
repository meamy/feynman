# Hyperedge cut (ebits): 4

# Actual ebits used (Synthesis): 4
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_5.qc):
#   Qubits: 9
#   H: 14
#   T: 84
#   cnot: 72
#   Depth: 91
#   T depth: 37
# Result (13.274ms):
#   Qubits: 17
#   H: 22
#   T: 40
#   cnot: 66
#   cz: 4
#   measure: 8
#   reset: 8
#   Depth: 92
#   T depth: 34


# Result Circuit
.v 1 2 3 4 5 6 7 8 9 bell0 bell1 bell2 bell3 bell4 bell5 bell6 bell7
.i 1 2 3 4 5 6 7 8 9
.o 1 2 3 4 5 6 7 8 9
BEGIN 
H 9
T 8
H bell0
cnot bell0 bell1
cnot 5 bell1
measure bell1
cnot bell1 bell0
cnot bell0 8
T* 8
cnot 9 8
T 8
cnot bell0 8
T* 8
cnot 9 8
H 8
T 7
cnot 4 7
T* 7
cnot 8 7
T 7
cnot 4 7
T* 7
cnot 8 7
H 7
T 6
H bell2
cnot bell2 bell3
cnot 3 bell3
measure bell3
cnot bell3 bell2
cnot bell2 6
T* 6
cnot 7 6
T 6
cnot bell2 6
T* 6
cnot 7 6
H 6
T 6
H bell4
cnot bell4 bell5
cnot 1 bell5
measure bell5
cnot bell5 bell4
cnot bell4 6
T* 6
H bell6
cnot bell6 bell7
cnot 2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 6
T 6
cnot bell4 6
T* 6
cnot bell6 6
H 6
cnot bell2 7
cnot 6 7
T* 7
cnot bell2 7
T 7
cnot 6 7
H 7
cnot 4 8
cnot 7 8
T* 8
cnot 4 8
T 8
cnot 7 8
H 8
cnot bell0 9
cnot 8 9
T* 9
cnot bell0 9
T 9
cnot 8 9
H 9
T* 8
cnot bell0 8
T 8
cnot bell0 8
H bell0
measure bell0
cz bell0 5
H 8
cnot 4 7
cnot 8 7
T 7
cnot 4 7
T* 7
cnot 8 7
H 7
cnot bell2 6
cnot 7 6
T 6
cnot bell2 6
T* 6
cnot 7 6
H 6
T* 6
cnot bell4 6
T 6
cnot bell6 6
T* 6
cnot bell4 6
H bell4
measure bell4
cz bell4 1
T 6
cnot bell6 6
H bell6
measure bell6
cz bell6 2
H 6
cnot bell2 7
cnot 6 7
T* 7
cnot bell2 7
T 7
cnot 6 7
H 7
cnot 4 8
cnot 7 8
T* 8
cnot 4 8
T 8
cnot 7 8
H 8
T* 6
cnot bell2 6
T 6
T* 7
cnot 4 7
T 7
cnot 4 7
cnot bell2 6
H bell2
measure bell2
cz bell2 3
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
reset bell6
reset bell7
END
