# Hyperedge cut (ebits): 3

# Actual ebits used (Synthesis): 3
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_4.qc):
#   Qubits: 7
#   H: 10
#   T: 56
#   cnot: 48
#   Depth: 61
#   T depth: 25
# Result (13.201ms):
#   Qubits: 13
#   H: 16
#   T: 28
#   cnot: 45
#   cz: 3
#   measure: 6
#   reset: 6
#   Depth: 68
#   T depth: 26


# Result Circuit
.v 1 2 3 4 5 6 7 bell0 bell1 bell2 bell3 bell4 bell5
.i 1 2 3 4 5 6 7
.o 1 2 3 4 5 6 7
BEGIN 
H 7
T 6
H bell0
cnot bell0 bell1
cnot 4 bell1
measure bell1
cnot bell1 bell0
cnot bell0 6
T* 6
cnot 7 6
T 6
cnot bell0 6
T* 6
cnot 7 6
H 6
T 5
cnot 3 5
T* 5
cnot 6 5
T 5
cnot 3 5
T* 5
cnot 6 5
H 5
T 5
H bell2
cnot bell2 bell3
cnot 1 bell3
measure bell3
cnot bell3 bell2
cnot bell2 5
T* 5
H bell4
cnot bell4 bell5
cnot 2 bell5
measure bell5
cnot bell5 bell4
cnot bell4 5
T 5
cnot bell2 5
T* 5
cnot bell4 5
H 5
cnot 3 6
cnot 5 6
T* 6
cnot 3 6
T 6
cnot 5 6
H 6
cnot bell0 7
cnot 6 7
T* 7
cnot bell0 7
T 7
cnot 6 7
H 7
T* 6
cnot bell0 6
T 6
cnot bell0 6
H bell0
measure bell0
cz bell0 4
H 6
cnot 3 5
cnot 6 5
T 5
cnot 3 5
T* 5
cnot 6 5
H 5
T* 5
cnot bell2 5
T 5
cnot bell4 5
T* 5
cnot bell2 5
H bell2
measure bell2
cz bell2 1
T 5
cnot bell4 5
H bell4
measure bell4
cz bell4 2
H 5
cnot 3 6
cnot 5 6
T* 6
cnot 3 6
T 6
cnot 5 6
H 6
T* 5
cnot 3 5
T 5
cnot 3 5
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
END
