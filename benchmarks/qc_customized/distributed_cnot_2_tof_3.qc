# Hyperedge cut (ebits): 2

# Actual ebits used (Synthesis): 2
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/tof_3.qc):
#   Qubits: 5
#   H: 6
#   T: 21
#   cnot: 18
#   Depth: 23
#   T depth: 10
# Result (9.073ms):
#   Qubits: 9
#   H: 10
#   T: 15
#   cnot: 20
#   cz: 2
#   measure: 4
#   reset: 4
#   Depth: 35
#   T depth: 12


# Result Circuit
.v 1 2 3 4 5 bell0 bell1 bell2 bell3
.i 1 2 3 4
.o 1 2 3 4 5
BEGIN 
H 5
T 5
H bell0
cnot bell0 bell1
cnot 1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 5
T* 5
H bell2
cnot bell2 bell3
cnot 2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 5
T 5
cnot bell0 5
T* 5
cnot bell2 5
H 5
H 4
T 4
cnot 3 4
T* 4
cnot 5 4
T 4
cnot 3 4
T* 4
cnot 5 4
H 4
T 5
cnot 3 5
T* 5
cnot 3 5
H 5
T* 5
cnot bell0 5
T 5
cnot bell2 5
T* 5
cnot bell0 5
H bell0
measure bell0
cz bell0 1
T 5
cnot bell2 5
H bell2
measure bell2
cz bell2 2
H 5
T 3
reset bell0
reset bell1
reset bell2
reset bell3
END
