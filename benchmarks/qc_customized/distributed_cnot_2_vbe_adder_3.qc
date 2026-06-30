# Hyperedge cut (ebits): 2

# Actual ebits used (Synthesis): 2
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/vbe_adder_3.qc):
#   Qubits: 10
#   H: 10
#   T: 70
#   cnot: 70
#   Depth: 70
#   T depth: 29
# Result (12.066ms):
#   Qubits: 14
#   H: 14
#   S: 6
#   T: 24
#   cnot: 52
#   cz: 2
#   measure: 4
#   reset: 4
#   Depth: 68
#   T depth: 17


# Result Circuit
.v 0 1 2 3 4 5 6 7 8 9 bell0 bell1 bell2 bell3
.i 0 1 2 3 4 5 6 7 8 9
.o 0 1 2 3 4 5 6 7 8 9
BEGIN 
H 3
H 6
H 9
cnot 1 3
T* 3
cnot 2 3
S 3
cnot 1 3
T* 3
cnot 0 3
cnot 1 3
T* 3
cnot 2 3
cnot 1 3
T 3
cnot 0 3
cnot 1 2
H 3
cnot 4 6
T* 6
cnot 5 6
S 6
cnot 4 6
T* 6
H bell0
cnot bell0 bell1
cnot 3 bell1
measure bell1
cnot bell1 bell0
cnot bell0 6
cnot 4 6
T* 6
cnot 5 6
cnot 4 6
T 6
cnot 4 5
cnot bell0 6
H 6
H bell2
cnot bell2 bell3
cnot 7 bell3
measure bell3
cnot bell3 bell2
cnot bell2 9
T* 9
cnot 8 9
S 9
cnot bell2 9
T* 9
cnot 6 9
cnot bell2 9
T* 9
cnot 8 9
cnot bell2 9
T 9
cnot bell2 8
cnot 6 8
cnot 6 9
H 9
T* 6
cnot 8 6
S* 6
cnot bell2 6
T 6
cnot 8 6
cnot bell2 6
H bell2
measure bell2
cz bell2 7
H 6
cnot bell0 6
T* 6
cnot 5 6
T 6
cnot bell0 6
S* 6
cnot 4 6
T 6
cnot 5 6
T 6
cnot 4 6
cnot bell0 5
H bell0
measure bell0
cz bell0 3
H 6
H 3
cnot 0 3
T* 3
cnot 2 3
T 3
cnot 0 3
S* 3
cnot 1 3
T 3
cnot 2 3
T 3
cnot 1 3
H 3
T 7
T 8
cnot 0 2
reset bell0
reset bell1
reset bell2
reset bell3
END
