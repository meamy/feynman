# Hyperedge cut (ebits): 3

# Actual ebits used (Synthesis): 3
# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/example.qc):
#   Qubits: 3
#   H: 4
#   cnot: 6
#   Depth: 7
#   T depth: 0
# Result (9.943ms):
#   Qubits: 9
#   H: 10
#   cnot: 15
#   cz: 3
#   measure: 6
#   reset: 6
#   Depth: 26
#   T depth: 0


# Result Circuit
.v a b c bell0 bell1 bell2 bell3 bell4 bell5
.i a b c
.o a b c
BEGIN 
H a
H bell0
cnot bell0 bell1
cnot a bell1
measure bell1
cnot bell1 bell0
cnot bell0 b
H bell0
measure bell0
cz bell0 a
H a
cnot b c
H bell2
cnot bell2 bell3
cnot a bell3
measure bell3
cnot bell3 bell2
cnot bell2 b
H bell2
measure bell2
cz bell2 a
H a
cnot b c
H bell4
cnot bell4 bell5
cnot a bell5
measure bell5
cnot bell5 bell4
cnot bell4 b
H bell4
measure bell4
cz bell4 a
H a
cnot b c
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
END
