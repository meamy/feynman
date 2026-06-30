# Hyperedge cut (ebits): 2

# Actual ebits used (Synthesis): 2
# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/cnot.qc):
#   Qubits: 4
#   cnot: 3
#   Depth: 3
#   T depth: 0
# Result (10.935ms):
#   Qubits: 8
#   H: 4
#   cnot: 9
#   cz: 2
#   measure: 4
#   reset: 4
#   Depth: 11
#   T depth: 0


# Result Circuit
.v a b c d bell0 bell1 bell2 bell3
.i a b c d
.o a b c d
BEGIN 
H bell0
cnot bell0 bell1
cnot c bell1
measure bell1
cnot bell1 bell0
cnot bell0 d
H bell0
measure bell0
cz bell0 c
H bell2
cnot bell2 bell3
cnot b bell3
measure bell3
cnot bell3 bell2
cnot bell2 d
H bell2
measure bell2
cz bell2 b
cnot a d
reset bell0
reset bell1
reset bell2
reset bell3
END
