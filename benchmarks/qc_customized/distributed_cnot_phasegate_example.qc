# Hyperedge cut (ebits): 1

# Actual ebits used (Synthesis): 1
# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/phasegate_example.qc):
#   Qubits: 3
#   T: 4
#   cnot: 6
#   Depth: 7
#   T depth: 4
# Result (10.181ms):
#   Qubits: 5
#   H: 2
#   Z: 1
#   cnot: 5
#   cz: 1
#   measure: 2
#   reset: 2
#   Depth: 10
#   T depth: 0


# Result Circuit
.v a b c bell0 bell1
.i a b c
.o a b c
BEGIN 
Z a
cnot b c
H bell0
cnot bell0 bell1
cnot a bell1
measure bell1
cnot bell1 bell0
cnot bell0 b
H bell0
measure bell0
cz bell0 a
reset bell0
reset bell1
END
