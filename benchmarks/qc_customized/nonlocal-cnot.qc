# Hyperedge cut (ebits): 1

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/cnot.qc):
#   Qubits: 2
#   cnot: 1
#   Depth: 1
#   T depth: 0
# Result (9.482ms):
#   Qubits: 4
#   H: 4
#   cnot: 3
#   cz: 2
#   measure: 2
#   reset: 2
#   Depth: 10
#   T depth: 0


# Result Circuit
.v x y bell0 bell1
.i x y
.o x y
BEGIN 
H y
H bell0
cnot bell0 bell1
cnot y bell1
measure bell1
cnot bell1 bell0
cz x bell0
H bell0
measure bell0
cz bell0 y
H y
reset bell0
reset bell1
END
