# Hyperedge cut (ebits metric): 2

# Qubit partition assignments:
#   QPU 0 (2 qubits): b c
#   QPU 1 (2 qubits): a d
# Total ebit cost (Synthesis): 2
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/test_circuit.qc):
#   Qubits: 4
#   T: 2
#   cnot: 6
#   Depth: 8
#   T depth: 2
# Result (4.411ms):
#   Qubits: 8
#   H: 4
#   T: 2
#   cnot: 12
#   cz: 2
#   measure: 4
#   reset: 4
#   Depth: 16
#   T depth: 2


# Result Circuit
.v a b c d bellA0 bellA1 bellA2 bellA3
.i a b c d
.o a b c d
BEGIN 
H bellA0
cnot bellA0 bellA1
cnot a bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot d bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 c
cnot b c
T c
cnot bellA2 c
T c
cnot bellA2 c
cnot bellA0 c
cnot b c
H bellA0
measure bellA0
cz bellA0 a
H bellA2
measure bellA2
cz bellA2 d
reset bellA0
reset bellA1
reset bellA2
reset bellA3
END
