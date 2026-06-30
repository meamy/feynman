
# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/random1.qc):
#   Qubits: 6
#   cnot: 20
#   Depth: 16
#   T depth: 0
# Result (1.468ms):
#   Qubits: 6
#   cnot: 19
#   Depth: 16
#   T depth: 0


# Result Circuit
.v q0 q1 q2 q3 q4 q5
.i q0 q1 q2 q3 q4 q5
.o q0 q1 q2 q3 q4 q5
BEGIN 
cnot q1 q2
cnot q3 q1
cnot q1 q2
cnot q0 q1
cnot q4 q0
cnot q0 q1
cnot q2 q0
cnot q5 q4
cnot q4 q5
cnot q4 q3
cnot q3 q5
cnot q1 q0
cnot q0 q3
cnot q1 q0
cnot q0 q4
cnot q2 q0
cnot q0 q5
cnot q2 q0
cnot q5 q2
END
