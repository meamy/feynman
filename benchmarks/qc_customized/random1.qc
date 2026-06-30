# Feynman -- quantum circuit toolkit
# Random CNOT circuit: 6 qubits, depth 20

.v q0 q1 q2 q3 q4 q5
.i q0 q1 q2 q3 q4 q5
.o q0 q1 q2 q3 q4 q5
BEGIN 
cnot q2 q5
cnot q2 q4
cnot q3 q2
cnot q2 q3
cnot q3 q0
cnot q1 q0
cnot q2 q1
cnot q0 q2
cnot q4 q1
cnot q0 q3
cnot q1 q0
cnot q1 q3
cnot q0 q5
cnot q4 q3
cnot q2 q3
cnot q5 q2
cnot q5 q3
cnot q5 q4
cnot q1 q2
cnot q0 q2
END
