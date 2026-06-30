# Hyperedge cut (ebits): 3

# Actual ebits used (Synthesis): 3
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/rc_adder_6.qc):
#   Qubits: 14
#   H: 22
#   T: 77
#   X: 8
#   cnot: 93
#   Depth: 93
#   T depth: 39
# Result (25.149ms):
#   Qubits: 20
#   H: 28
#   T: 47
#   cnot: 80
#   cz: 3
#   measure: 6
#   reset: 6
#   Depth: 98
#   T depth: 36


# Result Circuit
.v b0 a0 e b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z bell0 bell1 bell2 bell3 bell4 bell5
.i b0 a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z
.o b0 a0 e b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z
BEGIN 
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a2 b2
cnot a1 e
cnot a1 b1
H e
T e
cnot a0 e
T* e
cnot b0 e
T e
cnot a0 e
T* e
cnot b0 e
H e
cnot a2 a1
H a1
T a1
cnot b1 a1
T* a1
cnot e a1
T a1
cnot b1 a1
T* a1
cnot e a1
H a1
H bell0
cnot bell0 bell1
cnot a3 bell1
measure bell1
cnot bell1 bell0
cnot bell0 a2
H bell0
measure bell0
cz bell0 a3
H a2
T a2
cnot a1 a2
T* a2
cnot b2 a2
T a2
cnot a1 a2
T* a2
cnot b2 a2
H a2
cnot a4 a3
H a3
T a3
H bell2
cnot bell2 bell3
cnot a2 bell3
measure bell3
cnot bell3 bell2
cnot bell2 a3
T* a3
cnot b3 a3
T a3
cnot bell2 a3
T* a3
cnot b3 a3
H a3
cnot a5 a4
H a4
T a4
cnot a3 a4
T* a4
cnot b4 a4
T a4
cnot a3 a4
T* a4
cnot b4 a4
H a4
cnot a5 z
H z
T z
cnot a4 z
T* z
cnot b5 z
T z
cnot a4 z
T* z
cnot b5 z
H z
T a4
T b5
cnot e b1
cnot a4 b5
cnot a3 b4
cnot bell2 b3
cnot a1 b2
H a4
T* a4
cnot a3 a4
T a4
cnot b4 a4
T a4
cnot a3 a4
T* a4
cnot b4 a4
H a4
H a3
T* a3
cnot bell2 a3
T a3
cnot b3 a3
T a3
cnot bell2 a3
H bell2
measure bell2
cz bell2 a2
T* a3
cnot b3 a3
H a3
cnot a5 a4
H a2
T* a2
cnot a1 a2
T a2
cnot b2 a2
T a2
cnot a1 a2
T* a2
cnot b2 a2
H a2
cnot a4 a3
H a1
T* a1
cnot b1 a1
T* a1
cnot e a1
T a1
cnot b1 a1
T a1
cnot e a1
H a1
H bell4
cnot bell4 bell5
cnot a3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 a2
H bell4
measure bell4
cz bell4 a3
H e
T* e
cnot a0 e
T e
cnot b0 e
T* e
cnot a0 e
T e
cnot b0 e
H e
cnot a0 b0
T* b5
cnot a2 a1
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a2 b2
cnot a1 e
cnot a1 b1
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
END
