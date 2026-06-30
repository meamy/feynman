# Hyperedge cut (ebits): 9

# Actual ebits used (Synthesis): 9
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
# Result (30.171ms):
#   Qubits: 32
#   H: 40
#   T: 47
#   cnot: 98
#   cz: 9
#   measure: 18
#   reset: 18
#   Depth: 122
#   T depth: 36


# Result Circuit
.v b0 a0 e b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell16 bell17 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i b0 a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z
.o b0 a0 e b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 z
BEGIN 
cnot a5 b5
cnot a4 b4
cnot a3 b3
cnot a2 b2
H bell0
cnot bell0 bell1
cnot a1 bell1
measure bell1
cnot bell1 bell0
cnot bell0 e
H bell0
measure bell0
cz bell0 a1
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
H bell2
cnot bell2 bell3
cnot e bell3
measure bell3
cnot bell3 bell2
cnot bell2 a1
T a1
cnot b1 a1
T* a1
cnot bell2 a1
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
H bell6
cnot bell6 bell7
cnot a2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 a3
T* a3
cnot b3 a3
T a3
cnot bell6 a3
T* a3
cnot b3 a3
H a3
H bell8
cnot bell8 bell9
cnot a5 bell9
measure bell9
cnot bell9 bell8
cnot bell8 a4
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
H bell10
cnot bell10 bell11
cnot a4 bell11
measure bell11
cnot bell11 bell10
cnot bell10 z
T* z
cnot b5 z
T z
cnot bell10 z
H bell10
measure bell10
cz bell10 a4
T* z
cnot b5 z
H z
T a4
T b5
cnot bell2 b1
H bell12
cnot bell12 bell13
cnot a4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 b5
H bell12
measure bell12
cz bell12 a4
cnot a3 b4
cnot bell6 b3
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
cnot bell6 a3
T a3
cnot b3 a3
T a3
cnot bell6 a3
H bell6
measure bell6
cz bell6 a2
T* a3
cnot b3 a3
H a3
cnot bell8 a4
H bell8
measure bell8
cz bell8 a5
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
cnot bell2 a1
T a1
cnot b1 a1
T a1
cnot bell2 a1
H bell2
measure bell2
cz bell2 e
H a1
H bell14
cnot bell14 bell15
cnot a3 bell15
measure bell15
cnot bell15 bell14
cnot bell14 a2
H bell14
measure bell14
cz bell14 a3
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
H bell16
cnot bell16 bell17
cnot a1 bell17
measure bell17
cnot bell17 bell16
cnot bell16 e
H bell16
measure bell16
cz bell16 a1
cnot a1 b1
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
reset bell6
reset bell7
reset bell8
reset bell9
reset bell10
reset bell11
reset bell12
reset bell13
reset bell14
reset bell15
reset bell16
reset bell17
END
