# Hyperedge cut (ebits): 7

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/csum_mux_9.qc):
#   Qubits: 30
#   H: 28
#   T: 196
#   X: 28
#   cnot: 168
#   Depth: 53
#   T depth: 24
# Result (53.302ms):
#   Qubits: 44
#   H: 254
#   S: 28
#   T: 84
#   cnot: 21
#   cz: 177
#   measure: 14
#   reset: 14
#   Depth: 95
#   T depth: 15


# Result Circuit
.v c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 a0 a1 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 b0 b1 b2 b3 e70 e71 bell0 bell1 bell10 bell11 bell12 bell13 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 e70 e71
.o c00 c01 c10 c11 e10 e11 c20 c21 c30 c31 a0 a1 e30 e31 c40 c41 c50 c51 e50 e51 c60 c61 c70 c71 b0 b1 b2 b3 e70 e71
BEGIN 
H e10
H e11
H a0
H a1
H e30
H e31
H e50
H e51
H b0
H b1
H b2
H b3
H e70
H e71
S e10
H e10
cz c00 e10
cz c10 e10
H e10
T* e10
H e10
cz c00 e10
H e10
T* e10
H e10
cz c11 e10
cz c10 e10
H e10
T* e10
H e10
cz c00 e10
H e10
T e10
H e10
cz c11 e10
cz c00 e10
S e11
H e11
cz c01 e11
cz c10 e11
H e11
T* e11
H e11
cz c01 e11
H e11
T* e11
H e11
cz c11 e11
cz c10 e11
H e11
T* e11
H e11
cz c01 e11
H e11
T e11
H e11
cz c11 e11
cz c01 e11
S a0
H a0
cz c20 a0
cz c30 a0
H a0
T* a0
H a0
cz c20 a0
H a0
T* a0
H a0
cz c31 a0
cz c30 a0
H a0
T* a0
H a0
cz c20 a0
H a0
T a0
H a0
cz c20 a0
cz c31 a0
S a1
H a1
cz c21 a1
cz c30 a1
H a1
T* a1
H a1
cz c21 a1
H a1
T* a1
H a1
cz c31 a1
cz c30 a1
H a1
T* a1
H a1
cz c21 a1
H a1
T a1
H a1
cz c21 a1
cz c31 a1
S e50
H e50
cz c40 e50
cz c50 e50
H e50
T* e50
H e50
cz c40 e50
H e50
T* e50
H e50
cz c51 e50
cz c50 e50
H e50
T* e50
H e50
cz c40 e50
H e50
T e50
H e50
cz c51 e50
cz c40 e50
S e51
H e51
cz c41 e51
cz c50 e51
H e51
T* e51
H e51
cz c41 e51
H e51
T* e51
H e51
cz c51 e51
cz c50 e51
H e51
T* e51
H e51
cz c41 e51
H e51
T e51
H e51
cz c51 e51
cz c41 e51
S b0
H b0
cz c60 b0
cz c70 b0
H b0
T* b0
H b0
cz c60 b0
H b0
T* b0
H b0
cz c71 b0
cz c70 b0
H b0
T* b0
H b0
cz c60 b0
H b0
T b0
H b0
cz c60 b0
cz c71 b0
S b1
H b1
cz c61 b1
cz c70 b1
H b1
T* b1
H b1
cz c61 b1
H b1
T* b1
H b1
cz c71 b1
cz c70 b1
H b1
T* b1
H b1
cz c61 b1
H b1
T b1
H b1
cz c61 b1
cz c71 b1
S e30
H e30
cz a0 e30
H e30
T* e30
H e30
cz e10 e30
H e30
T* e30
H e30
cz a0 e30
cz a1 e30
H e30
T e30
H e30
cz e10 e30
H e30
T* e30
H e30
cz a1 e30
S e31
H e31
cz a0 e31
H e31
T* e31
H e31
cz e11 e31
H e31
T* e31
H e31
cz a0 e31
cz a1 e31
H e31
T e31
H e31
cz e11 e31
H e31
T* e31
H e31
cz a1 e31
S b2
H b2
cz b0 b2
H b2
T* b2
H b2
cz e50 b2
H b2
T* b2
H b2
cz b0 b2
cz b1 b2
H b2
T b2
H b2
cz e50 b2
H b2
T* b2
H b2
cz b1 b2
S b3
H b3
cz b0 b3
H b3
T* b3
H b3
cz e51 b3
H b3
T* b3
H b3
cz b0 b3
cz b1 b3
H b3
T b3
H b3
cz e51 b3
H b3
T* b3
H b3
cz b1 b3
S e70
H e70
H bell0
cnot bell0 bell1
cnot b2 bell1
measure bell1
cnot bell1 bell0
cz bell0 e70
H e70
T* e70
H e70
cz e30 e70
H e70
T* e70
H e70
cz bell0 e70
H bell2
cnot bell2 bell3
cnot b3 bell3
measure bell3
cnot bell3 bell2
cz bell2 e70
H e70
T e70
H e70
cz e30 e70
H e70
T* e70
H e70
cz bell2 e70
S e71
H e71
cz b2 e71
H e71
T* e71
H e71
H bell4
cnot bell4 bell5
cnot e31 bell5
measure bell5
cnot bell5 bell4
cz bell4 e71
H e71
T* e71
H e71
cz b2 e71
H bell0
measure bell0
cz bell0 b2
cz b3 e71
H e71
T e71
H e71
cz bell4 e71
H bell4
measure bell4
cz bell4 e31
H e71
T* e71
H e71
cz b3 e71
H bell2
measure bell2
cz bell2 b3
S c10
H c10
cz c00 c10
H c10
T c10
H c10
cz c01 c10
cz c00 c10
H c10
T c10
S c11
H c11
cz c00 c11
H c11
T* c11
H c11
cz c01 c11
cz c00 c11
H c11
T* c11
S c30
H c30
cz c20 c30
H c30
T c30
H c21
cz c30 c21
cz c20 c21
H c21
T c21
S c31
H c31
cz c20 c31
H c31
T* c31
H c31
cz c30 c31
cz c21 c31
H c31
T* c31
S c50
H c50
cz c40 c50
H c50
T c50
H c41
cz c50 c41
cz c40 c41
H c41
T c41
S c51
H c51
cz c40 c51
H c51
T* c51
H c51
cz c50 c51
cz c41 c51
H c51
T* c51
S c70
H c70
cz c60 c70
H c70
T c70
H c61
cz c70 c61
cz c60 c61
H c61
T c61
S c71
H c71
cz c60 c71
H c71
T* c71
H c71
cz c70 c71
cz c61 c71
H c71
T* c71
S a0
H e10
cz a0 e10
H e10
T e10
S a1
H a1
cz e10 a1
cz a0 a1
H a1
T* a1
H e11
cz a0 e11
H e11
T e11
H e11
cz e10 e11
cz a1 e11
H e11
T* e11
S b2
H e30
H bell6
cnot bell6 bell7
cnot b2 bell7
measure bell7
cnot bell7 bell6
cz bell6 e30
H e30
T e30
S b3
H b3
H bell8
cnot bell8 bell9
cnot e30 bell9
measure bell9
cnot bell9 bell8
cz bell8 b3
cz b2 b3
H b3
T* b3
H e31
cz bell6 e31
H e31
T e31
H e31
cz e30 e31
H bell10
cnot bell10 bell11
cnot b3 bell11
measure bell11
cnot bell11 bell10
cz bell10 e31
H bell10
measure bell10
cz bell10 b3
H e31
T* e31
S b0
H e50
cz b0 e50
H e50
T e50
S b1
H b1
cz e50 b1
cz b0 b1
H b1
T* b1
H e51
cz b0 e51
H e51
T e51
H e51
cz e50 e51
cz b1 e51
H e51
T* e51
H a1
cz e10 a1
H b3
cz bell8 b3
H bell8
measure bell8
cz bell8 e30
H b1
cz e50 b1
H b1
H c21
cz c30 c21
H c41
cz c50 c41
H c41
H c61
cz c70 c61
H c70
cz c60 c70
H c70
cz c60 c61
H c61
H c71
cz c61 c71
H c71
H c51
cz c41 c51
cz c40 c51
H c51
H c50
cz c40 c50
H c50
H c41
cz c40 c41
H c41
cz c20 c21
H c21
H c31
cz c21 c31
H c31
H c30
cz c20 c30
H c30
H c10
cz c01 c10
H c10
H c11
cz c01 c11
H c11
cz b2 b3
H b3
H e51
cz b1 e51
H e31
H bell12
cnot bell12 bell13
cnot b3 bell13
measure bell13
cnot bell13 bell12
cz bell12 e31
H bell12
measure bell12
cz bell12 b3
H e31
H e30
cz bell6 e30
H bell6
measure bell6
cz bell6 b2
H e30
cz a0 a1
H a1
cz b0 e51
H e51
H e50
cz b0 e50
H e50
H e11
cz a1 e11
H e11
H e10
cz a0 e10
H e10
H b1
cz b0 b1
H b1
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
END
