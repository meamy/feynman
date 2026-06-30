# Hyperedge cut (ebits metric): 36

# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_adder_1048576.qc):
#   Qubits: 58
#   H: 4940
#   T: 17290
#   cnot: 14840
#   Depth: 19508
#   T depth: 8708
# Result (10761.518ms):
#   Qubits: 78
#   H: 3716
#   S: 642
#   T: 15278
#   Z: 23
#   cnot: 17187
#   cz: 666
#   measure: 1298
#   reset: 1298
#   swap: 1532
#   Depth: 26342
#   T depth: 8720


# Result Circuit
.v x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 bellA0 bellA1 bellA10 bellA11 bellA12 bellA13 bellA2 bellA3 bellA4 bellA5 bellA6 bellA7 bellA8 bellA9 bellB0 bellB1 bellB2 bellB3 bellL0 bellL1
.i x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40
.o x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40
BEGIN 
cnot x20 x40
H x40
T x19
T x39
cnot x19 x39
T* x39
T x40
cnot x19 x40
T* x40
cnot x39 x40
T* x40
cnot x19 x40
T x40
cnot x39 x40
cnot x19 x39
cnot x19 x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x18 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x18
H bellA2
measure bellA2
cz bellA2 x38
T x18
T x38
cnot x18 x38
T* x38
cnot x18 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x18 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x18
H bellA2
measure bellA2
cz bellA2 x38
T x18
T x38
cnot x18 x38
T* x38
cnot x18 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x39
T x18
T x38
cnot x18 x38
T* x38
T x39
cnot x18 x39
T* x39
cnot x38 x39
T* x39
cnot x18 x39
T x39
cnot x38 x39
cnot x18 x38
H x39
cnot x18 x38
H 1
H bellA0
cnot bellA0 bellA1
cnot x17 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x37 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 1
cnot bellA0 1
T* 1
cnot bellA2 1
T* 1
cnot bellA0 1
T 1
cnot bellA2 1
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x17
H bellA2
measure bellA2
cz bellA2 x37
T x17
T x37
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x17 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x37 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
cnot 0 bellA2
T* bellA2
cnot 1 bellA2
cnot 0 bellA2
T* bellA2
cnot bellA0 bellA2
S* bellA2
cnot 0 bellA2
T bellA2
cnot 1 bellA2
cnot 0 bellA2
T bellA2
cnot bellA0 bellA2
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x17
H bellA2
measure bellA2
cz bellA2 x37
S x17
S x37
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x17 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x37 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T* 0
cnot bellA0 0
T 0
cnot bellA2 0
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x17
H bellA2
measure bellA2
cz bellA2 x37
T x17
T x37
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H bellA0
cnot bellA0 bellA1
cnot x17 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T* bellA0
H bellA0
measure bellA0
cz bellA0 x17
cz bellA0 x37
T x17
T x37
T x38
cnot x17 x38
T* x38
cnot x37 x38
T x38
cnot x17 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
H x38
cnot x17 x37
H 2
H bellA0
cnot bellA0 bellA1
cnot x16 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
cnot bellA0 2
T* 2
T x36
cnot 2 x36
T x36
cnot bellA0 x36
T* x36
cnot 2 x36
T* x36
cnot bellA0 2
cnot bellA0 x36
H bellA0
measure bellA0
cz bellA0 x16
T x16
reset bellA0
reset bellA1
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
H bellA0
cnot bellA0 bellA1
cnot x16 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x36
cnot 2 x36
T* x36
cnot bellA0 x36
S* x36
cnot 2 x36
T x36
cnot 1 x36
cnot 2 x36
T x36
cnot bellA0 x36
cnot 2 x36
T* x36
cnot 2 bellA0
cnot 1 x36
H bellA0
measure bellA0
cz bellA0 x16
S x16
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x16 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x36
cnot 1 x36
T* x36
cnot bellA0 x36
S* x36
cnot 1 x36
T x36
cnot 0 x36
cnot 1 x36
T x36
cnot bellA0 x36
cnot 1 x36
T* x36
cnot 0 x36
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x16
S x16
reset bellA0
reset bellA1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
H bellA0
cnot bellA0 bellA1
cnot x16 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x36
cnot 0 x36
T x36
cnot bellA0 x36
T* x36
cnot 0 x36
T* x36
cnot bellA0 0
cnot bellA0 x36
H bellA0
measure bellA0
cz bellA0 x16
T x16
reset bellA0
reset bellA1
H x37
H bellA0
cnot bellA0 bellA1
cnot x16 bellA1
measure bellA1
cnot bellA1 bellA0
T x36
cnot bellA0 x36
T* x36
cnot bellA0 x36
H bellA0
measure bellA0
cz bellA0 x16
H bellB0
cnot bellB0 bellB1
cnot x36 bellB1
measure bellB1
cnot bellB1 bellB0
T x16
T x37
cnot bellB0 x37
T* x37
cnot x16 x37
T x37
cnot bellB0 x37
T* x37
cnot x16 x37
H bellB0
measure bellB0
cz bellB0 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H x37
H bellL0
cnot bellL0 bellL1
cnot x16 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x36
H bellL0
measure bellL0
cz bellL0 x16
reset bellL0
reset bellL1
H 3
H bellA0
cnot bellA0 bellA1
cnot x15 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
cnot bellA0 3
T* 3
T x35
cnot 3 x35
T x35
cnot bellA0 x35
T* x35
cnot 3 x35
T* x35
cnot bellA0 3
cnot bellA0 x35
H bellA0
measure bellA0
cz bellA0 x15
T x15
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x15 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x35
cnot 3 x35
T* x35
cnot bellA0 x35
S* x35
cnot 3 x35
T x35
cnot 2 x35
cnot 3 x35
T x35
cnot bellA0 x35
cnot 3 x35
T* x35
cnot 2 x35
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x15
S x15
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x15 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x35
cnot 2 x35
T* x35
cnot bellA0 x35
S* x35
cnot 2 x35
T x35
cnot 1 x35
cnot 2 x35
T x35
cnot bellA0 x35
cnot 2 x35
T* x35
cnot 2 bellA0
cnot 1 x35
H bellA0
measure bellA0
cz bellA0 x15
S x15
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x15 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x35
cnot 1 x35
T* x35
cnot bellA0 x35
S* x35
cnot 1 x35
T x35
cnot 0 x35
cnot 1 x35
T x35
cnot bellA0 x35
cnot 1 x35
T* x35
cnot 0 x35
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x15
S x15
reset bellA0
reset bellA1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
H bellA0
cnot bellA0 bellA1
cnot x15 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x35
cnot 0 x35
T x35
cnot bellA0 x35
T* x35
cnot 0 x35
T* x35
cnot bellA0 0
cnot bellA0 x35
H bellA0
measure bellA0
cz bellA0 x15
T x15
reset bellA0
reset bellA1
H x36
H bellA0
cnot bellA0 bellA1
cnot x15 bellA1
measure bellA1
cnot bellA1 bellA0
T x35
cnot bellA0 x35
T* x35
T x36
cnot bellA0 x36
T* x36
cnot x35 x36
T* x36
cnot bellA0 x36
T x36
cnot x35 x36
cnot bellA0 x35
H bellA0
measure bellA0
cz bellA0 x15
T x15
reset bellA0
reset bellA1
H x36
H bellL0
cnot bellL0 bellL1
cnot x15 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x35
H bellL0
measure bellL0
cz bellL0 x15
reset bellL0
reset bellL1
H 4
H bellA0
cnot bellA0 bellA1
cnot x14 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
cnot bellA0 4
T* 4
T x34
cnot 4 x34
T x34
cnot bellA0 x34
T* x34
cnot 4 x34
T* x34
cnot bellA0 4
cnot bellA0 x34
H bellA0
measure bellA0
cz bellA0 x14
T x14
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x14 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
S x34
cnot 4 x34
T* x34
cnot bellA0 x34
S* x34
cnot 4 x34
T x34
cnot 3 x34
cnot 4 x34
T x34
cnot bellA0 x34
cnot 4 x34
T* x34
cnot 4 bellA0
cnot 3 x34
H bellA0
measure bellA0
cz bellA0 x14
S x14
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x14 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x34
cnot 3 x34
T* x34
cnot bellA0 x34
S* x34
cnot 3 x34
T x34
cnot 2 x34
cnot 3 x34
T x34
cnot bellA0 x34
cnot 3 x34
T* x34
cnot 2 x34
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x14
S x14
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x14 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x34
cnot 2 x34
T* x34
cnot bellA0 x34
S* x34
cnot 2 x34
T x34
cnot 1 x34
cnot 2 x34
T x34
cnot bellA0 x34
cnot 2 x34
T* x34
cnot 2 bellA0
cnot 1 x34
H bellA0
measure bellA0
cz bellA0 x14
S x14
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x14 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x34
cnot 1 x34
T* x34
cnot bellA0 x34
S* x34
cnot 1 x34
T x34
cnot 0 x34
cnot 1 x34
T x34
cnot bellA0 x34
cnot 1 x34
T* x34
cnot 0 x34
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x14
S x14
reset bellA0
reset bellA1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
H bellA0
cnot bellA0 bellA1
cnot x14 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x34
cnot 0 x34
T x34
cnot bellA0 x34
T* x34
cnot 0 x34
T* x34
cnot bellA0 0
cnot bellA0 x34
H bellA0
measure bellA0
cz bellA0 x14
T x14
reset bellA0
reset bellA1
H x35
H bellA0
cnot bellA0 bellA1
cnot x14 bellA1
measure bellA1
cnot bellA1 bellA0
T x34
cnot bellA0 x34
T* x34
T x35
cnot bellA0 x35
T* x35
cnot x34 x35
T* x35
cnot bellA0 x35
T x35
cnot x34 x35
cnot bellA0 x34
H bellA0
measure bellA0
cz bellA0 x14
T x14
reset bellA0
reset bellA1
H x35
H bellL0
cnot bellL0 bellL1
cnot x14 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x34
H bellL0
measure bellL0
cz bellL0 x14
reset bellL0
reset bellL1
H 5
T 5
T x13
cnot 5 x13
T* x13
T x33
cnot 5 x33
T* x33
cnot x13 x33
T* x33
cnot 5 x33
T x33
cnot x13 x33
cnot 5 x13
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 4
S x13
cnot 4 x13
T* x13
S x33
cnot 4 x33
T* x33
cnot x13 x33
S* x33
cnot 4 x33
T x33
T 5
cnot x13 5
cnot 4 5
T* 5
cnot x33 5
cnot 4 5
T* 5
cnot x13 5
cnot 4 5
T 5
cnot x33 5
cnot x13 x33
cnot 4 5
cnot 4 x13
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 3
S x13
cnot 3 x13
T* x13
S x33
cnot 3 x33
T* x33
cnot x13 x33
S* x33
cnot 3 x33
T x33
T 4
cnot x13 4
cnot 3 4
T* 4
cnot x33 4
cnot 3 4
T* 4
cnot x13 4
cnot 3 4
T 4
cnot x33 4
cnot x13 x33
cnot 3 x13
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 2
S x13
cnot 2 x13
T* x13
S x33
cnot 2 x33
T* x33
cnot x13 x33
S* x33
cnot 2 x33
T x33
T 3
cnot x13 3
cnot 2 3
T* 3
cnot x33 3
cnot 2 3
T* 3
cnot x13 3
cnot 2 3
T 3
cnot x33 3
cnot x13 x33
cnot 2 3
cnot 2 x13
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 1
S x13
cnot 1 x13
T* x13
S x33
cnot 1 x33
T* x33
cnot x13 x33
S* x33
cnot 1 x33
T x33
T 2
cnot x13 2
cnot 1 2
T* 2
cnot x33 2
cnot 1 2
T* 2
cnot x13 2
cnot 1 2
T 2
cnot x33 2
cnot x13 x33
cnot 1 x13
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 0
S x13
cnot 0 x13
T* x13
S x33
cnot 0 x33
T* x33
cnot x13 x33
S* x33
cnot 0 x33
T x33
T 1
cnot x13 1
cnot 0 1
T* 1
cnot x33 1
cnot 0 1
T* 1
cnot x13 1
cnot 0 1
T 1
cnot x33 1
cnot x13 x33
cnot 0 1
cnot 0 x13
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T x13
cnot 0 x13
T* x13
T x33
cnot 0 x33
T* x33
cnot x13 x33
T* x33
cnot 0 x33
T x33
cnot x13 x33
cnot 0 x13
H x34
T x13
T x33
cnot x13 x33
T* x33
T x34
cnot x13 x34
T* x34
cnot x33 x34
T* x34
cnot x13 x34
T x34
cnot x33 x34
cnot x13 x33
H x34
cnot x13 x33
H 6
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
T bellA0
cnot 6 bellA0
T* bellA0
T x32
cnot 6 x32
T* x32
cnot bellA0 x32
T* x32
cnot 6 x32
T x32
cnot bellA0 x32
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
S bellA0
cnot 5 bellA0
T* bellA0
S x32
cnot 5 x32
T* x32
cnot bellA0 x32
S* x32
cnot 5 x32
T x32
T 6
cnot bellA0 6
cnot 5 6
T* 6
cnot x32 6
cnot 5 6
T* 6
cnot bellA0 6
cnot 5 6
T 6
cnot x32 6
cnot bellA0 x32
cnot 5 6
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
S bellA0
cnot 4 bellA0
T* bellA0
S x32
cnot 4 x32
T* x32
cnot bellA0 x32
S* x32
cnot 4 x32
T x32
T 5
cnot bellA0 5
cnot 4 5
T* 5
cnot x32 5
cnot 4 5
T* 5
cnot bellA0 5
cnot 4 5
T 5
cnot x32 5
cnot bellA0 x32
cnot 4 5
cnot 4 bellA0
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
S bellA0
cnot 3 bellA0
T* bellA0
S x32
cnot 3 x32
T* x32
cnot bellA0 x32
S* x32
cnot 3 x32
T x32
T 4
cnot bellA0 4
cnot 3 4
T* 4
cnot x32 4
cnot 3 4
T* 4
cnot bellA0 4
cnot 3 4
T 4
cnot x32 4
cnot bellA0 x32
cnot 3 bellA0
cnot 3 4
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
S bellA0
cnot 2 bellA0
T* bellA0
S x32
cnot 2 x32
T* x32
cnot bellA0 x32
S* x32
cnot 2 x32
T x32
T 3
cnot bellA0 3
cnot 2 3
T* 3
cnot x32 3
cnot 2 3
T* 3
cnot bellA0 3
cnot 2 3
T 3
cnot x32 3
cnot bellA0 x32
cnot 2 3
cnot 2 bellA0
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
S bellA0
cnot 1 bellA0
T* bellA0
S x32
cnot 1 x32
T* x32
cnot bellA0 x32
S* x32
cnot 1 x32
T x32
T 2
cnot bellA0 2
cnot 1 2
T* 2
cnot x32 2
cnot 1 2
T* 2
cnot bellA0 2
cnot 1 2
T 2
cnot x32 2
cnot bellA0 x32
cnot 1 bellA0
cnot 1 2
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
S bellA0
cnot 0 bellA0
T* bellA0
S x32
cnot 0 x32
T* x32
cnot bellA0 x32
S* x32
cnot 0 x32
T x32
T 1
cnot bellA0 1
cnot 0 1
T* 1
cnot x32 1
cnot 0 1
T* 1
cnot bellA0 1
cnot 0 1
T 1
cnot x32 1
cnot bellA0 x32
cnot 0 1
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T bellA0
cnot 0 bellA0
T* bellA0
T x32
cnot 0 x32
T* x32
cnot bellA0 x32
T* x32
cnot 0 x32
T x32
cnot bellA0 x32
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H x33
H bellA0
cnot bellA0 bellA1
cnot x12 bellA1
measure bellA1
cnot bellA1 bellA0
T bellA0
T x32
cnot bellA0 x32
T* x32
T x33
cnot bellA0 x33
T* x33
cnot x32 x33
T* x33
cnot bellA0 x33
T x33
cnot x32 x33
cnot bellA0 x32
H bellA0
measure bellA0
cz bellA0 x12
reset bellA0
reset bellA1
H x33
H bellL0
cnot bellL0 bellL1
cnot x12 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x32
H bellL0
measure bellL0
cz bellL0 x12
reset bellL0
reset bellL1
H 7
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
cnot bellA0 7
T* 7
T x31
cnot 7 x31
T x31
cnot bellA0 x31
T* x31
cnot 7 x31
T* x31
cnot bellA0 7
cnot bellA0 x31
H bellA0
measure bellA0
cz bellA0 x11
T x11
reset bellA0
reset bellA1
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
T 7
cnot 6 bellA0
T* bellA0
cnot 7 bellA0
cnot 6 bellA0
T* bellA0
S x31
cnot 7 x31
T* x31
cnot bellA0 x31
S* x31
cnot 7 x31
T x31
cnot 6 x31
cnot 7 x31
T x31
cnot bellA0 x31
cnot 7 x31
T* x31
cnot 7 bellA0
cnot 6 x31
H bellA0
measure bellA0
cz bellA0 x11
S x11
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
T 6
cnot 5 bellA0
T* bellA0
cnot 6 bellA0
cnot 5 bellA0
T* bellA0
S x31
cnot 6 x31
T* x31
cnot bellA0 x31
S* x31
cnot 6 x31
T x31
cnot 5 x31
cnot 6 x31
T x31
cnot bellA0 x31
cnot 6 x31
T* x31
cnot 5 x31
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x11
S x11
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
T 5
cnot 4 bellA0
T* bellA0
cnot 5 bellA0
cnot 4 bellA0
T* bellA0
S x31
cnot 5 x31
T* x31
cnot bellA0 x31
S* x31
cnot 5 x31
T x31
cnot 4 x31
cnot 5 x31
T x31
cnot bellA0 x31
cnot 5 x31
T* x31
cnot 4 x31
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x11
S x11
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
S x31
cnot 4 x31
T* x31
cnot bellA0 x31
S* x31
cnot 4 x31
T x31
cnot 3 x31
cnot 4 x31
T x31
cnot bellA0 x31
cnot 4 x31
T* x31
cnot 4 bellA0
cnot 3 x31
H bellA0
measure bellA0
cz bellA0 x11
S x11
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x31
cnot 3 x31
T* x31
cnot bellA0 x31
S* x31
cnot 3 x31
T x31
cnot 2 x31
cnot 3 x31
T x31
cnot bellA0 x31
cnot 3 x31
T* x31
cnot 2 x31
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x11
S x11
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x31
cnot 2 x31
T* x31
cnot bellA0 x31
S* x31
cnot 2 x31
T x31
cnot 1 x31
cnot 2 x31
T x31
cnot bellA0 x31
cnot 2 x31
T* x31
cnot 2 bellA0
cnot 1 x31
H bellA0
measure bellA0
cz bellA0 x11
S x11
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x31
cnot 1 x31
T* x31
cnot bellA0 x31
S* x31
cnot 1 x31
T x31
cnot 0 x31
cnot 1 x31
T x31
cnot bellA0 x31
cnot 1 x31
T* x31
cnot 0 x31
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x11
S x11
reset bellA0
reset bellA1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x31
cnot 0 x31
T x31
cnot bellA0 x31
T* x31
cnot 0 x31
T* x31
cnot bellA0 0
cnot bellA0 x31
H bellA0
measure bellA0
cz bellA0 x11
T x11
reset bellA0
reset bellA1
H x32
H bellA0
cnot bellA0 bellA1
cnot x11 bellA1
measure bellA1
cnot bellA1 bellA0
T x31
cnot bellA0 x31
T* x31
T x32
cnot bellA0 x32
T* x32
cnot x31 x32
T* x32
cnot bellA0 x32
T x32
cnot x31 x32
cnot bellA0 x31
H bellA0
measure bellA0
cz bellA0 x11
T x11
reset bellA0
reset bellA1
H x32
H bellL0
cnot bellL0 bellL1
cnot x11 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x31
H bellL0
measure bellL0
cz bellL0 x11
reset bellL0
reset bellL1
H 8
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
cnot bellA0 8
T* 8
T x30
cnot 8 x30
T x30
cnot bellA0 x30
T* x30
cnot 8 x30
T* x30
cnot bellA0 8
cnot bellA0 x30
H bellA0
measure bellA0
cz bellA0 x10
T x10
reset bellA0
reset bellA1
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
T 8
cnot 7 bellA0
T* bellA0
cnot 8 bellA0
cnot 7 bellA0
T* bellA0
S x30
cnot 8 x30
T* x30
cnot bellA0 x30
S* x30
cnot 8 x30
T x30
cnot 7 x30
cnot 8 x30
T x30
cnot bellA0 x30
cnot 8 x30
T* x30
cnot 7 x30
cnot 8 bellA0
H bellA0
measure bellA0
cz bellA0 x10
S x10
reset bellA0
reset bellA1
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
T 7
cnot 6 bellA0
T* bellA0
cnot 7 bellA0
cnot 6 bellA0
T* bellA0
S x30
cnot 7 x30
T* x30
cnot bellA0 x30
S* x30
cnot 7 x30
T x30
cnot 6 x30
cnot 7 x30
T x30
cnot bellA0 x30
cnot 7 x30
T* x30
cnot 7 bellA0
cnot 6 x30
H bellA0
measure bellA0
cz bellA0 x10
S x10
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
T 6
cnot 5 bellA0
T* bellA0
cnot 6 bellA0
cnot 5 bellA0
T* bellA0
S x30
cnot 6 x30
T* x30
cnot bellA0 x30
S* x30
cnot 6 x30
T x30
cnot 5 x30
cnot 6 x30
T x30
cnot bellA0 x30
cnot 6 x30
T* x30
cnot 5 x30
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x10
S x10
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
T 5
cnot 4 bellA0
T* bellA0
cnot 5 bellA0
cnot 4 bellA0
T* bellA0
S x30
cnot 5 x30
T* x30
cnot bellA0 x30
S* x30
cnot 5 x30
T x30
cnot 4 x30
cnot 5 x30
T x30
cnot bellA0 x30
cnot 5 x30
T* x30
cnot 4 x30
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x10
S x10
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
S x30
cnot 4 x30
T* x30
cnot bellA0 x30
S* x30
cnot 4 x30
T x30
cnot 3 x30
cnot 4 x30
T x30
cnot bellA0 x30
cnot 4 x30
T* x30
cnot 4 bellA0
cnot 3 x30
H bellA0
measure bellA0
cz bellA0 x10
S x10
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x30
cnot 3 x30
T* x30
cnot bellA0 x30
S* x30
cnot 3 x30
T x30
cnot 2 x30
cnot 3 x30
T x30
cnot bellA0 x30
cnot 3 x30
T* x30
cnot 2 x30
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x10
S x10
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x30
cnot 2 x30
T* x30
cnot bellA0 x30
S* x30
cnot 2 x30
T x30
cnot 1 x30
cnot 2 x30
T x30
cnot bellA0 x30
cnot 2 x30
T* x30
cnot 2 bellA0
cnot 1 x30
H bellA0
measure bellA0
cz bellA0 x10
S x10
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x30
cnot 1 x30
T* x30
cnot bellA0 x30
S* x30
cnot 1 x30
T x30
cnot 0 x30
cnot 1 x30
T x30
cnot bellA0 x30
cnot 1 x30
T* x30
cnot 0 x30
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x10
S x10
reset bellA0
reset bellA1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x30
cnot 0 x30
T x30
cnot bellA0 x30
T* x30
cnot 0 x30
T* x30
cnot bellA0 0
cnot bellA0 x30
H bellA0
measure bellA0
cz bellA0 x10
T x10
reset bellA0
reset bellA1
H x31
H bellA0
cnot bellA0 bellA1
cnot x10 bellA1
measure bellA1
cnot bellA1 bellA0
T x30
cnot bellA0 x30
T* x30
T x31
cnot bellA0 x31
T* x31
cnot x30 x31
T* x31
cnot bellA0 x31
T x31
cnot x30 x31
cnot bellA0 x30
H bellA0
measure bellA0
cz bellA0 x10
T x10
reset bellA0
reset bellA1
H x31
H bellL0
cnot bellL0 bellL1
cnot x10 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x30
H bellL0
measure bellL0
cz bellL0 x10
reset bellL0
reset bellL1
H 9
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 9
cnot bellA0 9
T* 9
T x29
cnot 9 x29
T x29
cnot bellA0 x29
T* x29
cnot 9 x29
T* x29
T 8
cnot bellA0 9
cnot bellA0 x29
H bellA0
measure bellA0
cz bellA0 x9
T x9
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
reset bellA0
reset bellA1
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 9
cnot bellA0 9
T* 9
S x29
cnot 9 x29
T x29
cnot bellA0 x29
T* x29
cnot 9 x29
S* x29
T x30
cnot bellA0 x30
T* x30
cnot x29 x30
T* x30
cnot bellA0 x30
T x30
T 8
cnot bellA0 9
cnot x29 x30
cnot bellA0 x29
H bellA0
measure bellA0
cz bellA0 x9
S x9
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
reset bellA0
reset bellA1
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
cnot bellA0 8
T* 8
T x29
cnot 8 x29
T x29
cnot bellA0 x29
T* x29
cnot 8 x29
T* x29
cnot bellA0 8
cnot bellA0 x29
H bellA0
measure bellA0
cz bellA0 x9
T x9
reset bellA0
reset bellA1
H 8
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
cnot bellA0 7
T* 7
T x29
cnot 7 x29
T x29
cnot bellA0 x29
T* x29
cnot 7 x29
T* x29
cnot bellA0 7
cnot bellA0 x29
H bellA0
measure bellA0
cz bellA0 x9
T x9
reset bellA0
reset bellA1
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
T 7
cnot 6 bellA0
T* bellA0
cnot 7 bellA0
cnot 6 bellA0
T* bellA0
S x29
cnot 7 x29
T* x29
cnot bellA0 x29
S* x29
cnot 7 x29
T x29
cnot 6 x29
cnot 7 x29
T x29
cnot bellA0 x29
cnot 7 x29
T* x29
cnot 7 bellA0
cnot 6 x29
H bellA0
measure bellA0
cz bellA0 x9
S x9
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
T 6
cnot 5 bellA0
T* bellA0
cnot 6 bellA0
cnot 5 bellA0
T* bellA0
S x29
cnot 6 x29
T* x29
cnot bellA0 x29
S* x29
cnot 6 x29
T x29
cnot 5 x29
cnot 6 x29
T x29
cnot bellA0 x29
cnot 6 x29
T* x29
cnot 5 x29
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x9
S x9
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
T 5
cnot 4 bellA0
T* bellA0
cnot 5 bellA0
cnot 4 bellA0
T* bellA0
S x29
cnot 5 x29
T* x29
cnot bellA0 x29
S* x29
cnot 5 x29
T x29
cnot 4 x29
cnot 5 x29
T x29
cnot bellA0 x29
cnot 5 x29
T* x29
cnot 4 x29
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x9
S x9
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
S x29
cnot 4 x29
T* x29
cnot bellA0 x29
S* x29
cnot 4 x29
T x29
cnot 3 x29
cnot 4 x29
T x29
cnot bellA0 x29
cnot 4 x29
T* x29
cnot 4 bellA0
cnot 3 x29
H bellA0
measure bellA0
cz bellA0 x9
S x9
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x29
cnot 3 x29
T* x29
cnot bellA0 x29
S* x29
cnot 3 x29
T x29
cnot 2 x29
cnot 3 x29
T x29
cnot bellA0 x29
cnot 3 x29
T* x29
cnot 2 x29
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x9
S x9
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x29
cnot 2 x29
T* x29
cnot bellA0 x29
S* x29
cnot 2 x29
T x29
cnot 1 x29
cnot 2 x29
T x29
cnot bellA0 x29
cnot 2 x29
T* x29
cnot 2 bellA0
cnot 1 x29
H bellA0
measure bellA0
cz bellA0 x9
S x9
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x29
cnot 1 x29
T* x29
cnot bellA0 x29
S* x29
cnot 1 x29
T x29
cnot 0 x29
cnot 1 x29
T x29
cnot bellA0 x29
cnot 1 x29
T* x29
cnot 0 x29
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x9
S x9
reset bellA0
reset bellA1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x29
cnot 0 x29
T x29
cnot bellA0 x29
T* x29
cnot 0 x29
T* x29
cnot bellA0 0
cnot bellA0 x29
H bellA0
measure bellA0
cz bellA0 x9
T x9
reset bellA0
reset bellA1
H x30
H bellA0
cnot bellA0 bellA1
cnot x9 bellA1
measure bellA1
cnot bellA1 bellA0
T x29
cnot bellA0 x29
T* x29
T x30
cnot bellA0 x30
T* x30
cnot x29 x30
T* x30
cnot bellA0 x30
T x30
cnot x29 x30
cnot bellA0 x29
H bellA0
measure bellA0
cz bellA0 x9
T x9
reset bellA0
reset bellA1
H x30
H bellL0
cnot bellL0 bellL1
cnot x9 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x29
H bellL0
measure bellL0
cz bellL0 x9
reset bellL0
reset bellL1
H 10
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x8 bellA3
measure bellA3
cnot bellA3 bellA2
T 8
T 9
cnot 8 9
T* 9
T x29
cnot 8 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
T x29
T x28
cnot x28 bellA0
T* bellA0
cnot bellA0 bellA2
T bellA2
cnot x28 bellA2
T* bellA2
cnot bellA0 bellA2
T* bellA2
cnot x28 bellA0
cnot x28 bellA2
cnot 9 x29
cnot 8 9
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x8
T 10
T x8
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x8 bellA3
measure bellA3
cnot bellA3 bellA2
T 8
S 9
cnot 8 9
T* 9
T x29
cnot 8 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
T x29
S x28
cnot 9 x28
cnot 8 x28
T* x28
cnot x28 bellA2
T bellA2
cnot 9 bellA2
cnot 8 bellA2
S* bellA2
cnot bellA2 bellA0
T bellA0
cnot x28 bellA0
cnot 9 bellA0
cnot 8 bellA0
T* bellA0
cnot bellA2 bellA0
T* bellA0
cnot x28 bellA0
cnot x28 bellA2
cnot 9 x29
cnot 8 9
cnot 9 x28
cnot 9 bellA2
cnot 9 bellA0
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x8
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
T 10
S x8
cnot bellB0 x8
T* x8
cnot bellB0 x8
H bellB0
measure bellB0
cz bellB0 9
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 9
T x29
cnot bellA0 x29
T* x29
S x28
cnot 9 x28
T* x28
cnot bellA0 x28
T x28
cnot 9 x28
S* x28
cnot x29 x28
T* x28
cnot bellA0 x28
T x28
T 8
cnot x29 x28
cnot bellA0 x29
H bellA0
measure bellA0
cz bellA0 x8
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
S x8
cnot bellB0 x8
T* x8
cnot bellB0 x8
H bellB0
measure bellB0
cz bellB0 9
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 8
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
cnot bellA0 8
T* 8
T x28
cnot 8 x28
T x28
cnot bellA0 x28
T* x28
cnot 8 x28
T* x28
cnot bellA0 8
cnot bellA0 x28
H bellA0
measure bellA0
cz bellA0 x8
T x8
reset bellA0
reset bellA1
H 8
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
cnot bellA0 7
T* 7
T x28
cnot 7 x28
T x28
cnot bellA0 x28
T* x28
cnot 7 x28
T* x28
cnot bellA0 7
cnot bellA0 x28
H bellA0
measure bellA0
cz bellA0 x8
T x8
reset bellA0
reset bellA1
H 7
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
T 7
cnot 6 bellA0
T* bellA0
cnot 7 bellA0
cnot 6 bellA0
T* bellA0
S x28
cnot 7 x28
T* x28
cnot bellA0 x28
S* x28
cnot 7 x28
T x28
cnot 6 x28
cnot 7 x28
T x28
cnot bellA0 x28
cnot 7 x28
T* x28
cnot 7 bellA0
cnot 6 x28
H bellA0
measure bellA0
cz bellA0 x8
S x8
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
T 6
cnot 5 bellA0
T* bellA0
cnot 6 bellA0
cnot 5 bellA0
T* bellA0
S x28
cnot 6 x28
T* x28
cnot bellA0 x28
S* x28
cnot 6 x28
T x28
cnot 5 x28
cnot 6 x28
T x28
cnot bellA0 x28
cnot 6 x28
T* x28
cnot 5 x28
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x8
S x8
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
T 5
cnot 4 bellA0
T* bellA0
cnot 5 bellA0
cnot 4 bellA0
T* bellA0
S x28
cnot 5 x28
T* x28
cnot bellA0 x28
S* x28
cnot 5 x28
T x28
cnot 4 x28
cnot 5 x28
T x28
cnot bellA0 x28
cnot 5 x28
T* x28
cnot 4 x28
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x8
S x8
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
S x28
cnot 4 x28
T* x28
cnot bellA0 x28
S* x28
cnot 4 x28
T x28
cnot 3 x28
cnot 4 x28
T x28
cnot bellA0 x28
cnot 4 x28
T* x28
cnot 4 bellA0
cnot 3 x28
H bellA0
measure bellA0
cz bellA0 x8
S x8
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x28
cnot 3 x28
T* x28
cnot bellA0 x28
S* x28
cnot 3 x28
T x28
cnot 2 x28
cnot 3 x28
T x28
cnot bellA0 x28
cnot 3 x28
T* x28
cnot 2 x28
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x8
S x8
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x28
cnot 2 x28
T* x28
cnot bellA0 x28
S* x28
cnot 2 x28
T x28
cnot 1 x28
cnot 2 x28
T x28
cnot bellA0 x28
cnot 2 x28
T* x28
cnot 2 bellA0
cnot 1 x28
H bellA0
measure bellA0
cz bellA0 x8
S x8
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x28
cnot 1 x28
T* x28
cnot bellA0 x28
S* x28
cnot 1 x28
T x28
cnot 0 x28
cnot 1 x28
T x28
cnot bellA0 x28
cnot 1 x28
T* x28
cnot 0 x28
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x8
S x8
reset bellA0
reset bellA1
H 0
H x30
T 0
T x29
cnot 0 x29
T* x29
T x30
cnot 0 x30
T* x30
cnot x29 x30
T* x30
cnot 0 x30
T x30
cnot x29 x30
cnot 0 x29
H x30
H 0
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x28
cnot 0 x28
T x28
cnot bellA0 x28
T* x28
cnot 0 x28
T* x28
cnot bellA0 0
cnot bellA0 x28
H bellA0
measure bellA0
cz bellA0 x8
T x8
reset bellA0
reset bellA1
H x29
H bellA0
cnot bellA0 bellA1
cnot x8 bellA1
measure bellA1
cnot bellA1 bellA0
T x28
cnot bellA0 x28
T* x28
T x29
cnot bellA0 x29
T* x29
cnot x28 x29
T* x29
cnot bellA0 x29
T x29
cnot x28 x29
cnot bellA0 x28
H bellA0
measure bellA0
cz bellA0 x8
T x8
reset bellA0
reset bellA1
H x29
H bellL0
cnot bellL0 bellL1
cnot x8 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x28
H bellL0
measure bellL0
cz bellL0 x8
reset bellL0
reset bellL1
H 11
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x7 bellA3
measure bellA3
cnot bellA3 bellA2
S 8
T 9
cnot 8 9
T* 9
T x29
cnot 8 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
T x29
T x28
cnot 8 x28
T* x28
cnot 8 bellA0
T* bellA0
cnot x28 bellA0
T* bellA0
cnot 8 bellA0
T bellA0
T 11
T x27
cnot 11 x27
T* x27
cnot 11 bellA2
T* bellA2
cnot x27 bellA2
T* bellA2
cnot 11 bellA2
T bellA2
cnot x27 bellA2
cnot x28 bellA0
cnot 9 x29
cnot 8 9
cnot 8 x28
cnot 11 x27
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x7
T 10
T x7
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x7 bellA3
measure bellA3
cnot bellA3 bellA2
T* 8
Z 8
S 9
cnot 8 9
S* 9
S x28
cnot 8 x28
S* x28
cnot 9 x28
T* x28
cnot 8 x28
T x28
cnot 8 bellA0
T* bellA0
cnot x28 bellA0
cnot 9 bellA0
T bellA0
cnot 8 bellA0
T* bellA0
S x27
cnot x28 x27
cnot bellA0 x27
cnot 9 x27
T* x27
T 11
cnot x28 11
cnot x27 11
cnot bellA0 11
cnot 9 11
T* 11
cnot 11 bellA2
T bellA2
cnot x27 bellA2
cnot 11 bellA2
T bellA2
cnot x28 bellA2
cnot bellA0 bellA2
cnot 9 bellA2
S* bellA2
cnot 11 bellA2
T* bellA2
T x29
cnot 8 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
T x29
cnot x28 bellA0
cnot bellA0 x27
cnot 9 x29
cnot 9 x28
cnot 9 x27
cnot 9 bellA0
cnot 8 9
cnot x27 11
cnot 11 bellA2
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x7
S 10
S x7
cnot 10 x7
T* x7
cnot 10 x7
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x7 bellA3
measure bellA3
cnot bellA3 bellA2
T 8
S 9
cnot 8 9
T* 9
T x28
cnot 8 x28
T* x28
cnot 9 x28
T* x28
cnot 8 x28
T x28
S x27
cnot 9 x27
cnot 8 x27
T* x27
cnot x27 bellA2
T bellA2
cnot 9 bellA2
cnot 8 bellA2
S* bellA2
cnot bellA2 bellA0
T bellA0
cnot x27 bellA0
cnot bellA2 bellA0
cnot 9 bellA0
cnot 8 bellA0
T* bellA0
cnot x27 bellA0
cnot x27 bellA2
cnot 9 x28
cnot 8 9
cnot 9 x27
cnot 9 bellA2
cnot 9 bellA0
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x7
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
T 10
S x7
cnot 10 x7
T* x7
cnot bellB0 x7
cnot 10 x7
T* x7
cnot bellB0 x7
H bellB0
measure bellB0
cz bellB0 9
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 9
T x28
cnot bellA0 x28
T* x28
S x27
cnot 9 x27
T* x27
cnot bellA0 x27
T x27
cnot 9 x27
S* x27
cnot x28 x27
T* x27
cnot bellA0 x27
T x27
T 8
cnot x28 x27
cnot bellA0 x28
H bellA0
measure bellA0
cz bellA0 x7
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
S x7
cnot bellB0 x7
T* x7
cnot bellB0 x7
H bellB0
measure bellB0
cz bellB0 9
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 8
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
cnot bellA0 8
T* 8
T x27
cnot 8 x27
T x27
cnot bellA0 x27
T* x27
cnot 8 x27
T* x27
cnot bellA0 8
cnot bellA0 x27
H bellA0
measure bellA0
cz bellA0 x7
T x7
reset bellA0
reset bellA1
H 8
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
cnot bellA0 7
T* 7
T x27
cnot 7 x27
T x27
cnot bellA0 x27
T* x27
cnot 7 x27
T* x27
cnot bellA0 7
cnot bellA0 x27
H bellA0
measure bellA0
cz bellA0 x7
T x7
reset bellA0
reset bellA1
H 7
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
T 7
cnot 6 bellA0
T* bellA0
cnot 7 bellA0
cnot 6 bellA0
T* bellA0
S x27
cnot 7 x27
T* x27
cnot bellA0 x27
S* x27
cnot 7 x27
T x27
cnot 6 x27
cnot 7 x27
T x27
cnot bellA0 x27
cnot 7 x27
T* x27
cnot 7 bellA0
cnot 6 x27
H bellA0
measure bellA0
cz bellA0 x7
S x7
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
T 6
cnot 5 bellA0
T* bellA0
cnot 6 bellA0
cnot 5 bellA0
T* bellA0
S x27
cnot 6 x27
T* x27
cnot bellA0 x27
S* x27
cnot 6 x27
T x27
cnot 5 x27
cnot 6 x27
T x27
cnot bellA0 x27
cnot 6 x27
T* x27
cnot 5 x27
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x7
S x7
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
T 5
cnot 4 bellA0
T* bellA0
cnot 5 bellA0
cnot 4 bellA0
T* bellA0
S x27
cnot 5 x27
T* x27
cnot bellA0 x27
S* x27
cnot 5 x27
T x27
cnot 4 x27
cnot 5 x27
T x27
cnot bellA0 x27
cnot 5 x27
T* x27
cnot 4 x27
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x7
S x7
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
S x27
cnot 4 x27
T* x27
cnot bellA0 x27
S* x27
cnot 4 x27
T x27
cnot 3 x27
cnot 4 x27
T x27
cnot bellA0 x27
cnot 4 x27
T* x27
cnot 4 bellA0
cnot 3 x27
H bellA0
measure bellA0
cz bellA0 x7
S x7
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x27
cnot 3 x27
T* x27
cnot bellA0 x27
S* x27
cnot 3 x27
T x27
cnot 2 x27
cnot 3 x27
T x27
cnot bellA0 x27
cnot 3 x27
T* x27
cnot 2 x27
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x7
S x7
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x27
cnot 2 x27
T* x27
cnot bellA0 x27
S* x27
cnot 2 x27
T x27
cnot 1 x27
cnot 2 x27
T x27
cnot bellA0 x27
cnot 2 x27
T* x27
cnot 2 bellA0
cnot 1 x27
H bellA0
measure bellA0
cz bellA0 x7
S x7
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 0
H x30
T 0
T x29
cnot 0 x29
T* x29
T x30
cnot 0 x30
T* x30
cnot x29 x30
T* x30
cnot 0 x30
T x30
cnot x29 x30
cnot 0 x29
H x30
H 0
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x27
cnot 1 x27
T* x27
cnot bellA0 x27
S* x27
cnot 1 x27
T x27
cnot 0 x27
cnot 1 x27
T x27
cnot bellA0 x27
cnot 1 x27
T* x27
cnot 0 x27
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x7
S x7
reset bellA0
reset bellA1
H 0
H x29
T 0
T x28
cnot 0 x28
T* x28
T x29
cnot 0 x29
T* x29
cnot x28 x29
T* x29
cnot 0 x29
T x29
cnot x28 x29
cnot 0 x28
H x29
H 0
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x27
cnot 0 x27
T x27
cnot bellA0 x27
T* x27
cnot 0 x27
T* x27
cnot bellA0 0
cnot bellA0 x27
H bellA0
measure bellA0
cz bellA0 x7
T x7
reset bellA0
reset bellA1
H x28
H bellA0
cnot bellA0 bellA1
cnot x7 bellA1
measure bellA1
cnot bellA1 bellA0
T x27
cnot bellA0 x27
T* x27
T x28
cnot bellA0 x28
T* x28
cnot x27 x28
T* x28
cnot bellA0 x28
T x28
cnot x27 x28
cnot bellA0 x27
H bellA0
measure bellA0
cz bellA0 x7
T x7
reset bellA0
reset bellA1
H x28
H bellL0
cnot bellL0 bellL1
cnot x7 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x27
H bellL0
measure bellL0
cz bellL0 x7
reset bellL0
reset bellL1
H 12
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x6 bellA5
measure bellA5
cnot bellA5 bellA4
T 11
T* 8
Z 8
cnot 11 8
T* 8
T x27
cnot 11 x27
T* x27
cnot 8 x27
T* x27
cnot 11 x27
T x27
T 9
cnot 8 9
cnot 11 9
T* 9
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
cnot 11 x29
T x29
T x28
cnot 8 x28
cnot 11 x28
T* x28
cnot 8 bellA0
cnot 11 bellA0
T* bellA0
cnot x28 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
T x26
cnot x26 bellA2
T* bellA2
cnot bellA2 bellA4
T bellA4
cnot x26 bellA4
T* bellA4
cnot bellA2 bellA4
T* bellA4
cnot x28 bellA0
cnot x26 bellA2
cnot x26 bellA4
cnot 9 x29
cnot 8 9
cnot 8 x28
cnot 8 x27
cnot 11 x28
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x6
T 10
T 12
T x6
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x6 bellA5
measure bellA5
cnot bellA5 bellA4
S 11
T 8
Z 8
cnot 11 8
T* 8
S x27
cnot 11 x27
T* x27
cnot 8 x27
S* x27
cnot 11 x27
T x27
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x27 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x28
cnot 8 x28
cnot 11 x28
S* x28
cnot x27 x28
cnot bellA0 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x28 9
cnot x27 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot x28 x29
cnot x27 x29
cnot bellA0 x29
cnot 9 x29
cnot 11 x29
T x29
cnot 8 x29
cnot 11 x29
T* x29
S x26
cnot 11 x26
T* x26
cnot 11 bellA4
T* bellA4
cnot x26 bellA4
S* bellA4
cnot 11 bellA4
T bellA4
cnot bellA4 bellA2
cnot 11 bellA2
T bellA2
cnot x26 bellA2
cnot 11 bellA2
T* bellA2
cnot bellA4 bellA2
cnot 11 bellA2
T* bellA2
cnot x27 bellA0
cnot x26 bellA2
cnot x26 bellA4
cnot bellA0 x28
cnot x28 9
cnot 9 x29
cnot 8 x27
cnot 11 x29
cnot 11 x28
cnot 11 x26
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x6
S 10
T 12
S x6
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x6 bellA3
measure bellA3
cnot bellA3 bellA2
T 11
cnot 11 bellA2
T* bellA2
cnot bellA0 bellA2
cnot 11 bellA2
T* bellA2
S x26
cnot bellA0 x26
T* x26
cnot bellA2 x26
S* x26
cnot bellA0 x26
T x26
cnot 11 x26
cnot bellA0 x26
T x26
cnot bellA2 x26
cnot bellA0 x26
T* x26
T* 8
Z 8
cnot bellA0 8
T* 8
S x27
cnot 8 x27
T x27
cnot bellA0 x27
S* x27
cnot 8 x27
T* x27
S 9
cnot bellA0 9
cnot 8 9
S* 9
cnot x27 9
cnot 8 9
T* 9
cnot bellA0 9
cnot 8 9
T 9
T x28
cnot bellA0 x28
cnot 8 x28
T* x28
cnot x27 x28
cnot 9 x28
cnot 8 x28
T x28
cnot bellA0 x28
cnot 8 x28
T* x28
cnot bellA0 8
cnot bellA0 bellA2
cnot bellA0 x27
cnot x27 9
cnot 8 9
cnot 9 x28
cnot 11 x26
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x6
S 10
S x6
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x6 bellA3
measure bellA3
cnot bellA3 bellA2
T 8
S 9
cnot 8 9
T* 9
T x27
cnot 8 x27
T* x27
cnot 9 x27
T* x27
cnot 8 x27
T x27
S x26
cnot 9 x26
cnot 8 x26
T* x26
cnot 9 bellA2
cnot 8 bellA2
T* bellA2
cnot x26 bellA2
S* bellA2
cnot 9 bellA2
cnot 8 bellA2
T bellA2
cnot bellA2 bellA0
cnot 9 bellA0
cnot 8 bellA0
T bellA0
cnot x26 bellA0
cnot 9 bellA0
cnot 8 bellA0
T* bellA0
cnot bellA2 bellA0
cnot 9 bellA0
cnot 8 bellA0
T* bellA0
cnot x26 bellA0
cnot x26 bellA2
cnot 9 x27
cnot 8 9
cnot 9 x26
cnot 9 bellA0
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x6
T 10
S x6
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 9
cnot bellA0 9
T* 9
S x26
cnot 9 x26
T x26
cnot bellA0 x26
T* x26
cnot 9 x26
S* x26
T x27
cnot bellA0 x27
T* x27
cnot x26 x27
T* x27
cnot bellA0 x27
T x27
T 8
cnot bellA0 9
cnot x26 x27
cnot bellA0 x26
H bellA0
measure bellA0
cz bellA0 x6
S x6
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
reset bellA0
reset bellA1
H 8
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
cnot bellA0 8
T* 8
T x26
cnot 8 x26
T x26
cnot bellA0 x26
T* x26
cnot 8 x26
T* x26
cnot bellA0 8
cnot bellA0 x26
H bellA0
measure bellA0
cz bellA0 x6
T x6
reset bellA0
reset bellA1
H 8
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
cnot bellA0 7
T* 7
T x26
cnot 7 x26
T x26
cnot bellA0 x26
T* x26
cnot 7 x26
T* x26
cnot bellA0 7
cnot bellA0 x26
H bellA0
measure bellA0
cz bellA0 x6
T x6
reset bellA0
reset bellA1
H 7
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
T 7
cnot 6 bellA0
T* bellA0
cnot 7 bellA0
cnot 6 bellA0
T* bellA0
S x26
cnot 7 x26
T* x26
cnot bellA0 x26
S* x26
cnot 7 x26
T x26
cnot 6 x26
cnot 7 x26
T x26
cnot bellA0 x26
cnot 7 x26
T* x26
cnot 7 bellA0
cnot 6 x26
H bellA0
measure bellA0
cz bellA0 x6
S x6
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
T 6
cnot 5 bellA0
T* bellA0
cnot 6 bellA0
cnot 5 bellA0
T* bellA0
S x26
cnot 6 x26
T* x26
cnot bellA0 x26
S* x26
cnot 6 x26
T x26
cnot 5 x26
cnot 6 x26
T x26
cnot bellA0 x26
cnot 6 x26
T* x26
cnot 5 x26
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x6
S x6
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
T 5
cnot 4 bellA0
T* bellA0
cnot 5 bellA0
cnot 4 bellA0
T* bellA0
S x26
cnot 5 x26
T* x26
cnot bellA0 x26
S* x26
cnot 5 x26
T x26
cnot 4 x26
cnot 5 x26
T x26
cnot bellA0 x26
cnot 5 x26
T* x26
cnot 4 x26
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x6
S x6
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
S x26
cnot 4 x26
T* x26
cnot bellA0 x26
S* x26
cnot 4 x26
T x26
cnot 3 x26
cnot 4 x26
T x26
cnot bellA0 x26
cnot 4 x26
T* x26
cnot 4 bellA0
cnot 3 x26
H bellA0
measure bellA0
cz bellA0 x6
S x6
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x26
cnot 3 x26
T* x26
cnot bellA0 x26
S* x26
cnot 3 x26
T x26
cnot 2 x26
cnot 3 x26
T x26
cnot bellA0 x26
cnot 3 x26
T* x26
cnot 2 x26
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x6
S x6
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 0
H x30
T 0
T x29
cnot 0 x29
T* x29
T x30
cnot 0 x30
T* x30
cnot x29 x30
T* x30
cnot 0 x30
T x30
cnot x29 x30
cnot 0 x29
H x30
H 0
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x26
cnot 2 x26
T* x26
cnot bellA0 x26
S* x26
cnot 2 x26
T x26
cnot 1 x26
cnot 2 x26
T x26
cnot bellA0 x26
cnot 2 x26
T* x26
cnot 2 bellA0
cnot 1 x26
H bellA0
measure bellA0
cz bellA0 x6
S x6
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 0
H x29
T 0
T x28
cnot 0 x28
T* x28
T x29
cnot 0 x29
T* x29
cnot x28 x29
T* x29
cnot 0 x29
T x29
cnot x28 x29
cnot 0 x28
H x29
H 0
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x26
cnot 1 x26
T* x26
cnot bellA0 x26
S* x26
cnot 1 x26
T x26
cnot 0 x26
cnot 1 x26
T x26
cnot bellA0 x26
cnot 1 x26
T* x26
cnot 0 x26
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x6
S x6
reset bellA0
reset bellA1
H 0
H x28
T 0
T x27
cnot 0 x27
T* x27
T x28
cnot 0 x28
T* x28
cnot x27 x28
T* x28
cnot 0 x28
T x28
cnot x27 x28
cnot 0 x27
H x28
H 0
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x26
cnot 0 x26
T x26
cnot bellA0 x26
T* x26
cnot 0 x26
T* x26
cnot bellA0 0
cnot bellA0 x26
H bellA0
measure bellA0
cz bellA0 x6
T x6
reset bellA0
reset bellA1
H x27
H bellA0
cnot bellA0 bellA1
cnot x6 bellA1
measure bellA1
cnot bellA1 bellA0
T x26
cnot bellA0 x26
T* x26
T x27
cnot bellA0 x27
T* x27
cnot x26 x27
T* x27
cnot bellA0 x27
T x27
cnot x26 x27
cnot bellA0 x26
H bellA0
measure bellA0
cz bellA0 x6
T x6
reset bellA0
reset bellA1
H x27
H bellL0
cnot bellL0 bellL1
cnot x6 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x26
H bellL0
measure bellL0
cz bellL0 x6
reset bellL0
reset bellL1
H 13
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x5 bellA5
measure bellA5
cnot bellA5 bellA4
T 11
Z 8
cnot 11 8
T* 8
T x27
cnot 11 x27
T* x27
cnot 8 x27
T* x27
cnot 11 x27
T x27
T 9
cnot 8 9
cnot 11 9
T* 9
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
cnot 11 x29
T x29
T x28
cnot 8 x28
cnot 11 x28
T* x28
cnot 8 bellA0
cnot 11 bellA0
T* bellA0
cnot x28 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
T x26
cnot 8 x26
cnot 11 x26
T* x26
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot x26 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
T 13
T x25
cnot 13 x25
T* x25
cnot 13 bellA4
T* bellA4
cnot x25 bellA4
T* bellA4
cnot 13 bellA4
T bellA4
cnot x25 bellA4
cnot x26 bellA2
cnot x28 bellA0
cnot 9 x29
cnot 8 9
cnot 8 x28
cnot 8 x27
cnot 8 x26
cnot 13 x25
cnot 11 x28
cnot 11 x26
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x5
T 10
T 12
T x5
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x5 bellA5
measure bellA5
cnot bellA5 bellA4
S 11
T* 8
cnot 11 8
S* 8
S x26
cnot 11 x26
T* x26
cnot 8 x26
S* x26
cnot 11 x26
T x26
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot x26 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x25
cnot x26 x25
cnot bellA2 x25
cnot 11 x25
T* x25
cnot x25 bellA4
T bellA4
cnot x26 bellA4
cnot bellA2 bellA4
cnot 11 bellA4
S* bellA4
cnot x25 bellA4
T* bellA4
T 13
cnot x25 13
cnot bellA4 13
T 13
cnot x26 13
cnot bellA2 13
cnot 11 13
cnot bellA4 13
T* 13
cnot x25 13
cnot bellA4 13
T* 13
S x27
cnot 11 x27
T* x27
cnot 8 x27
S* x27
cnot 11 x27
T x27
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x27 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x28
cnot 8 x28
cnot 11 x28
S* x28
cnot x27 x28
cnot bellA0 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x28 9
cnot x27 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot x28 x29
cnot x27 x29
cnot bellA0 x29
cnot 9 x29
cnot 11 x29
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot x26 bellA2
cnot x27 bellA0
cnot bellA2 bellA4
cnot bellA0 x28
cnot bellA2 x25
cnot x28 9
cnot 9 x29
cnot 8 x27
cnot 8 x26
cnot bellA4 13
cnot 11 x29
cnot 11 x28
cnot 11 x25
cnot 11 bellA4
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x5
S 10
S 12
S x5
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x5 bellA5
measure bellA5
cnot bellA5 bellA4
S 11
T 8
Z 8
cnot 11 8
T* 8
S x26
cnot 11 x26
T* x26
cnot 8 x26
S* x26
cnot 11 x26
T x26
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x26 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x27
cnot 8 x27
cnot 11 x27
S* x27
cnot x26 x27
cnot bellA0 x27
cnot 11 x27
T x27
cnot 8 x27
cnot 11 x27
T* x27
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x27 9
cnot x26 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x28
cnot 8 x28
cnot 11 x28
T* x28
cnot x27 x28
cnot x26 x28
cnot bellA0 x28
cnot 9 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
S x25
cnot 11 x25
T* x25
cnot 11 bellA4
T* bellA4
cnot x25 bellA4
S* bellA4
cnot 11 bellA4
T bellA4
cnot bellA4 bellA2
cnot 11 bellA2
T bellA2
cnot x25 bellA2
cnot 11 bellA2
T* bellA2
cnot bellA4 bellA2
cnot 11 bellA2
T* bellA2
cnot x26 bellA0
cnot x25 bellA2
cnot x25 bellA4
cnot bellA0 x27
cnot x27 9
cnot 9 x28
cnot 8 x26
cnot 11 x28
cnot 11 x27
cnot 11 x25
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x5
S 10
T 12
S x5
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x5 bellA3
measure bellA3
cnot bellA3 bellA2
T* 8
Z 8
S 9
cnot 8 9
S* 9
S x26
cnot 8 x26
S* x26
cnot 9 x26
T* x26
cnot 8 x26
T x26
cnot 8 bellA0
T* bellA0
cnot x26 bellA0
cnot 9 bellA0
T bellA0
cnot 8 bellA0
T* bellA0
S x25
cnot x26 x25
cnot bellA0 x25
cnot 9 x25
T* x25
T 11
cnot x26 11
cnot x25 11
cnot bellA0 11
cnot 9 11
T* 11
cnot 11 bellA2
T bellA2
cnot x25 bellA2
cnot 11 bellA2
T bellA2
cnot x26 bellA2
cnot bellA0 bellA2
cnot 9 bellA2
S* bellA2
cnot 11 bellA2
T* bellA2
T x27
cnot 8 x27
T* x27
cnot 9 x27
T* x27
cnot 8 x27
T x27
cnot x26 bellA0
cnot bellA0 x25
cnot 9 x27
cnot 9 x26
cnot 9 x25
cnot 9 bellA0
cnot 8 9
cnot x25 11
cnot 11 bellA2
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x5
S 10
S x5
cnot 10 x5
T* x5
cnot 10 x5
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x5 bellA3
measure bellA3
cnot bellA3 bellA2
T 8
S 9
cnot 8 9
T* 9
T x26
cnot 8 x26
T* x26
cnot 9 x26
T* x26
cnot 8 x26
T x26
S x25
cnot 9 x25
cnot 8 x25
T* x25
cnot 9 bellA2
cnot 8 bellA2
T* bellA2
cnot x25 bellA2
S* bellA2
cnot 9 bellA2
cnot 8 bellA2
T bellA2
cnot 9 bellA0
cnot 8 bellA0
cnot bellA2 bellA0
T bellA0
cnot x25 bellA0
cnot bellA2 bellA0
T* bellA0
cnot x25 bellA0
cnot x25 bellA2
cnot 9 x26
cnot 8 9
cnot 9 x25
cnot 9 bellA0
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x5
T 10
S x5
cnot 10 x5
T* x5
cnot 10 x5
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 9
cnot bellA0 9
T* 9
S x25
cnot 9 x25
T x25
cnot bellA0 x25
T* x25
cnot 9 x25
S* x25
T x26
cnot bellA0 x26
T* x26
cnot x25 x26
T* x26
cnot bellA0 x26
T x26
T 8
cnot bellA0 9
cnot x25 x26
cnot bellA0 x25
H bellA0
measure bellA0
cz bellA0 x5
S x5
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
reset bellA0
reset bellA1
H 8
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
cnot bellA0 8
T* 8
T x25
cnot 8 x25
T x25
cnot bellA0 x25
T* x25
cnot 8 x25
T* x25
cnot bellA0 8
cnot bellA0 x25
H bellA0
measure bellA0
cz bellA0 x5
T x5
reset bellA0
reset bellA1
H 8
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
cnot bellA0 7
T* 7
T x25
cnot 7 x25
T x25
cnot bellA0 x25
T* x25
cnot 7 x25
T* x25
cnot bellA0 7
cnot bellA0 x25
H bellA0
measure bellA0
cz bellA0 x5
T x5
reset bellA0
reset bellA1
H 7
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
T 7
cnot 6 bellA0
T* bellA0
cnot 7 bellA0
cnot 6 bellA0
T* bellA0
S x25
cnot 7 x25
T* x25
cnot bellA0 x25
S* x25
cnot 7 x25
T x25
cnot 6 x25
cnot 7 x25
T x25
cnot bellA0 x25
cnot 7 x25
T* x25
cnot 7 bellA0
cnot 6 x25
H bellA0
measure bellA0
cz bellA0 x5
S x5
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
T 6
cnot 5 bellA0
T* bellA0
cnot 6 bellA0
cnot 5 bellA0
T* bellA0
S x25
cnot 6 x25
T* x25
cnot bellA0 x25
S* x25
cnot 6 x25
T x25
cnot 5 x25
cnot 6 x25
T x25
cnot bellA0 x25
cnot 6 x25
T* x25
cnot 5 x25
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x5
S x5
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
T 5
cnot 4 bellA0
T* bellA0
cnot 5 bellA0
cnot 4 bellA0
T* bellA0
S x25
cnot 5 x25
T* x25
cnot bellA0 x25
S* x25
cnot 5 x25
T x25
cnot 4 x25
cnot 5 x25
T x25
cnot bellA0 x25
cnot 5 x25
T* x25
cnot 4 x25
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x5
S x5
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
S x25
cnot 4 x25
T* x25
cnot bellA0 x25
S* x25
cnot 4 x25
T x25
cnot 3 x25
cnot 4 x25
T x25
cnot bellA0 x25
cnot 4 x25
T* x25
cnot 4 bellA0
cnot 3 x25
H bellA0
measure bellA0
cz bellA0 x5
S x5
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 0
H x30
T 0
T x29
cnot 0 x29
T* x29
T x30
cnot 0 x30
T* x30
cnot x29 x30
T* x30
cnot 0 x30
T x30
cnot x29 x30
cnot 0 x29
H x30
H 0
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
S x25
cnot 3 x25
T* x25
cnot bellA0 x25
S* x25
cnot 3 x25
T x25
cnot 2 x25
cnot 3 x25
T x25
cnot bellA0 x25
cnot 3 x25
T* x25
cnot 2 x25
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x5
S x5
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 0
H x29
T 0
T x28
cnot 0 x28
T* x28
T x29
cnot 0 x29
T* x29
cnot x28 x29
T* x29
cnot 0 x29
T x29
cnot x28 x29
cnot 0 x28
H x29
H 0
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
S x25
cnot 2 x25
T* x25
cnot bellA0 x25
S* x25
cnot 2 x25
T x25
cnot 1 x25
cnot 2 x25
T x25
cnot bellA0 x25
cnot 2 x25
T* x25
cnot 2 bellA0
cnot 1 x25
H bellA0
measure bellA0
cz bellA0 x5
S x5
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 0
H x28
T 0
T x27
cnot 0 x27
T* x27
T x28
cnot 0 x28
T* x28
cnot x27 x28
T* x28
cnot 0 x28
T x28
cnot x27 x28
cnot 0 x27
H x28
H 0
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
S x25
cnot 1 x25
T* x25
cnot bellA0 x25
S* x25
cnot 1 x25
T x25
cnot 0 x25
cnot 1 x25
T x25
cnot bellA0 x25
cnot 1 x25
T* x25
cnot 0 x25
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x5
S x5
reset bellA0
reset bellA1
H 0
H x27
T 0
T x26
cnot 0 x26
T* x26
T x27
cnot 0 x27
T* x27
cnot x26 x27
T* x27
cnot 0 x27
T x27
cnot x26 x27
cnot 0 x26
H x27
H 0
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x25
cnot 0 x25
T x25
cnot bellA0 x25
T* x25
cnot 0 x25
T* x25
cnot bellA0 0
cnot bellA0 x25
H bellA0
measure bellA0
cz bellA0 x5
T x5
reset bellA0
reset bellA1
H x26
H bellA0
cnot bellA0 bellA1
cnot x5 bellA1
measure bellA1
cnot bellA1 bellA0
T x25
cnot bellA0 x25
T* x25
T x26
cnot bellA0 x26
T* x26
cnot x25 x26
T* x26
cnot bellA0 x26
T x26
cnot x25 x26
cnot bellA0 x25
H bellA0
measure bellA0
cz bellA0 x5
T x5
reset bellA0
reset bellA1
H x26
H bellL0
cnot bellL0 bellL1
cnot x5 bellL1
measure bellL1
cnot bellL1 bellL0
cnot bellL0 x25
H bellL0
measure bellL0
cz bellL0 x5
reset bellL0
reset bellL1
H 14
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
T 13
T 8
Z 8
cnot 13 8
T* 8
T x25
cnot 13 x25
T* x25
cnot 8 x25
T* x25
cnot 13 x25
T x25
T 11
cnot 8 11
cnot 13 11
T* 11
T x27
cnot 11 x27
T x27
cnot 8 x27
cnot 13 x27
T* x27
cnot 11 x27
T* x27
T 9
cnot 8 9
cnot 13 9
T* 9
T x29
cnot 8 x29
cnot 13 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
cnot 13 x29
T x29
T x28
cnot 8 x28
cnot 13 x28
T* x28
cnot 8 bellA0
cnot 13 bellA0
T* bellA0
cnot x28 bellA0
T* bellA0
cnot 8 bellA0
cnot 13 bellA0
T bellA0
T x26
cnot 8 x26
cnot 13 x26
T* x26
cnot 8 bellA2
cnot 13 bellA2
T* bellA2
cnot x26 bellA2
T* bellA2
cnot 8 bellA2
cnot 13 bellA2
T bellA2
T x24
T x4
cnot x24 x4
T* x4
cnot x24 bellA4
T* bellA4
cnot x4 bellA4
T* bellA4
cnot x24 bellA4
T bellA4
cnot x26 bellA2
cnot x28 bellA0
cnot x4 bellA4
cnot x24 x4
cnot 9 x29
cnot 8 9
cnot 8 x28
cnot 8 x27
cnot 8 x26
cnot 8 x25
cnot 13 x28
cnot 13 x27
cnot 13 x26
cnot 13 9
cnot 13 8
cnot 8 11
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
T 10
T 12
T 14
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
S 11
T 8
cnot 11 8
S* 8
S x26
cnot 11 x26
T* x26
cnot 8 x26
S* x26
cnot 11 x26
T x26
cnot 8 bellA2
cnot 11 bellA2
S* bellA2
cnot x26 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x25
cnot 8 x25
cnot 11 x25
S* x25
cnot x26 x25
cnot bellA2 x25
cnot 11 x25
T x25
cnot 8 x25
cnot 11 x25
T* x25
S 13
cnot 8 13
cnot 11 13
T* 13
cnot x26 13
cnot x25 13
cnot bellA2 13
cnot 11 13
T 13
cnot 8 13
cnot 11 13
T* 13
S x27
cnot 11 x27
T* x27
cnot 8 x27
S* x27
cnot 11 x27
T x27
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x27 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x28
cnot 8 x28
cnot 11 x28
S* x28
cnot x27 x28
cnot bellA0 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x28 9
cnot x27 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot x28 x29
cnot x27 x29
cnot bellA0 x29
cnot 9 x29
cnot 11 x29
T x29
cnot 8 x29
cnot 11 x29
T* x29
S x24
cnot x26 x24
cnot x25 x24
cnot bellA2 x24
cnot 13 x24
cnot 11 x24
T* x24
S x4
cnot x24 x4
T x4
cnot x26 x4
cnot x25 x4
cnot bellA2 x4
cnot 13 x4
cnot 11 x4
S* x4
cnot x24 x4
T* x4
cnot x26 bellA4
cnot x25 bellA4
cnot x24 bellA4
cnot bellA2 bellA4
cnot 13 bellA4
cnot 11 bellA4
T* bellA4
cnot x4 bellA4
cnot x24 bellA4
T* bellA4
cnot x26 bellA4
cnot x25 bellA4
cnot x24 bellA4
cnot bellA2 bellA4
cnot 13 bellA4
cnot 11 bellA4
T bellA4
cnot x24 bellA4
cnot x26 bellA2
cnot x27 bellA0
cnot x4 bellA4
cnot bellA0 x28
cnot bellA2 x25
cnot x28 9
cnot 9 x29
cnot 8 x27
cnot 8 x26
cnot x25 13
cnot 13 x4
cnot 13 x24
cnot 11 x4
cnot 11 x29
cnot 11 x28
cnot 11 x25
cnot 11 x24
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
S 10
S 12
T 14
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
S 11
T* 8
cnot 11 8
S* 8
S x25
cnot 11 x25
T* x25
cnot 8 x25
S* x25
cnot 11 x25
T x25
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot x25 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x24
cnot x25 x24
cnot bellA2 x24
cnot 11 x24
T* x24
S x4
cnot x24 x4
T x4
cnot x25 x4
cnot bellA2 x4
cnot 11 x4
S* x4
cnot x24 x4
T* x4
T 13
cnot x25 13
cnot x24 13
cnot bellA2 13
cnot 11 13
T* 13
cnot x4 13
cnot x24 13
T* 13
cnot x25 13
cnot x24 13
cnot bellA2 13
cnot 11 13
T 13
S x26
cnot 11 x26
T* x26
cnot 8 x26
S* x26
cnot 11 x26
T x26
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x26 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x27
cnot 8 x27
cnot 11 x27
S* x27
cnot x26 x27
cnot bellA0 x27
cnot 11 x27
T x27
cnot 8 x27
cnot 11 x27
T* x27
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x27 9
cnot x26 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x28
cnot 8 x28
cnot 11 x28
T* x28
cnot x27 x28
cnot x26 x28
cnot bellA0 x28
cnot 9 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
cnot x24 13
cnot x4 13
cnot x25 bellA2
cnot x26 bellA0
cnot bellA2 x4
cnot bellA0 x27
cnot bellA2 x24
cnot x27 9
cnot 9 x28
cnot 8 x26
cnot 8 x25
cnot 11 x4
cnot 11 x28
cnot 11 x27
cnot 11 x24
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
S 10
S 12
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
S 11
T 8
Z 8
cnot 11 8
T* 8
S x25
cnot 11 x25
T* x25
cnot 8 x25
S* x25
cnot 11 x25
T x25
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x25 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x26
cnot 8 x26
cnot 11 x26
S* x26
cnot x25 x26
cnot bellA0 x26
cnot 11 x26
T x26
cnot 8 x26
cnot 11 x26
T* x26
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x26 9
cnot x25 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x27
cnot 8 x27
cnot 11 x27
T* x27
cnot x26 x27
cnot x25 x27
cnot bellA0 x27
cnot 9 x27
cnot 11 x27
T x27
cnot 8 x27
cnot 11 x27
T* x27
S x24
cnot 11 x24
T* x24
S x4
cnot 11 x4
T* x4
cnot x24 x4
S* x4
cnot 11 x4
T x4
cnot x24 bellA2
cnot 11 bellA2
T* bellA2
cnot x4 bellA2
cnot 11 bellA2
T* bellA2
cnot x24 bellA2
cnot 11 bellA2
T bellA2
cnot x25 bellA0
cnot x4 bellA2
cnot x24 x4
cnot bellA0 x26
cnot x26 9
cnot 9 x27
cnot 8 x25
cnot 11 x27
cnot 11 x26
cnot 11 x24
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
S 10
T 12
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
T 11
S x24
cnot 11 x24
T* x24
S x4
cnot 11 x4
T* x4
cnot x24 x4
S* x4
cnot 11 x4
T x4
cnot x24 bellA0
cnot 11 bellA0
T* bellA0
cnot x4 bellA0
cnot 11 bellA0
T* bellA0
cnot x24 bellA0
cnot 11 bellA0
T bellA0
T* 8
Z 8
cnot x4 8
cnot bellA0 8
cnot 11 8
T* 8
S x25
cnot 8 x25
T x25
cnot x4 x25
cnot bellA0 x25
cnot 11 x25
S* x25
cnot 8 x25
T* x25
S 9
cnot x25 9
cnot 8 9
T 9
cnot x4 9
cnot bellA0 9
cnot 11 9
cnot 8 9
T* 9
cnot x25 9
cnot 8 9
S* 9
T x26
cnot 9 x26
T x26
cnot x4 x26
cnot bellA0 x26
cnot 8 x26
cnot 11 x26
T* x26
cnot 9 x26
T* x26
cnot x4 bellA0
cnot x24 x4
cnot bellA0 x25
cnot bellA0 8
cnot 8 9
cnot 8 x26
cnot 11 x26
cnot 11 x25
cnot 11 x24
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
S 10
reset bellA0
reset bellA1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
S 9
cnot 8 9
T* 9
T x25
cnot 8 x25
T* x25
cnot 9 x25
T* x25
cnot 8 x25
T x25
S x24
cnot 9 x24
cnot 8 x24
T* x24
S x4
cnot 9 x4
cnot 8 x4
T* x4
cnot x24 x4
S* x4
cnot 9 x4
cnot 8 x4
T x4
cnot x24 bellA0
cnot 9 bellA0
cnot 8 bellA0
T* bellA0
cnot x4 bellA0
cnot 9 bellA0
cnot 8 bellA0
T* bellA0
cnot x24 bellA0
cnot 9 bellA0
cnot 8 bellA0
T bellA0
cnot x4 bellA0
cnot x24 x4
cnot 9 x25
cnot 8 9
cnot 9 x24
cnot 9 bellA0
H bellA0
measure bellA0
cz bellA0 10
T 10
reset bellA0
reset bellA1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x23 x24
swap x13 x23
cnot x13 x25
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 8
T 9
S x24
cnot 9 x24
T* x24
S x4
cnot 9 x4
T* x4
cnot x24 x4
S* x4
cnot 9 x4
T x4
T x25
cnot x24 x25
cnot 9 x25
T* x25
cnot x4 x25
cnot 9 x25
T* x25
cnot x24 x25
cnot 9 x25
T x25
T 8
cnot x4 x25
cnot x24 x4
cnot 9 x25
cnot 9 x24
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x23 x24
swap x13 x23
cnot x13 x25
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x25
cnot 7 x25
T* x25
cnot 8 x25
T* x25
cnot 7 x25
T x25
cnot 8 x25
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x25
cnot 7 x25
T* x25
cnot 8 x25
T* x25
cnot 7 x25
T x25
cnot 8 x25
cnot 7 8
H 8
T 8
T x24
cnot 8 x24
T* x24
T x4
cnot 8 x4
T* x4
cnot x24 x4
T* x4
cnot 8 x4
T x4
cnot x24 x4
cnot 8 x24
H 8
T 7
T x24
cnot 7 x24
T* x24
T x4
cnot 7 x4
T* x4
cnot x24 x4
T* x4
cnot 7 x4
T x4
cnot x24 x4
cnot 7 x24
H 7
T 6
T 7
cnot 6 7
T* 7
T x25
cnot 6 x25
T* x25
cnot 7 x25
T* x25
cnot 6 x25
T x25
cnot 7 x25
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x25
cnot 6 x25
T* x25
cnot 7 x25
T* x25
cnot 6 x25
T x25
cnot 7 x25
cnot 6 7
H 7
T 6
S x24
cnot 6 x24
T* x24
S x4
cnot 6 x4
T* x4
cnot x24 x4
S* x4
cnot 6 x4
T x4
T 7
cnot x24 7
cnot 6 7
T* 7
cnot x4 7
cnot 6 7
T* 7
cnot x24 7
cnot 6 7
T 7
cnot x4 7
cnot x24 x4
cnot 6 x24
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x25
cnot 5 x25
T* x25
cnot 6 x25
T* x25
cnot 5 x25
T x25
cnot 6 x25
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x25
cnot 5 x25
T* x25
cnot 6 x25
T* x25
cnot 5 x25
T x25
cnot 6 x25
cnot 5 6
H 6
T 5
S x24
cnot 5 x24
T* x24
S x4
cnot 5 x4
T* x4
cnot x24 x4
S* x4
cnot 5 x4
T x4
T 6
cnot x24 6
cnot 5 6
T* 6
cnot x4 6
cnot 5 6
T* 6
cnot x24 6
cnot 5 6
T 6
cnot x4 6
cnot x24 x4
cnot 5 6
cnot 5 x24
H 5
T 4
T 5
cnot 4 5
T* 5
T x25
cnot 4 x25
T* x25
cnot 5 x25
T* x25
cnot 4 x25
T x25
cnot 5 x25
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x25
cnot 4 x25
T* x25
cnot 5 x25
T* x25
cnot 4 x25
T x25
cnot 5 x25
cnot 4 5
H 5
T 4
S x24
cnot 4 x24
T* x24
S x4
cnot 4 x4
T* x4
cnot x24 x4
S* x4
cnot 4 x4
T x4
T 5
cnot x24 5
cnot 4 5
T* 5
cnot x4 5
cnot 4 5
T* 5
cnot x24 5
cnot 4 5
T 5
cnot x4 5
cnot x24 x4
cnot 4 5
cnot 4 x24
H 4
T 3
T 4
cnot 3 4
T* 4
T x25
cnot 3 x25
T* x25
cnot 4 x25
T* x25
cnot 3 x25
T x25
cnot 4 x25
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 0
H x30
T 0
T x29
cnot 0 x29
T* x29
T x30
cnot 0 x30
T* x30
cnot x29 x30
T* x30
cnot 0 x30
T x30
cnot x29 x30
cnot 0 x29
H x30
H 0
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x25
cnot 3 x25
T* x25
cnot 4 x25
T* x25
cnot 3 x25
T x25
cnot 4 x25
cnot 3 4
H 4
T 3
S x24
cnot 3 x24
T* x24
S x4
cnot 3 x4
T* x4
cnot x24 x4
S* x4
cnot 3 x4
T x4
T 4
cnot x24 4
cnot 3 4
T* 4
cnot x4 4
cnot 3 4
T* 4
cnot x24 4
cnot 3 4
T 4
cnot x4 4
cnot x24 x4
cnot 3 x24
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x25
cnot 2 x25
T* x25
cnot 3 x25
T* x25
cnot 2 x25
T x25
cnot 3 x25
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 0
H x29
T 0
T x28
cnot 0 x28
T* x28
T x29
cnot 0 x29
T* x29
cnot x28 x29
T* x29
cnot 0 x29
T x29
cnot x28 x29
cnot 0 x28
H x29
H 0
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x25
cnot 2 x25
T* x25
cnot 3 x25
T* x25
cnot 2 x25
T x25
cnot 3 x25
cnot 2 3
H 3
T 2
S x24
cnot 2 x24
T* x24
S x4
cnot 2 x4
T* x4
cnot x24 x4
S* x4
cnot 2 x4
T x4
T 3
cnot x24 3
cnot 2 3
T* 3
cnot x4 3
cnot 2 3
T* 3
cnot x24 3
cnot 2 3
T 3
cnot x4 3
cnot x24 x4
cnot 2 3
cnot 2 x24
H 2
T 1
T 2
cnot 1 2
T* 2
T x25
cnot 1 x25
T* x25
cnot 2 x25
T* x25
cnot 1 x25
T x25
cnot 2 x25
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 0
H x28
T 0
T x27
cnot 0 x27
T* x27
T x28
cnot 0 x28
T* x28
cnot x27 x28
T* x28
cnot 0 x28
T x28
cnot x27 x28
cnot 0 x27
H x28
H 0
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x25
cnot 1 x25
T* x25
cnot 2 x25
T* x25
cnot 1 x25
T x25
cnot 2 x25
cnot 1 2
H 2
T 1
S x24
cnot 1 x24
T* x24
S x4
cnot 1 x4
T* x4
cnot x24 x4
S* x4
cnot 1 x4
T x4
T 2
cnot x24 2
cnot 1 2
T* 2
cnot x4 2
cnot 1 2
T* 2
cnot x24 2
cnot 1 2
T 2
cnot x4 2
cnot x24 x4
cnot 1 x24
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x25
cnot 0 x25
T* x25
cnot 1 x25
T* x25
cnot 0 x25
T x25
cnot 1 x25
cnot 0 1
H 0
H x27
T 0
T x26
cnot 0 x26
T* x26
T x27
cnot 0 x27
T* x27
cnot x26 x27
T* x27
cnot 0 x27
T x27
cnot x26 x27
cnot 0 x26
H x27
H 0
T 0
T 1
cnot 0 1
T* 1
T x25
cnot 0 x25
T* x25
cnot 1 x25
T* x25
cnot 0 x25
T x25
cnot 1 x25
cnot 0 1
H 1
T 0
S x24
cnot 0 x24
T* x24
S x4
cnot 0 x4
T* x4
cnot x24 x4
S* x4
cnot 0 x4
T x4
T 1
cnot x24 1
cnot 0 1
T* 1
cnot x4 1
cnot 0 1
T* 1
cnot x24 1
cnot 0 1
T 1
cnot x4 1
cnot x24 x4
cnot 0 1
cnot 0 x24
H 0
H x26
T 0
T x25
cnot 0 x25
T* x25
T x26
cnot 0 x26
T* x26
cnot x25 x26
T* x26
cnot 0 x26
T x26
cnot x25 x26
cnot 0 x25
H x26
H 0
T 0
T x24
cnot 0 x24
T* x24
T x4
cnot 0 x4
T* x4
cnot x24 x4
T* x4
cnot 0 x4
T x4
cnot x24 x4
cnot 0 x24
H x25
T x24
T x25
cnot x24 x25
T* x25
T x4
cnot x24 x4
T* x4
cnot x25 x4
T* x4
cnot x24 x4
T x4
cnot x25 x4
cnot x24 x25
H x25
cnot x4 x24
H 15
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
T 13
S* 8
cnot 13 8
T* 8
T x25
cnot 13 x25
T* x25
cnot 8 x25
T* x25
cnot 13 x25
T x25
T 11
cnot 8 11
cnot 13 11
T* 11
T x27
cnot 11 x27
T x27
cnot 8 x27
cnot 13 x27
T* x27
cnot 11 x27
T* x27
T 9
cnot 8 9
cnot 13 9
T* 9
T x29
cnot 8 x29
cnot 13 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
cnot 13 x29
T x29
T bellA6
T x23
cnot bellA6 x23
T* x23
T x3
cnot bellA6 x3
T* x3
cnot x23 x3
T* x3
cnot bellA6 x3
T x3
T x28
cnot 8 x28
cnot 13 x28
T* x28
cnot 8 bellA0
cnot 13 bellA0
T* bellA0
cnot x28 bellA0
T* bellA0
cnot 8 bellA0
cnot 13 bellA0
T bellA0
T x26
cnot 8 x26
cnot 13 x26
T* x26
cnot 8 bellA2
cnot 13 bellA2
T* bellA2
cnot x26 bellA2
T* bellA2
cnot 8 bellA2
cnot 13 bellA2
T bellA2
T x24
cnot 8 x24
cnot 13 x24
T* x24
cnot 8 bellA4
cnot 13 bellA4
T* bellA4
cnot x24 bellA4
T* bellA4
cnot 8 bellA4
cnot 13 bellA4
T bellA4
cnot x24 bellA4
cnot x26 bellA2
cnot x28 bellA0
cnot x23 x3
cnot bellA6 x23
cnot 9 x29
cnot 8 9
cnot 8 x28
cnot 8 x27
cnot 8 x26
cnot 8 x25
cnot 8 x24
cnot 13 x28
cnot 13 x27
cnot 13 x26
cnot 13 x24
cnot 13 9
cnot 13 8
cnot 8 11
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
T 10
T 12
T 14
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
S 11
T* 8
Z 8
cnot 11 8
S* 8
S x26
cnot 11 x26
T* x26
cnot 8 x26
S* x26
cnot 11 x26
T x26
cnot 8 bellA2
cnot 11 bellA2
S* bellA2
cnot x26 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x25
cnot 8 x25
cnot 11 x25
S* x25
cnot x26 x25
cnot bellA2 x25
cnot 11 x25
T x25
cnot 8 x25
cnot 11 x25
T* x25
S 13
cnot 8 13
cnot 11 13
S* 13
cnot x26 13
cnot x25 13
cnot bellA2 13
cnot 11 13
T 13
cnot 8 13
cnot 11 13
T* 13
S x27
cnot 11 x27
T* x27
cnot 8 x27
S* x27
cnot 11 x27
T x27
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x27 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x28
cnot 8 x28
cnot 11 x28
S* x28
cnot x27 x28
cnot bellA0 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x28 9
cnot x27 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
S x24
cnot 8 x24
cnot 11 x24
S* x24
cnot x26 x24
cnot x25 x24
cnot bellA2 x24
cnot 13 x24
cnot 11 x24
T x24
cnot 8 x24
cnot 11 x24
T* x24
cnot 8 bellA4
cnot 11 bellA4
T* bellA4
cnot x26 bellA4
cnot x25 bellA4
cnot x24 bellA4
cnot bellA2 bellA4
cnot 13 bellA4
cnot 11 bellA4
T bellA4
cnot 8 bellA4
cnot 11 bellA4
T* bellA4
S x23
cnot x26 x23
cnot x25 x23
cnot x24 x23
cnot bellA4 x23
cnot bellA2 x23
cnot 13 x23
cnot 11 x23
T* x23
S x3
cnot x23 x3
T x3
cnot x26 x3
cnot x25 x3
cnot x24 x3
cnot bellA4 x3
cnot bellA2 x3
cnot 13 x3
cnot 11 x3
S* x3
cnot x23 x3
T* x3
T bellA6
cnot x26 bellA6
cnot x25 bellA6
cnot x24 bellA6
cnot x23 bellA6
cnot bellA4 bellA6
cnot bellA2 bellA6
cnot 13 bellA6
cnot 11 bellA6
T* bellA6
cnot x3 bellA6
cnot x23 bellA6
T* bellA6
cnot x26 bellA6
cnot x25 bellA6
cnot x24 bellA6
cnot x23 bellA6
cnot bellA4 bellA6
cnot bellA2 bellA6
cnot 13 bellA6
cnot 11 bellA6
T bellA6
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot x28 x29
cnot x27 x29
cnot bellA0 x29
cnot 9 x29
cnot 11 x29
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot x24 bellA4
cnot x26 bellA2
cnot x27 bellA0
cnot x3 bellA6
cnot x23 bellA6
cnot bellA4 x3
cnot bellA0 x28
cnot bellA2 x25
cnot bellA4 x23
cnot x28 9
cnot 9 x29
cnot 8 x27
cnot 8 x26
cnot x25 13
cnot 13 x3
cnot 13 x24
cnot 13 x23
cnot 13 bellA4
cnot 11 x3
cnot 11 x29
cnot 11 x28
cnot 11 x25
cnot 11 x24
cnot 11 x23
cnot 11 bellA4
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
S 10
S 12
S 14
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
S 11
T 8
cnot 11 8
S* 8
S x25
cnot 11 x25
T* x25
cnot 8 x25
S* x25
cnot 11 x25
T x25
cnot 8 bellA2
cnot 11 bellA2
S* bellA2
cnot x25 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x24
cnot 8 x24
cnot 11 x24
S* x24
cnot x25 x24
cnot bellA2 x24
cnot 11 x24
T x24
cnot 8 x24
cnot 11 x24
T* x24
S 13
cnot 8 13
cnot 11 13
T* 13
cnot x25 13
cnot x24 13
cnot bellA2 13
cnot 11 13
T 13
cnot 8 13
cnot 11 13
T* 13
S x26
cnot 11 x26
T* x26
cnot 8 x26
S* x26
cnot 11 x26
T x26
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x26 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x27
cnot 8 x27
cnot 11 x27
S* x27
cnot x26 x27
cnot bellA0 x27
cnot 11 x27
T x27
cnot 8 x27
cnot 11 x27
T* x27
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x27 9
cnot x26 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x28
cnot 8 x28
cnot 11 x28
T* x28
cnot x27 x28
cnot x26 x28
cnot bellA0 x28
cnot 9 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
S x23
cnot x25 x23
cnot x24 x23
cnot bellA2 x23
cnot 13 x23
cnot 11 x23
T* x23
S x3
cnot x23 x3
T x3
cnot x25 x3
cnot x24 x3
cnot bellA2 x3
cnot 13 x3
cnot 11 x3
S* x3
cnot x23 x3
T* x3
cnot x25 bellA4
cnot x24 bellA4
cnot x23 bellA4
cnot bellA2 bellA4
cnot 13 bellA4
cnot 11 bellA4
T* bellA4
cnot x3 bellA4
cnot x23 bellA4
T* bellA4
cnot x25 bellA4
cnot x24 bellA4
cnot x23 bellA4
cnot bellA2 bellA4
cnot 13 bellA4
cnot 11 bellA4
T bellA4
cnot x23 bellA4
cnot x25 bellA2
cnot x26 bellA0
cnot x3 bellA4
cnot bellA0 x27
cnot bellA2 x24
cnot x27 9
cnot 9 x28
cnot 8 x26
cnot 8 x25
cnot x24 13
cnot 13 x3
cnot 13 x23
cnot 11 x3
cnot 11 x28
cnot 11 x27
cnot 11 x24
cnot 11 x23
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
S 10
S 12
T 14
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
S 11
T* 8
cnot 11 8
S* 8
S x24
cnot 11 x24
T* x24
cnot 8 x24
S* x24
cnot 11 x24
T x24
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot x24 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x23
cnot x24 x23
cnot bellA2 x23
cnot 11 x23
T* x23
S x3
cnot x23 x3
T x3
cnot x24 x3
cnot bellA2 x3
cnot 11 x3
S* x3
cnot x23 x3
T* x3
T 13
cnot x24 13
cnot x23 13
cnot bellA2 13
cnot 11 13
T* 13
cnot x3 13
cnot x23 13
T* 13
cnot x24 13
cnot x23 13
cnot bellA2 13
cnot 11 13
T 13
S x25
cnot 11 x25
T* x25
cnot 8 x25
S* x25
cnot 11 x25
T x25
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x25 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x26
cnot 8 x26
cnot 11 x26
S* x26
cnot x25 x26
cnot bellA0 x26
cnot 11 x26
T x26
cnot 8 x26
cnot 11 x26
T* x26
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x26 9
cnot x25 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x27
cnot 8 x27
cnot 11 x27
T* x27
cnot x26 x27
cnot x25 x27
cnot bellA0 x27
cnot 9 x27
cnot 11 x27
T x27
cnot 8 x27
cnot 11 x27
T* x27
cnot x23 13
cnot x3 13
cnot x24 bellA2
cnot x25 bellA0
cnot bellA2 x3
cnot bellA0 x26
cnot bellA2 x23
cnot x26 9
cnot 9 x27
cnot 8 x25
cnot 8 x24
cnot 11 x3
cnot 11 x27
cnot 11 x26
cnot 11 x23
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
S 10
S 12
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
S 11
T 8
Z 8
cnot 11 8
T* 8
S x24
cnot 11 x24
T* x24
cnot 8 x24
S* x24
cnot 11 x24
T x24
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x24 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x25
cnot 8 x25
cnot 11 x25
S* x25
cnot x24 x25
cnot bellA0 x25
cnot 11 x25
T x25
cnot 8 x25
cnot 11 x25
T* x25
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x25 9
cnot x24 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x26
cnot 8 x26
cnot 11 x26
T* x26
cnot x25 x26
cnot x24 x26
cnot bellA0 x26
cnot 9 x26
cnot 11 x26
T x26
cnot 8 x26
cnot 11 x26
T* x26
S x23
cnot 11 x23
T* x23
S x3
cnot 11 x3
T* x3
cnot x23 x3
S* x3
cnot 11 x3
T x3
cnot x23 bellA2
cnot 11 bellA2
T* bellA2
cnot x3 bellA2
cnot 11 bellA2
T* bellA2
cnot x23 bellA2
cnot 11 bellA2
T bellA2
cnot x24 bellA0
cnot x3 bellA2
cnot x23 x3
cnot bellA0 x25
cnot x25 9
cnot 9 x26
cnot 8 x24
cnot 11 x26
cnot 11 x25
cnot 11 x23
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
S 10
T 12
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
T 11
S x23
cnot 11 x23
T* x23
S x3
cnot 11 x3
T* x3
cnot x23 x3
S* x3
cnot 11 x3
T x3
cnot x23 bellA0
cnot 11 bellA0
T* bellA0
cnot x3 bellA0
cnot 11 bellA0
T* bellA0
cnot x23 bellA0
cnot 11 bellA0
T bellA0
T* 8
Z 8
cnot x3 8
cnot bellA0 8
cnot 11 8
T* 8
S x24
cnot 8 x24
T x24
cnot x3 x24
cnot bellA0 x24
cnot 11 x24
S* x24
cnot 8 x24
T* x24
S 9
cnot x24 9
cnot 8 9
T 9
cnot x3 9
cnot bellA0 9
cnot 11 9
cnot 8 9
T* 9
cnot x24 9
cnot 8 9
S* 9
T x25
cnot 9 x25
T x25
cnot x3 x25
cnot bellA0 x25
cnot 8 x25
cnot 11 x25
T* x25
cnot 9 x25
T* x25
cnot x3 bellA0
cnot x23 x3
cnot bellA0 x24
cnot bellA0 8
cnot 8 9
cnot 8 x25
cnot 11 x25
cnot 11 x24
cnot 11 x23
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
S 10
reset bellA0
reset bellA1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x23 x24
swap x13 x23
cnot x13 x25
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x23 x24
swap x13 x23
cnot x13 x25
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
S 9
cnot 8 9
T* 9
T x24
cnot 8 x24
T* x24
cnot 9 x24
T* x24
cnot 8 x24
T x24
S x23
cnot 9 x23
cnot 8 x23
T* x23
S x3
cnot 9 x3
cnot 8 x3
T* x3
cnot x23 x3
S* x3
cnot 9 x3
cnot 8 x3
T x3
cnot x23 bellA0
cnot 9 bellA0
cnot 8 bellA0
T* bellA0
cnot x3 bellA0
cnot 9 bellA0
cnot 8 bellA0
T* bellA0
cnot x23 bellA0
cnot 9 bellA0
cnot 8 bellA0
T bellA0
cnot x3 bellA0
cnot x23 x3
cnot 9 x24
cnot 8 9
cnot 9 x23
cnot 9 bellA0
H bellA0
measure bellA0
cz bellA0 10
T 10
reset bellA0
reset bellA1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x13 x23
cnot x13 x24
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x25
cnot 7 x25
T* x25
cnot 8 x25
T* x25
cnot 7 x25
T x25
cnot 8 x25
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x25
cnot 7 x25
T* x25
cnot 8 x25
T* x25
cnot 7 x25
T x25
cnot 8 x25
cnot 7 8
H 8
T 9
S x23
cnot 9 x23
T* x23
S x3
cnot 9 x3
T* x3
cnot x23 x3
S* x3
cnot 9 x3
T x3
T x24
cnot x23 x24
cnot 9 x24
T* x24
cnot x3 x24
cnot 9 x24
T* x24
cnot x23 x24
cnot 9 x24
T x24
T 8
cnot x3 x24
cnot x23 x3
cnot 9 x24
cnot 9 x23
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x13 x23
cnot x13 x24
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x24
cnot 7 x24
T* x24
cnot 8 x24
T* x24
cnot 7 x24
T x24
cnot 8 x24
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x25
cnot 6 x25
T* x25
cnot 7 x25
T* x25
cnot 6 x25
T x25
cnot 7 x25
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x25
cnot 6 x25
T* x25
cnot 7 x25
T* x25
cnot 6 x25
T x25
cnot 7 x25
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x24
cnot 7 x24
T* x24
cnot 8 x24
T* x24
cnot 7 x24
T x24
cnot 8 x24
cnot 7 8
H 8
T 8
T x23
cnot 8 x23
T* x23
T x3
cnot 8 x3
T* x3
cnot x23 x3
T* x3
cnot 8 x3
T x3
cnot x23 x3
cnot 8 x23
H 8
T 7
T x23
cnot 7 x23
T* x23
T x3
cnot 7 x3
T* x3
cnot x23 x3
T* x3
cnot 7 x3
T x3
cnot x23 x3
cnot 7 x23
H 7
T 6
T 7
cnot 6 7
T* 7
T x24
cnot 6 x24
T* x24
cnot 7 x24
T* x24
cnot 6 x24
T x24
cnot 7 x24
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x25
cnot 5 x25
T* x25
cnot 6 x25
T* x25
cnot 5 x25
T x25
cnot 6 x25
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x25
cnot 5 x25
T* x25
cnot 6 x25
T* x25
cnot 5 x25
T x25
cnot 6 x25
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x24
cnot 6 x24
T* x24
cnot 7 x24
T* x24
cnot 6 x24
T x24
cnot 7 x24
cnot 6 7
H 7
T 6
S x23
cnot 6 x23
T* x23
S x3
cnot 6 x3
T* x3
cnot x23 x3
S* x3
cnot 6 x3
T x3
T 7
cnot x23 7
cnot 6 7
T* 7
cnot x3 7
cnot 6 7
T* 7
cnot x23 7
cnot 6 7
T 7
cnot x3 7
cnot x23 x3
cnot 6 x23
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x24
cnot 5 x24
T* x24
cnot 6 x24
T* x24
cnot 5 x24
T x24
cnot 6 x24
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x25
cnot 4 x25
T* x25
cnot 5 x25
T* x25
cnot 4 x25
T x25
cnot 5 x25
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x25
cnot 4 x25
T* x25
cnot 5 x25
T* x25
cnot 4 x25
T x25
cnot 5 x25
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x24
cnot 5 x24
T* x24
cnot 6 x24
T* x24
cnot 5 x24
T x24
cnot 6 x24
cnot 5 6
H 6
T 5
S x23
cnot 5 x23
T* x23
S x3
cnot 5 x3
T* x3
cnot x23 x3
S* x3
cnot 5 x3
T x3
T 6
cnot x23 6
cnot 5 6
T* 6
cnot x3 6
cnot 5 6
T* 6
cnot x23 6
cnot 5 6
T 6
cnot x3 6
cnot x23 x3
cnot 5 6
cnot 5 x23
H 5
T 4
T 5
cnot 4 5
T* 5
T x24
cnot 4 x24
T* x24
cnot 5 x24
T* x24
cnot 4 x24
T x24
cnot 5 x24
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x25
cnot 3 x25
T* x25
cnot 4 x25
T* x25
cnot 3 x25
T x25
cnot 4 x25
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 0
H x30
T 0
T x29
cnot 0 x29
T* x29
T x30
cnot 0 x30
T* x30
cnot x29 x30
T* x30
cnot 0 x30
T x30
cnot x29 x30
cnot 0 x29
H x30
H 0
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x25
cnot 3 x25
T* x25
cnot 4 x25
T* x25
cnot 3 x25
T x25
cnot 4 x25
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x24
cnot 4 x24
T* x24
cnot 5 x24
T* x24
cnot 4 x24
T x24
cnot 5 x24
cnot 4 5
H 5
T 4
S x23
cnot 4 x23
T* x23
S x3
cnot 4 x3
T* x3
cnot x23 x3
S* x3
cnot 4 x3
T x3
T 5
cnot x23 5
cnot 4 5
T* 5
cnot x3 5
cnot 4 5
T* 5
cnot x23 5
cnot 4 5
T 5
cnot x3 5
cnot x23 x3
cnot 4 5
cnot 4 x23
H 4
T 3
T 4
cnot 3 4
T* 4
T x24
cnot 3 x24
T* x24
cnot 4 x24
T* x24
cnot 3 x24
T x24
cnot 4 x24
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x25
cnot 2 x25
T* x25
cnot 3 x25
T* x25
cnot 2 x25
T x25
cnot 3 x25
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 0
H x29
T 0
T x28
cnot 0 x28
T* x28
T x29
cnot 0 x29
T* x29
cnot x28 x29
T* x29
cnot 0 x29
T x29
cnot x28 x29
cnot 0 x28
H x29
H 0
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x25
cnot 2 x25
T* x25
cnot 3 x25
T* x25
cnot 2 x25
T x25
cnot 3 x25
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x24
cnot 3 x24
T* x24
cnot 4 x24
T* x24
cnot 3 x24
T x24
cnot 4 x24
cnot 3 4
H 4
T 3
S x23
cnot 3 x23
T* x23
S x3
cnot 3 x3
T* x3
cnot x23 x3
S* x3
cnot 3 x3
T x3
T 4
cnot x23 4
cnot 3 4
T* 4
cnot x3 4
cnot 3 4
T* 4
cnot x23 4
cnot 3 4
T 4
cnot x3 4
cnot x23 x3
cnot 3 x23
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x24
cnot 2 x24
T* x24
cnot 3 x24
T* x24
cnot 2 x24
T x24
cnot 3 x24
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x25
cnot 1 x25
T* x25
cnot 2 x25
T* x25
cnot 1 x25
T x25
cnot 2 x25
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 0
H x28
T 0
T x27
cnot 0 x27
T* x27
T x28
cnot 0 x28
T* x28
cnot x27 x28
T* x28
cnot 0 x28
T x28
cnot x27 x28
cnot 0 x27
H x28
H 0
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x25
cnot 1 x25
T* x25
cnot 2 x25
T* x25
cnot 1 x25
T x25
cnot 2 x25
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x24
cnot 2 x24
T* x24
cnot 3 x24
T* x24
cnot 2 x24
T x24
cnot 3 x24
cnot 2 3
H 3
T 2
S x23
cnot 2 x23
T* x23
S x3
cnot 2 x3
T* x3
cnot x23 x3
S* x3
cnot 2 x3
T x3
T 3
cnot x23 3
cnot 2 3
T* 3
cnot x3 3
cnot 2 3
T* 3
cnot x23 3
cnot 2 3
T 3
cnot x3 3
cnot x23 x3
cnot 2 3
cnot 2 x23
H 2
T 1
T 2
cnot 1 2
T* 2
T x24
cnot 1 x24
T* x24
cnot 2 x24
T* x24
cnot 1 x24
T x24
cnot 2 x24
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x25
cnot 0 x25
T* x25
cnot 1 x25
T* x25
cnot 0 x25
T x25
cnot 1 x25
cnot 0 1
H 0
H x27
T 0
T x26
cnot 0 x26
T* x26
T x27
cnot 0 x27
T* x27
cnot x26 x27
T* x27
cnot 0 x27
T x27
cnot x26 x27
cnot 0 x26
H x27
H 0
T 0
T 1
cnot 0 1
T* 1
T x25
cnot 0 x25
T* x25
cnot 1 x25
T* x25
cnot 0 x25
T x25
cnot 1 x25
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x24
cnot 1 x24
T* x24
cnot 2 x24
T* x24
cnot 1 x24
T x24
cnot 2 x24
cnot 1 2
H 2
T 1
S x23
cnot 1 x23
T* x23
S x3
cnot 1 x3
T* x3
cnot x23 x3
S* x3
cnot 1 x3
T x3
T 2
cnot x23 2
cnot 1 2
T* 2
cnot x3 2
cnot 1 2
T* 2
cnot x23 2
cnot 1 2
T 2
cnot x3 2
cnot x23 x3
cnot 1 x23
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x24
cnot 0 x24
T* x24
cnot 1 x24
T* x24
cnot 0 x24
T x24
cnot 1 x24
cnot 0 1
H 0
H x26
T 0
T x25
cnot 0 x25
T* x25
T x26
cnot 0 x26
T* x26
cnot x25 x26
T* x26
cnot 0 x26
T x26
cnot x25 x26
cnot 0 x25
H x26
H 0
T 0
T 1
cnot 0 1
T* 1
T x24
cnot 0 x24
T* x24
cnot 1 x24
T* x24
cnot 0 x24
T x24
cnot 1 x24
cnot 0 1
H 1
T 0
S x23
cnot 0 x23
T* x23
S x3
cnot 0 x3
T* x3
cnot x23 x3
S* x3
cnot 0 x3
T x3
T 1
cnot x23 1
cnot 0 1
T* 1
cnot x3 1
cnot 0 1
T* 1
cnot x23 1
cnot 0 1
T 1
cnot x3 1
cnot x23 x3
cnot 0 1
cnot 0 x23
H 0
H x25
T 0
T x24
cnot 0 x24
T* x24
T x25
cnot 0 x25
T* x25
cnot x24 x25
T* x25
cnot 0 x25
T x25
cnot x24 x25
cnot 0 x24
H x25
H 0
T 0
T x23
cnot 0 x23
T* x23
T x3
cnot 0 x3
T* x3
cnot x23 x3
T* x3
cnot 0 x3
T x3
cnot x23 x3
cnot 0 x23
H x24
T x23
T x24
cnot x23 x24
T* x24
T x3
cnot x23 x3
T* x3
cnot x24 x3
T* x3
cnot x23 x3
T x3
cnot x24 x3
cnot x23 x24
H x24
cnot x3 x23
H 16
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
T* 8
T bellA6
cnot 8 bellA6
T* bellA6
T x23
cnot 8 x23
T* x23
cnot bellA6 x23
T* x23
cnot 8 x23
T x23
T 13
cnot 8 13
T* 13
T x25
cnot 13 x25
T x25
cnot 8 x25
T* x25
cnot 13 x25
T* x25
T 11
cnot 8 11
T* 11
T x27
cnot 11 x27
T x27
cnot 8 x27
T* x27
cnot 11 x27
T* x27
T 9
cnot 8 9
T* 9
T x29
cnot 8 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
T x29
T x28
cnot 8 x28
T* x28
cnot 8 bellA0
T* bellA0
cnot x28 bellA0
T* bellA0
cnot 8 bellA0
T bellA0
T x26
cnot 8 x26
T* x26
cnot 8 bellA2
T* bellA2
cnot x26 bellA2
T* bellA2
cnot 8 bellA2
T bellA2
T x24
cnot 8 x24
T* x24
cnot 8 bellA4
T* bellA4
cnot x24 bellA4
T* bellA4
cnot 8 bellA4
T bellA4
cnot 8 11
cnot 8 13
cnot x24 bellA4
cnot x26 bellA2
cnot x28 bellA0
cnot bellA6 x23
cnot 9 x29
cnot 8 9
cnot 8 x28
cnot 8 x27
cnot 8 x26
cnot 8 x25
cnot 8 x24
cnot 8 bellA6
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
T 16
T x2
cnot 16 x2
T* x2
T x22
cnot 16 x22
T* x22
cnot x2 x22
T* x22
cnot 16 x22
T x22
T 10
T 12
T 14
cnot x2 x22
cnot 16 x2
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot x22 bellA9
measure bellA9
cnot bellA9 bellA8
S 11
T 8
Z 8
cnot 11 8
S* 8
S x26
cnot 11 x26
T* x26
cnot 8 x26
S* x26
cnot 11 x26
T x26
cnot 8 bellA2
cnot 11 bellA2
S* bellA2
cnot x26 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x25
cnot 8 x25
cnot 11 x25
S* x25
cnot x26 x25
cnot bellA2 x25
cnot 11 x25
T x25
cnot 8 x25
cnot 11 x25
T* x25
S 13
cnot 8 13
cnot 11 13
S* 13
cnot x26 13
cnot x25 13
cnot bellA2 13
cnot 11 13
T 13
cnot 8 13
cnot 11 13
T* 13
S x27
cnot 11 x27
T* x27
cnot 8 x27
S* x27
cnot 11 x27
T x27
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x27 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x28
cnot 8 x28
cnot 11 x28
S* x28
cnot x27 x28
cnot bellA0 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x28 9
cnot x27 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
S x24
cnot 8 x24
cnot 11 x24
S* x24
cnot x26 x24
cnot x25 x24
cnot bellA2 x24
cnot 13 x24
cnot 11 x24
T x24
cnot 8 x24
cnot 11 x24
T* x24
cnot 8 bellA4
cnot 11 bellA4
S* bellA4
cnot x26 bellA4
cnot x25 bellA4
cnot x24 bellA4
cnot bellA2 bellA4
cnot 13 bellA4
cnot 11 bellA4
T bellA4
cnot 8 bellA4
cnot 11 bellA4
T* bellA4
S x23
cnot 8 x23
cnot 11 x23
S* x23
cnot x26 x23
cnot x25 x23
cnot x24 x23
cnot bellA4 x23
cnot bellA2 x23
cnot 13 x23
cnot 11 x23
T x23
cnot 8 x23
cnot 11 x23
T* x23
S bellA6
cnot 8 bellA6
cnot 11 bellA6
T* bellA6
cnot x26 bellA6
cnot x25 bellA6
cnot x24 bellA6
cnot x23 bellA6
cnot bellA4 bellA6
cnot bellA2 bellA6
cnot 13 bellA6
cnot 11 bellA6
T bellA6
cnot 8 bellA6
cnot 11 bellA6
T* bellA6
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot x28 x29
cnot x27 x29
cnot bellA0 x29
cnot 9 x29
cnot 11 x29
T x29
cnot 8 x29
cnot 11 x29
T* x29
cnot x26 bellA8
cnot x25 bellA8
cnot x24 bellA8
cnot x23 bellA8
cnot bellA6 bellA8
cnot bellA4 bellA8
cnot bellA2 bellA8
cnot 13 bellA8
cnot 11 bellA8
T* bellA8
cnot x24 bellA4
cnot x26 bellA2
cnot x27 bellA0
cnot x23 bellA6
cnot bellA6 bellA8
cnot bellA0 x28
cnot bellA2 x25
cnot bellA4 x23
cnot bellA4 bellA8
cnot bellA4 bellA6
cnot x28 9
cnot 9 x29
cnot 8 x27
cnot 8 x26
cnot x25 13
cnot 13 x24
cnot 13 x23
cnot 13 bellA8
cnot 13 bellA6
cnot 13 bellA4
cnot 11 x29
cnot 11 x28
cnot 11 x25
cnot 11 x24
cnot 11 x23
cnot 11 bellA8
cnot 11 bellA6
cnot 11 bellA4
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
H bellA8
measure bellA8
cz bellA8 x22
T 16
S x2
cnot 16 x2
T* x2
S x22
cnot 16 x22
T* x22
cnot x2 x22
S* x22
cnot 16 x22
T x22
cnot 16 15
cnot x2 15
T* 15
cnot x22 15
cnot x2 15
T 15
S 10
S 12
S 14
cnot x22 15
cnot 16 15
cnot x2 x22
cnot 16 x2
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot x22 bellA9
measure bellA9
cnot bellA9 bellA8
S 11
T* 8
Z 8
cnot 11 8
S* 8
S x25
cnot 11 x25
T* x25
cnot 8 x25
S* x25
cnot 11 x25
T x25
cnot 8 bellA2
cnot 11 bellA2
S* bellA2
cnot x25 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x24
cnot 8 x24
cnot 11 x24
S* x24
cnot x25 x24
cnot bellA2 x24
cnot 11 x24
T x24
cnot 8 x24
cnot 11 x24
T* x24
S 13
cnot 8 13
cnot 11 13
S* 13
cnot x25 13
cnot x24 13
cnot bellA2 13
cnot 11 13
T 13
cnot 8 13
cnot 11 13
T* 13
S x26
cnot 11 x26
T* x26
cnot 8 x26
S* x26
cnot 11 x26
T x26
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x26 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x27
cnot 8 x27
cnot 11 x27
S* x27
cnot x26 x27
cnot bellA0 x27
cnot 11 x27
T x27
cnot 8 x27
cnot 11 x27
T* x27
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x27 9
cnot x26 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
S x23
cnot 8 x23
cnot 11 x23
S* x23
cnot x25 x23
cnot x24 x23
cnot bellA2 x23
cnot 13 x23
cnot 11 x23
T x23
cnot 8 x23
cnot 11 x23
T* x23
T x28
cnot 8 x28
cnot 11 x28
T* x28
cnot x27 x28
cnot x26 x28
cnot bellA0 x28
cnot 9 x28
cnot 11 x28
T x28
cnot 8 x28
cnot 11 x28
T* x28
cnot 8 bellA4
cnot 11 bellA4
T* bellA4
cnot x25 bellA4
cnot x24 bellA4
cnot x23 bellA4
cnot bellA2 bellA4
cnot 13 bellA4
cnot 11 bellA4
T bellA4
cnot 8 bellA4
cnot 11 bellA4
T* bellA4
T bellA6
cnot bellA6 bellA8
T* bellA8
cnot x23 bellA4
cnot x25 bellA2
cnot x26 bellA0
cnot bellA6 bellA8
cnot bellA0 x27
cnot bellA2 x24
cnot x27 9
cnot 9 x28
cnot 8 x26
cnot 8 x25
cnot x24 13
cnot 13 x23
cnot 13 bellA4
cnot 11 x28
cnot 11 x27
cnot 11 x24
cnot 11 x23
cnot 11 bellA4
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
H bellA8
measure bellA8
cz bellA8 x22
S 14
S x2
cnot 14 x2
T* x2
S x22
cnot 14 x22
T* x22
cnot x2 x22
S* x22
cnot 14 x22
T x22
cnot 14 15
cnot x2 15
T* 15
cnot x22 15
cnot x2 15
T 15
S 10
S 12
cnot x22 15
cnot x2 x22
cnot 14 x2
cnot 14 15
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x2 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot x22 bellA7
measure bellA7
cnot bellA7 bellA6
S 11
T 8
cnot 11 8
S* 8
S x24
cnot 11 x24
T* x24
cnot 8 x24
S* x24
cnot 11 x24
T x24
cnot 8 bellA2
cnot 11 bellA2
S* bellA2
cnot x24 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
S x23
cnot 8 x23
cnot 11 x23
S* x23
cnot x24 x23
cnot bellA2 x23
cnot 11 x23
T x23
cnot 8 x23
cnot 11 x23
T* x23
S 13
cnot 8 13
cnot 11 13
T* 13
cnot x24 13
cnot x23 13
cnot bellA2 13
cnot 11 13
T 13
cnot 8 13
cnot 11 13
T* 13
S x25
cnot 11 x25
T* x25
cnot 8 x25
S* x25
cnot 11 x25
T x25
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x25 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x26
cnot 8 x26
cnot 11 x26
S* x26
cnot x25 x26
cnot bellA0 x26
cnot 11 x26
T x26
cnot 8 x26
cnot 11 x26
T* x26
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x26 9
cnot x25 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x27
cnot 8 x27
cnot 11 x27
T* x27
cnot x26 x27
cnot x25 x27
cnot bellA0 x27
cnot 9 x27
cnot 11 x27
T x27
cnot 8 x27
cnot 11 x27
T* x27
cnot x24 bellA4
cnot x23 bellA4
cnot bellA2 bellA4
cnot 13 bellA4
cnot 11 bellA4
T* bellA4
cnot bellA4 bellA6
T bellA6
cnot x24 bellA6
cnot x23 bellA6
cnot bellA4 bellA6
cnot bellA2 bellA6
cnot 13 bellA6
cnot 11 bellA6
T* bellA6
cnot x24 bellA2
cnot x25 bellA0
cnot bellA0 x26
cnot bellA2 x23
cnot x26 9
cnot 9 x27
cnot 8 x25
cnot 8 x24
cnot x23 13
cnot 13 bellA6
cnot 13 bellA4
cnot 11 x27
cnot 11 x26
cnot 11 x23
cnot 11 bellA6
cnot 11 bellA4
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x2
H bellA6
measure bellA6
cz bellA6 x22
T 14
S x2
cnot 14 x2
T* x2
S x22
cnot 14 x22
T* x22
cnot x2 x22
S* x22
cnot 14 x22
T x22
S 10
S 12
cnot x2 x22
cnot 14 x2
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x2 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot x22 bellA7
measure bellA7
cnot bellA7 bellA6
S 11
T* 8
cnot 11 8
S* 8
S x24
cnot 11 x24
T* x24
cnot 8 x24
S* x24
cnot 11 x24
T x24
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x24 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x25
cnot 8 x25
cnot 11 x25
S* x25
cnot x24 x25
cnot bellA0 x25
cnot 11 x25
T x25
cnot 8 x25
cnot 11 x25
T* x25
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x25 9
cnot x24 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
S x23
cnot 11 x23
T* x23
cnot 8 x23
S* x23
cnot 11 x23
T x23
T x26
cnot 8 x26
cnot 11 x26
T* x26
cnot x25 x26
cnot x24 x26
cnot bellA0 x26
cnot 9 x26
cnot 11 x26
T x26
cnot 8 x26
cnot 11 x26
T* x26
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot x23 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
T 13
cnot 13 bellA4
T* bellA4
cnot 13 bellA6
T* bellA6
cnot bellA4 bellA6
cnot 13 bellA6
T bellA6
cnot x23 bellA2
cnot x24 bellA0
cnot bellA0 x25
cnot bellA4 bellA6
cnot x25 9
cnot 9 x26
cnot 8 x24
cnot 8 x23
cnot 13 bellA4
cnot 11 x26
cnot 11 x25
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x2
H bellA6
measure bellA6
cz bellA6 x22
S 12
S x2
cnot 12 x2
T* x2
S x22
cnot 12 x22
T* x22
cnot x2 x22
S* x22
cnot 12 x22
T x22
S 10
cnot x2 x22
cnot 12 x2
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x2 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x22 bellA5
measure bellA5
cnot bellA5 bellA4
S 11
T 8
Z 8
cnot 11 8
T* 8
S x23
cnot 11 x23
T* x23
cnot 8 x23
S* x23
cnot 11 x23
T x23
cnot 8 bellA0
cnot 11 bellA0
S* bellA0
cnot x23 bellA0
cnot 11 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
S x24
cnot 8 x24
cnot 11 x24
S* x24
cnot x23 x24
cnot bellA0 x24
cnot 11 x24
T x24
cnot 8 x24
cnot 11 x24
T* x24
S 9
cnot 8 9
cnot 11 9
S* 9
cnot x24 9
cnot x23 9
cnot bellA0 9
cnot 11 9
T 9
cnot 8 9
cnot 11 9
T* 9
T x25
cnot 8 x25
cnot 11 x25
T* x25
cnot x24 x25
cnot x23 x25
cnot bellA0 x25
cnot 9 x25
cnot 11 x25
T x25
cnot 8 x25
cnot 11 x25
T* x25
cnot 11 bellA2
T* bellA2
cnot 11 bellA4
T* bellA4
cnot bellA2 bellA4
cnot 11 bellA4
T bellA4
cnot x23 bellA0
cnot bellA2 bellA4
cnot bellA0 x24
cnot x24 9
cnot 9 x25
cnot 8 x23
cnot 11 x25
cnot 11 x24
cnot 11 bellA2
cnot 11 bellA0
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x2
H bellA4
measure bellA4
cz bellA4 x22
T 12
S x2
cnot 12 x2
T* x2
S x22
cnot 12 x22
T* x22
cnot x2 x22
S* x22
cnot 12 x22
T x22
S 10
cnot x2 x22
cnot 12 x2
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x23 x24
swap x13 x23
cnot x13 x25
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x23 x24
swap x13 x23
cnot x13 x25
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x2 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x22 bellA5
measure bellA5
cnot bellA5 bellA4
T* 8
Z 8
S 9
cnot 8 9
S* 9
S x23
cnot 8 x23
S* x23
cnot 9 x23
T* x23
cnot 8 x23
T x23
T x24
cnot 8 x24
T* x24
cnot 9 x24
T* x24
cnot 8 x24
T x24
cnot 8 bellA0
T* bellA0
cnot x23 bellA0
cnot 9 bellA0
T bellA0
cnot 8 bellA0
T* bellA0
T 11
cnot 11 bellA4
T* bellA4
cnot x23 bellA4
cnot bellA0 bellA4
cnot 9 bellA4
cnot 11 bellA4
T* bellA4
cnot 11 bellA2
T* bellA2
cnot x23 bellA2
cnot bellA4 bellA2
cnot bellA0 bellA2
cnot 9 bellA2
T bellA2
cnot x23 bellA0
cnot bellA4 bellA2
cnot bellA0 x24
cnot bellA0 x23
cnot 9 bellA0
cnot 8 9
cnot bellA0 x24
cnot bellA0 x23
cnot bellA0 bellA4
cnot bellA0 bellA2
cnot 11 bellA2
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x2
H bellA4
measure bellA4
cz bellA4 x22
S 10
S x22
S x2
cnot 10 x2
T* x2
cnot x22 x2
T x2
cnot 10 x2
S* x2
cnot x22 x2
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x13 x23
cnot x13 x24
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x25
cnot 7 x25
T* x25
cnot 8 x25
T* x25
cnot 7 x25
T x25
cnot 8 x25
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x25
cnot 7 x25
T* x25
cnot 8 x25
T* x25
cnot 7 x25
T x25
cnot 8 x25
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x13 x23
cnot x13 x24
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
S 9
cnot 8 9
T* 9
T x23
cnot 8 x23
T* x23
cnot 9 x23
T* x23
cnot 8 x23
T x23
T* bellA0
cnot 9 x23
cnot 8 9
H bellA0
measure bellA0
cz bellA0 10
cz bellA0 x22
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
T 10
S x22
cnot bellB0 x22
T* x22
S x2
cnot bellB0 x2
T* x2
cnot x22 x2
S* x2
cnot bellB0 x2
T x2
cnot 10 x2
cnot bellB0 x2
T x2
cnot x22 x2
cnot bellB0 x2
T* x2
cnot bellB0 x22
cnot 10 x2
H bellB0
measure bellB0
cz bellB0 9
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
cnot x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x24
cnot 7 x24
T* x24
cnot 8 x24
T* x24
cnot 7 x24
T x24
cnot 8 x24
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x25
cnot 6 x25
T* x25
cnot 7 x25
T* x25
cnot 6 x25
T x25
cnot 7 x25
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x25
cnot 6 x25
T* x25
cnot 7 x25
T* x25
cnot 6 x25
T x25
cnot 7 x25
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x24
cnot 7 x24
T* x24
cnot 8 x24
T* x24
cnot 7 x24
T x24
cnot 8 x24
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 8
T x23
cnot bellA0 x23
T* x23
cnot bellA2 x23
T x23
cnot bellA0 x23
T* x23
T 9
cnot bellA2 x23
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
S x2
cnot bellB0 x2
T* x2
S x22
cnot bellB0 x22
T* x22
cnot x2 x22
S* x22
cnot bellB0 x22
T x22
cnot x2 x22
cnot bellB0 x2
H bellB0
measure bellB0
cz bellB0 9
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
cnot x13 x23
swap 9 x13
swap 8 9
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H 8
T 7
T 8
cnot 7 8
T* 8
T x23
cnot 7 x23
T* x23
cnot 8 x23
T* x23
cnot 7 x23
T x23
cnot 8 x23
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x24
cnot 6 x24
T* x24
cnot 7 x24
T* x24
cnot 6 x24
T x24
cnot 7 x24
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x25
cnot 5 x25
T* x25
cnot 6 x25
T* x25
cnot 5 x25
T x25
cnot 6 x25
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x25
cnot 5 x25
T* x25
cnot 6 x25
T* x25
cnot 5 x25
T x25
cnot 6 x25
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x24
cnot 6 x24
T* x24
cnot 7 x24
T* x24
cnot 6 x24
T x24
cnot 7 x24
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x23
cnot 7 x23
T* x23
cnot 8 x23
T* x23
cnot 7 x23
T x23
cnot 8 x23
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 8
cnot bellA0 8
T* 8
cnot bellA2 8
T 8
cnot bellA0 8
T* 8
cnot bellA2 8
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
T x2
T x22
cnot x2 x22
T* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 7
cnot bellA0 7
T* 7
cnot bellA2 7
T 7
cnot bellA0 7
T* 7
cnot bellA2 7
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
T x2
T x22
cnot x2 x22
T* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 7
T 6
T 7
cnot 6 7
T* 7
T x23
cnot 6 x23
T* x23
cnot 7 x23
T* x23
cnot 6 x23
T x23
cnot 7 x23
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x24
cnot 5 x24
T* x24
cnot 6 x24
T* x24
cnot 5 x24
T x24
cnot 6 x24
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x25
cnot 4 x25
T* x25
cnot 5 x25
T* x25
cnot 4 x25
T x25
cnot 5 x25
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x25
cnot 4 x25
T* x25
cnot 5 x25
T* x25
cnot 4 x25
T x25
cnot 5 x25
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x24
cnot 5 x24
T* x24
cnot 6 x24
T* x24
cnot 5 x24
T x24
cnot 6 x24
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x23
cnot 6 x23
T* x23
cnot 7 x23
T* x23
cnot 6 x23
T x23
cnot 7 x23
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 6
T 7
cnot 6 bellA0
T* bellA0
cnot 7 bellA0
cnot 6 bellA0
T* bellA0
cnot 6 bellA2
T* bellA2
cnot 7 bellA2
cnot 6 bellA2
T* bellA2
cnot bellA0 bellA2
cnot 6 bellA2
T bellA2
cnot 7 bellA2
cnot 6 bellA2
T bellA2
cnot bellA0 bellA2
cnot 7 bellA0
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
S x2
S x22
cnot x2 x22
S* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 6
T 5
T 6
cnot 5 6
T* 6
T x23
cnot 5 x23
T* x23
cnot 6 x23
T* x23
cnot 5 x23
T x23
cnot 6 x23
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x24
cnot 4 x24
T* x24
cnot 5 x24
T* x24
cnot 4 x24
T x24
cnot 5 x24
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x25
cnot 3 x25
T* x25
cnot 4 x25
T* x25
cnot 3 x25
T x25
cnot 4 x25
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 0
H x30
T 0
T x29
cnot 0 x29
T* x29
T x30
cnot 0 x30
T* x30
cnot x29 x30
T* x30
cnot 0 x30
T x30
cnot x29 x30
cnot 0 x29
H x30
H 0
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x25
cnot 3 x25
T* x25
cnot 4 x25
T* x25
cnot 3 x25
T x25
cnot 4 x25
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x24
cnot 4 x24
T* x24
cnot 5 x24
T* x24
cnot 4 x24
T x24
cnot 5 x24
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x23
cnot 5 x23
T* x23
cnot 6 x23
T* x23
cnot 5 x23
T x23
cnot 6 x23
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 5
T 6
cnot 5 bellA0
T* bellA0
cnot 6 bellA0
cnot 5 bellA0
T* bellA0
cnot 5 bellA2
T* bellA2
cnot 6 bellA2
cnot 5 bellA2
T* bellA2
cnot bellA0 bellA2
cnot 5 bellA2
T bellA2
cnot 6 bellA2
cnot 5 bellA2
T bellA2
cnot bellA0 bellA2
cnot 6 bellA0
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
S x2
S x22
cnot x2 x22
S* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 5
T 4
T 5
cnot 4 5
T* 5
T x23
cnot 4 x23
T* x23
cnot 5 x23
T* x23
cnot 4 x23
T x23
cnot 5 x23
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x24
cnot 3 x24
T* x24
cnot 4 x24
T* x24
cnot 3 x24
T x24
cnot 4 x24
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x25
cnot 2 x25
T* x25
cnot 3 x25
T* x25
cnot 2 x25
T x25
cnot 3 x25
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 0
H x29
T 0
T x28
cnot 0 x28
T* x28
T x29
cnot 0 x29
T* x29
cnot x28 x29
T* x29
cnot 0 x29
T x29
cnot x28 x29
cnot 0 x28
H x29
H 0
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x25
cnot 2 x25
T* x25
cnot 3 x25
T* x25
cnot 2 x25
T x25
cnot 3 x25
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x24
cnot 3 x24
T* x24
cnot 4 x24
T* x24
cnot 3 x24
T x24
cnot 4 x24
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x23
cnot 4 x23
T* x23
cnot 5 x23
T* x23
cnot 4 x23
T x23
cnot 5 x23
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 4
T 5
cnot 4 bellA0
T* bellA0
cnot 5 bellA0
cnot 4 bellA0
T* bellA0
cnot 4 bellA2
T* bellA2
cnot 5 bellA2
cnot 4 bellA2
T* bellA2
cnot bellA0 bellA2
cnot 4 bellA2
T bellA2
cnot 5 bellA2
cnot 4 bellA2
T bellA2
cnot bellA0 bellA2
cnot 5 bellA0
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
S x2
S x22
cnot x2 x22
S* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 4
T 3
T 4
cnot 3 4
T* 4
T x23
cnot 3 x23
T* x23
cnot 4 x23
T* x23
cnot 3 x23
T x23
cnot 4 x23
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x24
cnot 2 x24
T* x24
cnot 3 x24
T* x24
cnot 2 x24
T x24
cnot 3 x24
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x25
cnot 1 x25
T* x25
cnot 2 x25
T* x25
cnot 1 x25
T x25
cnot 2 x25
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 0
H x28
T 0
T x27
cnot 0 x27
T* x27
T x28
cnot 0 x28
T* x28
cnot x27 x28
T* x28
cnot 0 x28
T x28
cnot x27 x28
cnot 0 x27
H x28
H 0
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x25
cnot 1 x25
T* x25
cnot 2 x25
T* x25
cnot 1 x25
T x25
cnot 2 x25
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x24
cnot 2 x24
T* x24
cnot 3 x24
T* x24
cnot 2 x24
T x24
cnot 3 x24
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x23
cnot 3 x23
T* x23
cnot 4 x23
T* x23
cnot 3 x23
T x23
cnot 4 x23
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 3
T 4
cnot 3 bellA0
T* bellA0
cnot 4 bellA0
cnot 3 bellA0
T* bellA0
cnot 3 bellA2
T* bellA2
cnot 4 bellA2
cnot 3 bellA2
T* bellA2
cnot bellA0 bellA2
cnot 3 bellA2
T bellA2
cnot 4 bellA2
cnot 3 bellA2
T bellA2
cnot bellA0 bellA2
cnot 4 bellA0
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
S x2
S x22
cnot x2 x22
S* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 3
T 2
T 3
cnot 2 3
T* 3
T x23
cnot 2 x23
T* x23
cnot 3 x23
T* x23
cnot 2 x23
T x23
cnot 3 x23
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x24
cnot 1 x24
T* x24
cnot 2 x24
T* x24
cnot 1 x24
T x24
cnot 2 x24
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x25
cnot 0 x25
T* x25
cnot 1 x25
T* x25
cnot 0 x25
T x25
cnot 1 x25
cnot 0 1
H 0
H x27
T 0
T x26
cnot 0 x26
T* x26
T x27
cnot 0 x27
T* x27
cnot x26 x27
T* x27
cnot 0 x27
T x27
cnot x26 x27
cnot 0 x26
H x27
H 0
T 0
T 1
cnot 0 1
T* 1
T x25
cnot 0 x25
T* x25
cnot 1 x25
T* x25
cnot 0 x25
T x25
cnot 1 x25
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x24
cnot 1 x24
T* x24
cnot 2 x24
T* x24
cnot 1 x24
T x24
cnot 2 x24
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x23
cnot 2 x23
T* x23
cnot 3 x23
T* x23
cnot 2 x23
T x23
cnot 3 x23
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 2
T 3
cnot 2 bellA0
T* bellA0
cnot 3 bellA0
cnot 2 bellA0
T* bellA0
cnot 2 bellA2
T* bellA2
cnot 3 bellA2
cnot 2 bellA2
T* bellA2
cnot bellA0 bellA2
cnot 2 bellA2
T bellA2
cnot 3 bellA2
cnot 2 bellA2
T bellA2
cnot bellA0 bellA2
cnot 3 bellA0
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
S x2
S x22
cnot x2 x22
S* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 2
T 1
T 2
cnot 1 2
T* 2
T x23
cnot 1 x23
T* x23
cnot 2 x23
T* x23
cnot 1 x23
T x23
cnot 2 x23
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x24
cnot 0 x24
T* x24
cnot 1 x24
T* x24
cnot 0 x24
T x24
cnot 1 x24
cnot 0 1
H 0
H x26
T 0
T x25
cnot 0 x25
T* x25
T x26
cnot 0 x26
T* x26
cnot x25 x26
T* x26
cnot 0 x26
T x26
cnot x25 x26
cnot 0 x25
H x26
H 0
T 0
T 1
cnot 0 1
T* 1
T x24
cnot 0 x24
T* x24
cnot 1 x24
T* x24
cnot 0 x24
T x24
cnot 1 x24
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x23
cnot 1 x23
T* x23
cnot 2 x23
T* x23
cnot 1 x23
T x23
cnot 2 x23
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 1
T 2
cnot 1 bellA0
T* bellA0
cnot 2 bellA0
cnot 1 bellA0
T* bellA0
cnot 1 bellA2
T* bellA2
cnot 2 bellA2
cnot 1 bellA2
T* bellA2
cnot bellA0 bellA2
cnot 1 bellA2
T bellA2
cnot 2 bellA2
cnot 1 bellA2
T bellA2
cnot bellA0 bellA2
cnot 2 bellA0
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
S x2
S x22
cnot x2 x22
S* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 1
T 0
T 1
cnot 0 1
T* 1
T x23
cnot 0 x23
T* x23
cnot 1 x23
T* x23
cnot 0 x23
T x23
cnot 1 x23
cnot 0 1
H 0
H x25
T 0
T x24
cnot 0 x24
T* x24
T x25
cnot 0 x25
T* x25
cnot x24 x25
T* x25
cnot 0 x25
T x25
cnot x24 x25
cnot 0 x24
H x25
H 0
T 0
T 1
cnot 0 1
T* 1
T x23
cnot 0 x23
T* x23
cnot 1 x23
T* x23
cnot 0 x23
T x23
cnot 1 x23
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
T 1
cnot 0 bellA0
T* bellA0
cnot 1 bellA0
cnot 0 bellA0
T* bellA0
cnot 0 bellA2
T* bellA2
cnot 1 bellA2
cnot 0 bellA2
T* bellA2
cnot bellA0 bellA2
cnot 0 bellA2
T bellA2
cnot 1 bellA2
cnot 0 bellA2
T bellA2
cnot bellA0 bellA2
cnot 1 bellA0
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
S x2
S x22
cnot x2 x22
S* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 0
H x24
T 0
T x23
cnot 0 x23
T* x23
T x24
cnot 0 x24
T* x24
cnot x23 x24
T* x24
cnot 0 x24
T x24
cnot x23 x24
cnot 0 x23
H x24
H 0
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
T x2
T x22
cnot x2 x22
T* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x23
H bellA0
cnot bellA0 bellA1
cnot x2 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T x23
cnot bellA0 x23
T* x23
cnot bellA2 x23
T x23
cnot bellA0 x23
T* x23
cnot bellA2 x23
H bellA0
measure bellA0
cz bellA0 x2
H bellA2
measure bellA2
cz bellA2 x22
T x2
T x22
cnot x2 x22
T* x22
cnot x2 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x23
cnot x2 x22
H 17
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot 16 bellA9
measure bellA9
cnot bellA9 bellA8
H bellA10
cnot bellA10 bellA11
cnot x1 bellA11
cnot x21 bellA11
measure bellA11
cnot bellA11 bellA10
H bellA12
cnot bellA12 bellA13
cnot x22 bellA13
measure bellA13
cnot bellA13 bellA12
T bellA6
cnot 8 bellA6
T* bellA6
T x23
cnot 8 x23
T* x23
cnot bellA6 x23
T* x23
cnot 8 x23
T x23
T 13
cnot 8 13
T* 13
T x25
cnot 13 x25
T x25
cnot 8 x25
T* x25
cnot 13 x25
T* x25
T 11
cnot 8 11
T* 11
T x27
cnot 11 x27
T x27
cnot 8 x27
T* x27
cnot 11 x27
T* x27
T 9
cnot 8 9
T* 9
T x29
cnot 8 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
T x29
T x28
cnot 8 x28
T* x28
cnot 8 bellA0
T* bellA0
cnot x28 bellA0
T* bellA0
cnot 8 bellA0
T bellA0
T x26
cnot 8 x26
T* x26
cnot 8 bellA2
T* bellA2
cnot x26 bellA2
T* bellA2
cnot 8 bellA2
T bellA2
T x24
cnot 8 x24
T* x24
cnot 8 bellA4
T* bellA4
cnot x24 bellA4
T* bellA4
cnot 8 bellA4
T bellA4
cnot 8 bellA12
T* bellA12
cnot 8 bellA8
T* bellA8
cnot bellA12 bellA8
cnot 8 bellA8
T bellA8
T* bellA10
cnot 8 11
cnot 8 13
cnot x28 bellA0
cnot x24 bellA4
cnot x26 bellA2
cnot bellA6 x23
cnot bellA12 bellA8
cnot 9 x29
cnot 8 9
cnot 8 x28
cnot 8 x27
cnot 8 x26
cnot 8 x25
cnot 8 x24
cnot 8 bellA6
cnot 8 bellA12
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
H bellA8
measure bellA8
cz bellA8 16
H bellA10
measure bellA10
cz bellA10 x1
cz bellA10 x21
H bellA12
measure bellA12
cz bellA12 x22
T x1
T x21
T 17
cnot x1 17
T* 17
cnot x21 17
T 17
cnot x1 17
T* 17
T 16
T x22
cnot 16 x22
T* x22
T 10
T 12
T 14
cnot x21 17
cnot 16 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
reset bellA10
reset bellA11
reset bellA12
reset bellA13
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 2
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 0
H bellA0
cnot bellA0 bellA1
cnot x40 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
cnot bellA0 0
H bellA0
measure bellA0
cz bellA0 x40
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x40
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
T x39
cnot bellB0 x39
T* x39
cnot x40 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H x40
H 0
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x38
T x38
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 2
T 2
T 3
cnot 2 3
T* 3
T x36
cnot 2 x36
T* x36
cnot 3 x36
T* x36
cnot 2 x36
T x36
cnot 3 x36
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x35
cnot 3 x35
T* x35
cnot 4 x35
T* x35
cnot 3 x35
T x35
cnot 4 x35
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x34
cnot 4 x34
T* x34
cnot 5 x34
T* x34
cnot 4 x34
T x34
cnot 5 x34
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x33
cnot 5 x33
T* x33
cnot 6 x33
T* x33
cnot 5 x33
T x33
cnot 6 x33
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x32
cnot 6 x32
T* x32
cnot 7 x32
T* x32
cnot 6 x32
T x32
cnot 7 x32
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x31
cnot 7 x31
T* x31
cnot 8 x31
T* x31
cnot 7 x31
T x31
cnot 8 x31
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x29 x3
swap x28 x29
cnot x28 x30
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot 16 bellA9
measure bellA9
cnot bellA9 bellA8
H bellA10
cnot bellA10 bellA11
cnot x1 bellA11
cnot x21 bellA11
measure bellA11
cnot bellA11 bellA10
H bellA12
cnot bellA12 bellA13
cnot x22 bellA13
measure bellA13
cnot bellA13 bellA12
T bellA6
cnot 8 bellA6
T* bellA6
T x23
cnot 8 x23
T* x23
cnot bellA6 x23
T* x23
cnot 8 x23
T x23
T 13
cnot 8 13
T* 13
T x25
cnot 13 x25
T x25
cnot 8 x25
T* x25
cnot 13 x25
T* x25
T 11
cnot 8 11
T* 11
T x27
cnot 11 x27
T x27
cnot 8 x27
T* x27
cnot 11 x27
T* x27
T 9
cnot 8 9
T* 9
T x29
cnot 8 x29
T* x29
cnot 9 x29
T* x29
cnot 8 x29
T x29
T x28
cnot 8 x28
T* x28
cnot 8 bellA0
T* bellA0
cnot x28 bellA0
T* bellA0
cnot 8 bellA0
T bellA0
T x26
cnot 8 x26
T* x26
cnot 8 bellA2
T* bellA2
cnot x26 bellA2
T* bellA2
cnot 8 bellA2
T bellA2
T x24
cnot 8 x24
T* x24
cnot 8 bellA4
T* bellA4
cnot x24 bellA4
T* bellA4
cnot 8 bellA4
T bellA4
cnot 8 bellA12
T* bellA12
cnot 8 bellA8
T* bellA8
cnot bellA12 bellA8
cnot 8 bellA8
T bellA8
T* bellA10
cnot 8 11
cnot 8 13
cnot x28 bellA0
cnot x24 bellA4
cnot x26 bellA2
cnot bellA6 x23
cnot bellA12 bellA8
cnot 9 x29
cnot 8 9
cnot 8 x28
cnot 8 x27
cnot 8 x26
cnot 8 x25
cnot 8 x24
cnot 8 bellA6
cnot 8 bellA12
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
H bellA8
measure bellA8
cz bellA8 16
H bellA10
measure bellA10
cz bellA10 x1
cz bellA10 x21
H bellA12
measure bellA12
cz bellA12 x22
T x1
T x21
T 17
cnot x1 17
T* 17
cnot x21 17
T 17
cnot x1 17
T* 17
T 16
T x22
cnot 16 x22
T* x22
T 10
T 12
T 14
cnot x21 17
cnot 16 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
reset bellA10
reset bellA11
reset bellA12
reset bellA13
H 17
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot x1 bellA9
cnot x21 bellA9
measure bellA9
cnot bellA9 bellA8
H bellA10
cnot bellA10 bellA11
cnot x22 bellA11
measure bellA11
cnot bellA11 bellA10
T 13
T* 8
cnot 13 8
T* 8
T x24
cnot 13 x24
T* x24
cnot 8 x24
T* x24
cnot 13 x24
T x24
T 11
cnot 8 11
cnot 13 11
T* 11
T x26
cnot 11 x26
T x26
cnot 8 x26
cnot 13 x26
T* x26
cnot 11 x26
T* x26
T 9
cnot 8 9
cnot 13 9
T* 9
T x28
cnot 8 x28
cnot 13 x28
T* x28
cnot 9 x28
T* x28
cnot 8 x28
cnot 13 x28
T x28
T x27
cnot 8 x27
cnot 13 x27
T* x27
cnot 8 bellA0
cnot 13 bellA0
T* bellA0
cnot x27 bellA0
T* bellA0
cnot 8 bellA0
cnot 13 bellA0
T bellA0
T bellA6
cnot 8 bellA6
cnot 13 bellA6
T* bellA6
cnot 8 bellA10
cnot 13 bellA10
T* bellA10
cnot bellA6 bellA10
T* bellA10
cnot 8 bellA10
cnot 13 bellA10
T bellA10
T x25
cnot 8 x25
cnot 13 x25
T* x25
cnot 8 bellA2
cnot 13 bellA2
T* bellA2
cnot x25 bellA2
T* bellA2
cnot 8 bellA2
cnot 13 bellA2
T bellA2
T x23
cnot 8 x23
cnot 13 x23
T* x23
cnot 8 bellA4
cnot 13 bellA4
T* bellA4
cnot x23 bellA4
T* bellA4
cnot 8 bellA4
cnot 13 bellA4
T bellA4
T* bellA8
cnot bellA6 bellA10
cnot x25 bellA2
cnot x27 bellA0
cnot x23 bellA4
cnot 9 x28
cnot 8 9
cnot 8 x27
cnot 8 x26
cnot 8 x25
cnot 8 x24
cnot 8 x23
cnot 8 bellA6
cnot 13 x27
cnot 13 x26
cnot 13 x25
cnot 13 x23
cnot 13 bellA6
cnot 13 9
cnot 13 8
cnot 8 11
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
H bellA8
measure bellA8
cz bellA8 x1
cz bellA8 x21
H bellA10
measure bellA10
cz bellA10 x22
T x1
T x21
T 16
cnot x1 16
T* 16
cnot x21 16
T 16
cnot x1 16
T* 16
T 10
T 12
T 14
T x22
cnot x21 16
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
reset bellA10
reset bellA11
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 1
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 0
H x39
H bellA0
cnot bellA0 bellA1
cnot x38 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x39 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x38
H bellA2
measure bellA2
cz bellA2 x39
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
T x38
T x39
cnot bellB0 x39
T* x39
cnot x38 x39
cnot bellB0 x39
T* x39
cnot x38 x39
H bellB0
measure bellB0
cz bellB0 0
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H x39
H 0
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x37
T x37
reset bellA0
reset bellA1
H 1
T 1
T 2
cnot 1 2
T* 2
T x36
cnot 1 x36
T* x36
cnot 2 x36
T* x36
cnot 1 x36
T x36
cnot 2 x36
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x35
cnot 2 x35
T* x35
cnot 3 x35
T* x35
cnot 2 x35
T x35
cnot 3 x35
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x34
cnot 3 x34
T* x34
cnot 4 x34
T* x34
cnot 3 x34
T x34
cnot 4 x34
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x33
cnot 4 x33
T* x33
cnot 5 x33
T* x33
cnot 4 x33
T x33
cnot 5 x33
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x32
cnot 5 x32
T* x32
cnot 6 x32
T* x32
cnot 5 x32
T x32
cnot 6 x32
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x31
cnot 6 x31
T* x31
cnot 7 x31
T* x31
cnot 6 x31
T x31
cnot 7 x31
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x30
cnot 7 x30
T* x30
cnot 8 x30
T* x30
cnot 7 x30
T x30
cnot 8 x30
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
cnot x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot x1 bellA9
cnot x21 bellA9
measure bellA9
cnot bellA9 bellA8
H bellA10
cnot bellA10 bellA11
cnot x22 bellA11
measure bellA11
cnot bellA11 bellA10
T 13
T* 8
cnot 13 8
T* 8
T x24
cnot 13 x24
T* x24
cnot 8 x24
T* x24
cnot 13 x24
T x24
T 11
cnot 8 11
cnot 13 11
T* 11
T x26
cnot 11 x26
T x26
cnot 8 x26
cnot 13 x26
T* x26
cnot 11 x26
T* x26
T 9
cnot 8 9
cnot 13 9
T* 9
T x28
cnot 8 x28
cnot 13 x28
T* x28
cnot 9 x28
T* x28
cnot 8 x28
cnot 13 x28
T x28
T x27
cnot 8 x27
cnot 13 x27
T* x27
cnot 8 bellA0
cnot 13 bellA0
T* bellA0
cnot x27 bellA0
T* bellA0
cnot 8 bellA0
cnot 13 bellA0
T bellA0
T bellA6
cnot 8 bellA6
cnot 13 bellA6
T* bellA6
cnot 8 bellA10
cnot 13 bellA10
T* bellA10
cnot bellA6 bellA10
T* bellA10
cnot 8 bellA10
cnot 13 bellA10
T bellA10
T x25
cnot 8 x25
cnot 13 x25
T* x25
cnot 8 bellA2
cnot 13 bellA2
T* bellA2
cnot x25 bellA2
T* bellA2
cnot 8 bellA2
cnot 13 bellA2
T bellA2
T x23
cnot 8 x23
cnot 13 x23
T* x23
cnot 8 bellA4
cnot 13 bellA4
T* bellA4
cnot x23 bellA4
T* bellA4
cnot 8 bellA4
cnot 13 bellA4
T bellA4
T* bellA8
cnot bellA6 bellA10
cnot x25 bellA2
cnot x27 bellA0
cnot x23 bellA4
cnot 9 x28
cnot 8 9
cnot 8 x27
cnot 8 x26
cnot 8 x25
cnot 8 x24
cnot 8 x23
cnot 8 bellA6
cnot 13 x27
cnot 13 x26
cnot 13 x25
cnot 13 x23
cnot 13 bellA6
cnot 13 9
cnot 13 8
cnot 8 11
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
H bellA8
measure bellA8
cz bellA8 x1
cz bellA8 x21
H bellA10
measure bellA10
cz bellA10 x22
T x1
T x21
T 16
cnot x1 16
T* 16
cnot x21 16
T 16
cnot x1 16
T* 16
T 10
T 12
T 14
T x22
cnot x21 16
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
reset bellA10
reset bellA11
H 16
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot x1 bellA9
cnot x21 bellA9
measure bellA9
cnot bellA9 bellA8
H bellA10
cnot bellA10 bellA11
cnot x22 bellA11
measure bellA11
cnot bellA11 bellA10
T 13
S* 8
cnot 13 8
T* 8
T x23
cnot 13 x23
T* x23
cnot 8 x23
T* x23
cnot 13 x23
T x23
T 11
cnot 8 11
cnot 13 11
T* 11
T x25
cnot 11 x25
T x25
cnot 8 x25
cnot 13 x25
T* x25
cnot 11 x25
T* x25
T 9
cnot 8 9
cnot 13 9
T* 9
T x27
cnot 8 x27
cnot 13 x27
T* x27
cnot 9 x27
T* x27
cnot 8 x27
cnot 13 x27
T x27
T x26
cnot 8 x26
cnot 13 x26
T* x26
cnot 8 bellA0
cnot 13 bellA0
T* bellA0
cnot x26 bellA0
T* bellA0
cnot 8 bellA0
cnot 13 bellA0
T bellA0
T x24
cnot 8 x24
cnot 13 x24
T* x24
cnot 8 bellA2
cnot 13 bellA2
T* bellA2
cnot x24 bellA2
T* bellA2
cnot 8 bellA2
cnot 13 bellA2
T bellA2
cnot 8 bellA10
cnot 13 bellA10
T* bellA10
cnot 8 bellA4
cnot 13 bellA4
T* bellA4
cnot bellA10 bellA4
cnot 8 bellA4
cnot 13 bellA4
T bellA4
T bellA6
T* bellA8
cnot x24 bellA2
cnot x26 bellA0
cnot bellA10 bellA4
cnot 9 x27
cnot 8 9
cnot 8 x26
cnot 8 x25
cnot 8 x24
cnot 8 x23
cnot 8 bellA10
cnot 13 x26
cnot 13 x25
cnot 13 x24
cnot 13 bellA10
cnot 13 9
cnot 13 8
cnot 8 11
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
H bellA8
measure bellA8
cz bellA8 x1
cz bellA8 x21
H bellA10
measure bellA10
cz bellA10 x22
T x1
cnot 15 x1
T* x1
T x21
cnot 15 x21
T* x21
cnot x1 x21
cnot 15 x21
T x21
T 14
T x22
cnot 14 x22
T* x22
T 10
T 12
cnot x1 x21
cnot 15 x1
cnot 14 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
reset bellA10
reset bellA11
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 0
H x38
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x38 bellA3
measure bellA3
cnot bellA3 bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
H bellA0
measure bellA0
cz bellA0 x37
H bellA2
measure bellA2
cz bellA2 x38
T x37
T x38
cnot x37 x38
T* x38
cnot x37 x38
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H x38
H 0
T 0
T 1
cnot 0 1
T* 1
T x36
cnot 0 x36
T* x36
cnot 1 x36
T* x36
cnot 0 x36
T x36
cnot 1 x36
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x35
cnot 1 x35
T* x35
cnot 2 x35
T* x35
cnot 1 x35
T x35
cnot 2 x35
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x34
cnot 2 x34
T* x34
cnot 3 x34
T* x34
cnot 2 x34
T x34
cnot 3 x34
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x33
cnot 3 x33
T* x33
cnot 4 x33
T* x33
cnot 3 x33
T x33
cnot 4 x33
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x32
cnot 4 x32
T* x32
cnot 5 x32
T* x32
cnot 4 x32
T x32
cnot 5 x32
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x31
cnot 5 x31
T* x31
cnot 6 x31
T* x31
cnot 5 x31
T x31
cnot 6 x31
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x30
cnot 6 x30
T* x30
cnot 7 x30
T* x30
cnot 6 x30
T x30
cnot 7 x30
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x29
cnot 7 x29
T* x29
cnot 8 x29
T* x29
cnot 7 x29
T x29
cnot 8 x29
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x26 x27
swap x25 x26
cnot x25 x28
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot 14 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot 15 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot x1 bellA9
cnot x21 bellA9
measure bellA9
cnot bellA9 bellA8
H bellA10
cnot bellA10 bellA11
cnot x22 bellA11
measure bellA11
cnot bellA11 bellA10
T 13
S* 8
cnot 13 8
T* 8
T x23
cnot 13 x23
T* x23
cnot 8 x23
T* x23
cnot 13 x23
T x23
T 11
cnot 8 11
cnot 13 11
T* 11
T x25
cnot 11 x25
T x25
cnot 8 x25
cnot 13 x25
T* x25
cnot 11 x25
T* x25
T 9
cnot 8 9
cnot 13 9
T* 9
T x27
cnot 8 x27
cnot 13 x27
T* x27
cnot 9 x27
T* x27
cnot 8 x27
cnot 13 x27
T x27
T x26
cnot 8 x26
cnot 13 x26
T* x26
cnot 8 bellA0
cnot 13 bellA0
T* bellA0
cnot x26 bellA0
T* bellA0
cnot 8 bellA0
cnot 13 bellA0
T bellA0
T x24
cnot 8 x24
cnot 13 x24
T* x24
cnot 8 bellA2
cnot 13 bellA2
T* bellA2
cnot x24 bellA2
T* bellA2
cnot 8 bellA2
cnot 13 bellA2
T bellA2
cnot 8 bellA10
cnot 13 bellA10
T* bellA10
cnot 8 bellA4
cnot 13 bellA4
T* bellA4
cnot bellA10 bellA4
cnot 8 bellA4
cnot 13 bellA4
T bellA4
T bellA6
T* bellA8
cnot x24 bellA2
cnot x26 bellA0
cnot bellA10 bellA4
cnot 9 x27
cnot 8 9
cnot 8 x26
cnot 8 x25
cnot 8 x24
cnot 8 x23
cnot 8 bellA10
cnot 13 x26
cnot 13 x25
cnot 13 x24
cnot 13 bellA10
cnot 13 9
cnot 13 8
cnot 8 11
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 14
H bellA6
measure bellA6
cz bellA6 15
H bellA8
measure bellA8
cz bellA8 x1
cz bellA8 x21
H bellA10
measure bellA10
cz bellA10 x22
T x1
cnot 15 x1
T* x1
T x21
cnot 15 x21
T* x21
cnot x1 x21
cnot 15 x21
T x21
T 14
T x22
cnot 14 x22
T* x22
T 10
T 12
cnot x1 x21
cnot 15 x1
cnot 14 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
reset bellA10
reset bellA11
H 15
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x1 bellA5
cnot x21 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot x22 bellA7
measure bellA7
cnot bellA7 bellA6
T 11
T 8
Z 8
cnot 11 8
T* 8
T x24
cnot 11 x24
T* x24
cnot 8 x24
T* x24
cnot 11 x24
T x24
T 9
cnot 8 9
cnot 11 9
T* 9
T x26
cnot 8 x26
cnot 11 x26
T* x26
cnot 9 x26
T* x26
cnot 8 x26
cnot 11 x26
T x26
T x25
cnot 8 x25
cnot 11 x25
T* x25
cnot 8 bellA0
cnot 11 bellA0
T* bellA0
cnot x25 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
T x23
cnot 8 x23
cnot 11 x23
T* x23
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot x23 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
T 13
cnot 8 13
cnot 11 13
T* 13
cnot 13 bellA6
T bellA6
cnot 8 bellA6
cnot 11 bellA6
T* bellA6
cnot 13 bellA6
T* bellA6
T* bellA4
cnot 8 13
cnot x23 bellA2
cnot x25 bellA0
cnot 9 x26
cnot 8 9
cnot 8 x25
cnot 8 x24
cnot 8 x23
cnot 8 bellA6
cnot 11 x25
cnot 11 x23
cnot 11 bellA6
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x1
cz bellA4 x21
H bellA6
measure bellA6
cz bellA6 x22
T x1
T x21
T 14
cnot x1 14
T* 14
cnot x21 14
T 14
cnot x1 14
T* 14
T 10
T 12
T x22
cnot x21 14
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 0
H x37
H bellA0
cnot bellA0 bellA1
cnot x37 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
T x36
cnot 0 x36
T* x36
cnot 0 bellA0
T* bellA0
cnot 0 x36
cnot 0 bellA0
H bellA0
measure bellA0
cz bellA0 x37
H bellB0
cnot bellB0 bellB1
cnot 0 bellB1
measure bellB1
cnot bellB1 bellB0
H bellB2
cnot bellB2 bellB3
cnot x36 bellB3
measure bellB3
cnot bellB3 bellB2
T x37
cnot bellB2 x37
T* x37
cnot bellB0 x37
T x37
cnot bellB2 x37
cnot bellB0 x37
H bellB0
measure bellB0
cz bellB0 0
H bellB2
measure bellB2
cz bellB2 x36
reset bellA0
reset bellA1
reset bellB0
reset bellB1
reset bellB2
reset bellB3
H x37
H 0
T 0
T 1
cnot 0 1
T* 1
T x35
cnot 0 x35
T* x35
cnot 1 x35
T* x35
cnot 0 x35
T x35
cnot 1 x35
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x34
cnot 1 x34
T* x34
cnot 2 x34
T* x34
cnot 1 x34
T x34
cnot 2 x34
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x33
cnot 2 x33
T* x33
cnot 3 x33
T* x33
cnot 2 x33
T x33
cnot 3 x33
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x32
cnot 3 x32
T* x32
cnot 4 x32
T* x32
cnot 3 x32
T x32
cnot 4 x32
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x31
cnot 4 x31
T* x31
cnot 5 x31
T* x31
cnot 4 x31
T x31
cnot 5 x31
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x30
cnot 5 x30
T* x30
cnot 6 x30
T* x30
cnot 5 x30
T x30
cnot 6 x30
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x29
cnot 6 x29
T* x29
cnot 7 x29
T* x29
cnot 6 x29
T x29
cnot 7 x29
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x28
cnot 7 x28
T* x28
cnot 8 x28
T* x28
cnot 7 x28
T x28
cnot 8 x28
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x25 x26
cnot x25 x27
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x1 bellA5
cnot x21 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot x22 bellA7
measure bellA7
cnot bellA7 bellA6
T 11
T 8
Z 8
cnot 11 8
T* 8
T x24
cnot 11 x24
T* x24
cnot 8 x24
T* x24
cnot 11 x24
T x24
T 9
cnot 8 9
cnot 11 9
T* 9
T x26
cnot 8 x26
cnot 11 x26
T* x26
cnot 9 x26
T* x26
cnot 8 x26
cnot 11 x26
T x26
T x25
cnot 8 x25
cnot 11 x25
T* x25
cnot 8 bellA0
cnot 11 bellA0
T* bellA0
cnot x25 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
T x23
cnot 8 x23
cnot 11 x23
T* x23
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot x23 bellA2
T* bellA2
cnot 8 bellA2
cnot 11 bellA2
T bellA2
T 13
cnot 8 13
cnot 11 13
T* 13
cnot 13 bellA6
T bellA6
cnot 8 bellA6
cnot 11 bellA6
T* bellA6
cnot 13 bellA6
T* bellA6
T* bellA4
cnot 8 13
cnot x23 bellA2
cnot x25 bellA0
cnot 9 x26
cnot 8 9
cnot 8 x25
cnot 8 x24
cnot 8 x23
cnot 8 bellA6
cnot 11 x25
cnot 11 x23
cnot 11 bellA6
cnot 11 9
cnot 11 8
cnot 11 13
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x1
cz bellA4 x21
H bellA6
measure bellA6
cz bellA6 x22
T x1
T x21
T 14
cnot x1 14
T* 14
cnot x21 14
T 14
cnot x1 14
T* 14
T 10
T 12
T x22
cnot x21 14
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 14
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x1 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot x21 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot x22 bellA9
measure bellA9
cnot bellA9 bellA8
T 11
Z 8
cnot 11 8
T* 8
T x23
cnot 11 x23
T* x23
cnot 8 x23
T* x23
cnot 11 x23
T x23
T 9
cnot 8 9
cnot 11 9
T* 9
T x25
cnot 8 x25
cnot 11 x25
T* x25
cnot 9 x25
T* x25
cnot 8 x25
cnot 11 x25
T x25
T x24
cnot 8 x24
cnot 11 x24
T* x24
cnot 8 bellA0
cnot 11 bellA0
T* bellA0
cnot x24 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
T 13
cnot 13 bellA4
T* bellA4
cnot 13 bellA6
T* bellA6
cnot bellA4 bellA6
T* bellA6
cnot 13 bellA6
T bellA6
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA8
cnot 11 bellA8
T* bellA8
cnot bellA2 bellA8
cnot 8 bellA8
cnot 11 bellA8
T bellA8
cnot x24 bellA0
cnot bellA2 bellA8
cnot bellA4 bellA6
cnot 9 x25
cnot 8 9
cnot 8 x24
cnot 8 x23
cnot 8 bellA2
cnot 13 bellA4
cnot 11 x24
cnot 11 bellA2
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x1
H bellA6
measure bellA6
cz bellA6 x21
H bellA8
measure bellA8
cz bellA8 x22
T 12
T x22
cnot 12 x22
T* x22
T 10
T x1
T x21
cnot 12 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 0
H x36
T 0
T x35
cnot 0 x35
T* x35
T x36
cnot 0 x36
T* x36
cnot x35 x36
T* x36
cnot 0 x36
T x36
cnot x35 x36
cnot 0 x35
H x36
H 0
T 0
T 1
cnot 0 1
T* 1
T x34
cnot 0 x34
T* x34
cnot 1 x34
T* x34
cnot 0 x34
T x34
cnot 1 x34
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x33
cnot 1 x33
T* x33
cnot 2 x33
T* x33
cnot 1 x33
T x33
cnot 2 x33
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x32
cnot 2 x32
T* x32
cnot 3 x32
T* x32
cnot 2 x32
T x32
cnot 3 x32
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x31
cnot 3 x31
T* x31
cnot 4 x31
T* x31
cnot 3 x31
T x31
cnot 4 x31
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x30
cnot 4 x30
T* x30
cnot 5 x30
T* x30
cnot 4 x30
T x30
cnot 5 x30
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x29
cnot 5 x29
T* x29
cnot 6 x29
T* x29
cnot 5 x29
T x29
cnot 6 x29
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x28
cnot 6 x28
T* x28
cnot 7 x28
T* x28
cnot 6 x28
T x28
cnot 7 x28
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x27
cnot 7 x27
T* x27
cnot 8 x27
T* x27
cnot 7 x27
T x27
cnot 8 x27
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
cnot x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot 12 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x1 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot x21 bellA7
measure bellA7
cnot bellA7 bellA6
H bellA8
cnot bellA8 bellA9
cnot x22 bellA9
measure bellA9
cnot bellA9 bellA8
T 11
Z 8
cnot 11 8
T* 8
T x23
cnot 11 x23
T* x23
cnot 8 x23
T* x23
cnot 11 x23
T x23
T 9
cnot 8 9
cnot 11 9
T* 9
T x25
cnot 8 x25
cnot 11 x25
T* x25
cnot 9 x25
T* x25
cnot 8 x25
cnot 11 x25
T x25
T x24
cnot 8 x24
cnot 11 x24
T* x24
cnot 8 bellA0
cnot 11 bellA0
T* bellA0
cnot x24 bellA0
T* bellA0
cnot 8 bellA0
cnot 11 bellA0
T bellA0
T 13
cnot 13 bellA4
T* bellA4
cnot 13 bellA6
T* bellA6
cnot bellA4 bellA6
T* bellA6
cnot 13 bellA6
T bellA6
cnot 8 bellA2
cnot 11 bellA2
T* bellA2
cnot 8 bellA8
cnot 11 bellA8
T* bellA8
cnot bellA2 bellA8
cnot 8 bellA8
cnot 11 bellA8
T bellA8
cnot x24 bellA0
cnot bellA2 bellA8
cnot bellA4 bellA6
cnot 9 x25
cnot 8 9
cnot 8 x24
cnot 8 x23
cnot 8 bellA2
cnot 13 bellA4
cnot 11 x24
cnot 11 bellA2
cnot 11 9
cnot 11 8
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 12
H bellA4
measure bellA4
cz bellA4 x1
H bellA6
measure bellA6
cz bellA6 x21
H bellA8
measure bellA8
cz bellA8 x22
T 12
T x22
cnot 12 x22
T* x22
T 10
T x1
T x21
cnot 12 x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
reset bellA8
reset bellA9
H 13
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x1 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x22 bellA5
measure bellA5
cnot bellA5 bellA4
T* 8
Z 8
T 9
cnot 8 9
T* 9
T x24
cnot 8 x24
T* x24
cnot 9 x24
T* x24
cnot 8 x24
T x24
T x23
cnot 8 x23
T* x23
cnot 8 bellA0
T* bellA0
cnot x23 bellA0
T* bellA0
cnot 8 bellA0
T bellA0
T 11
cnot 8 11
T* 11
cnot 11 bellA4
T bellA4
cnot 8 bellA4
T* bellA4
cnot 11 bellA4
T* bellA4
T* bellA2
cnot 8 11
cnot x23 bellA0
cnot 9 x24
cnot 8 9
cnot 8 x23
cnot 8 bellA4
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x1
cz bellA2 x21
H bellA4
measure bellA4
cz bellA4 x22
T x1
T x21
T 12
cnot x1 12
T* 12
cnot x21 12
T 12
cnot x1 12
T* 12
T 10
T x22
cnot x21 12
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x23 x24
swap x13 x23
cnot x13 x25
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 0
H x35
T 0
T x34
cnot 0 x34
T* x34
T x35
cnot 0 x35
T* x35
cnot x34 x35
T* x35
cnot 0 x35
T x35
cnot x34 x35
cnot 0 x34
H x35
H 0
T 0
T 1
cnot 0 1
T* 1
T x33
cnot 0 x33
T* x33
cnot 1 x33
T* x33
cnot 0 x33
T x33
cnot 1 x33
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x32
cnot 1 x32
T* x32
cnot 2 x32
T* x32
cnot 1 x32
T x32
cnot 2 x32
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x31
cnot 2 x31
T* x31
cnot 3 x31
T* x31
cnot 2 x31
T x31
cnot 3 x31
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x30
cnot 3 x30
T* x30
cnot 4 x30
T* x30
cnot 3 x30
T x30
cnot 4 x30
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x29
cnot 4 x29
T* x29
cnot 5 x29
T* x29
cnot 4 x29
T x29
cnot 5 x29
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x28
cnot 5 x28
T* x28
cnot 6 x28
T* x28
cnot 5 x28
T x28
cnot 6 x28
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x27
cnot 6 x27
T* x27
cnot 7 x27
T* x27
cnot 6 x27
T x27
cnot 7 x27
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x26
cnot 7 x26
T* x26
cnot 8 x26
T* x26
cnot 7 x26
T x26
cnot 8 x26
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x23 x24
swap x13 x23
cnot x13 x25
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x1 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x22 bellA5
measure bellA5
cnot bellA5 bellA4
T* 8
Z 8
T 9
cnot 8 9
T* 9
T x24
cnot 8 x24
T* x24
cnot 9 x24
T* x24
cnot 8 x24
T x24
T x23
cnot 8 x23
T* x23
cnot 8 bellA0
T* bellA0
cnot x23 bellA0
T* bellA0
cnot 8 bellA0
T bellA0
T 11
cnot 8 11
T* 11
cnot 11 bellA4
T bellA4
cnot 8 bellA4
T* bellA4
cnot 11 bellA4
T* bellA4
T* bellA2
cnot 8 11
cnot x23 bellA0
cnot 9 x24
cnot 8 9
cnot 8 x23
cnot 8 bellA4
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x1
cz bellA2 x21
H bellA4
measure bellA4
cz bellA4 x22
T x1
T x21
T 12
cnot x1 12
T* 12
cnot x21 12
T 12
cnot x1 12
T* 12
T 10
T x22
cnot x21 12
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
H 12
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x1 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x21 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot x22 bellA7
measure bellA7
cnot bellA7 bellA6
S 8
T 9
cnot 8 9
T* 9
T x23
cnot 8 x23
T* x23
cnot 9 x23
T* x23
cnot 8 x23
T x23
T 11
cnot 11 bellA2
T* bellA2
cnot 11 bellA4
T* bellA4
cnot bellA2 bellA4
T* bellA4
cnot 11 bellA4
T bellA4
cnot 8 bellA0
T* bellA0
cnot 8 bellA6
T* bellA6
cnot bellA0 bellA6
T* bellA6
cnot 8 bellA6
T bellA6
cnot bellA2 bellA4
cnot bellA0 bellA6
cnot 9 x23
cnot 8 9
cnot 8 bellA0
cnot 11 bellA2
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x1
H bellA4
measure bellA4
cz bellA4 x21
H bellA6
measure bellA6
cz bellA6 x22
T 10
T x1
T x21
T x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x13 x23
cnot x13 x24
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x25
cnot 7 x25
T* x25
cnot 8 x25
T* x25
cnot 7 x25
T x25
cnot 8 x25
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 0
H x34
T 0
T x33
cnot 0 x33
T* x33
T x34
cnot 0 x34
T* x34
cnot x33 x34
T* x34
cnot 0 x34
T x34
cnot x33 x34
cnot 0 x33
H x34
H 0
T 0
T 1
cnot 0 1
T* 1
T x32
cnot 0 x32
T* x32
cnot 1 x32
T* x32
cnot 0 x32
T x32
cnot 1 x32
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x31
cnot 1 x31
T* x31
cnot 2 x31
T* x31
cnot 1 x31
T x31
cnot 2 x31
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x30
cnot 2 x30
T* x30
cnot 3 x30
T* x30
cnot 2 x30
T x30
cnot 3 x30
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x29
cnot 3 x29
T* x29
cnot 4 x29
T* x29
cnot 3 x29
T x29
cnot 4 x29
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x28
cnot 4 x28
T* x28
cnot 5 x28
T* x28
cnot 4 x28
T x28
cnot 5 x28
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x27
cnot 5 x27
T* x27
cnot 6 x27
T* x27
cnot 5 x27
T x27
cnot 6 x27
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x26
cnot 6 x26
T* x26
cnot 7 x26
T* x26
cnot 6 x26
T x26
cnot 7 x26
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x25
cnot 7 x25
T* x25
cnot 8 x25
T* x25
cnot 7 x25
T x25
cnot 8 x25
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x13 x23
cnot x13 x24
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot 10 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x1 bellA3
measure bellA3
cnot bellA3 bellA2
H bellA4
cnot bellA4 bellA5
cnot x21 bellA5
measure bellA5
cnot bellA5 bellA4
H bellA6
cnot bellA6 bellA7
cnot x22 bellA7
measure bellA7
cnot bellA7 bellA6
S 8
T 9
cnot 8 9
T* 9
T x23
cnot 8 x23
T* x23
cnot 9 x23
T* x23
cnot 8 x23
T x23
T 11
cnot 11 bellA2
T* bellA2
cnot 11 bellA4
T* bellA4
cnot bellA2 bellA4
T* bellA4
cnot 11 bellA4
T bellA4
cnot 8 bellA0
T* bellA0
cnot 8 bellA6
T* bellA6
cnot bellA0 bellA6
T* bellA6
cnot 8 bellA6
T bellA6
cnot bellA2 bellA4
cnot bellA0 bellA6
cnot 9 x23
cnot 8 9
cnot 8 bellA0
cnot 11 bellA2
H bellA0
measure bellA0
cz bellA0 10
H bellA2
measure bellA2
cz bellA2 x1
H bellA4
measure bellA4
cz bellA4 x21
H bellA6
measure bellA6
cz bellA6 x22
T 10
T x1
T x21
T x22
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellA4
reset bellA5
reset bellA6
reset bellA7
H 11
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
cnot x21 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 9
T 8
cnot 9 8
T* 8
cnot bellA2 8
T 8
cnot 9 8
T* 8
T* bellA0
cnot bellA2 8
H bellA0
measure bellA0
cz bellA0 x1
cz bellA0 x21
H bellA2
measure bellA2
cz bellA2 x22
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
T x1
T x21
T 10
cnot x1 10
T* 10
cnot x21 10
T 10
cnot x1 10
T* 10
T x22
cnot x22 bellB0
T* bellB0
cnot x21 10
cnot x22 bellB0
H bellB0
measure bellB0
cz bellB0 9
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
cnot x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x24
cnot 7 x24
T* x24
cnot 8 x24
T* x24
cnot 7 x24
T x24
cnot 8 x24
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x25
cnot 6 x25
T* x25
cnot 7 x25
T* x25
cnot 6 x25
T x25
cnot 7 x25
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 0
H x33
T 0
T x32
cnot 0 x32
T* x32
T x33
cnot 0 x33
T* x33
cnot x32 x33
T* x33
cnot 0 x33
T x33
cnot x32 x33
cnot 0 x32
H x33
H 0
T 0
T 1
cnot 0 1
T* 1
T x31
cnot 0 x31
T* x31
cnot 1 x31
T* x31
cnot 0 x31
T x31
cnot 1 x31
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x30
cnot 1 x30
T* x30
cnot 2 x30
T* x30
cnot 1 x30
T x30
cnot 2 x30
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x29
cnot 2 x29
T* x29
cnot 3 x29
T* x29
cnot 2 x29
T x29
cnot 3 x29
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x28
cnot 3 x28
T* x28
cnot 4 x28
T* x28
cnot 3 x28
T x28
cnot 4 x28
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x27
cnot 4 x27
T* x27
cnot 5 x27
T* x27
cnot 4 x27
T x27
cnot 5 x27
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x26
cnot 5 x26
T* x26
cnot 6 x26
T* x26
cnot 5 x26
T x26
cnot 6 x26
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x25
cnot 6 x25
T* x25
cnot 7 x25
T* x25
cnot 6 x25
T x25
cnot 7 x25
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x24
cnot 7 x24
T* x24
cnot 8 x24
T* x24
cnot 7 x24
T x24
cnot 8 x24
cnot 7 8
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
cnot x13 x23
swap 9 x13
swap 8 9
H 8
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
cnot x21 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x22 bellA3
measure bellA3
cnot bellA3 bellA2
T 9
T 8
cnot 9 8
T* 8
cnot bellA2 8
T 8
cnot 9 8
T* 8
T* bellA0
cnot bellA2 8
H bellA0
measure bellA0
cz bellA0 x1
cz bellA0 x21
H bellA2
measure bellA2
cz bellA2 x22
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
T x1
T x21
T 10
cnot x1 10
T* 10
cnot x21 10
T 10
cnot x1 10
T* 10
T x22
cnot x22 bellB0
T* bellB0
cnot x21 10
cnot x22 bellB0
H bellB0
measure bellB0
cz bellB0 9
reset bellA0
reset bellA1
reset bellA2
reset bellA3
reset bellB0
reset bellB1
H 10
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
cnot x21 bellA1
measure bellA1
cnot bellA1 bellA0
T 9
T* bellA0
H bellA0
measure bellA0
cz bellA0 x1
cz bellA0 x21
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
T x1
cnot bellB0 x1
T* x1
T x21
cnot bellB0 x21
T* x21
cnot x1 x21
cnot bellB0 x21
T x21
cnot x1 x21
cnot bellB0 x1
H bellB0
measure bellB0
cz bellB0 9
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 8
T 8
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
H 8
T 7
T 8
cnot 7 8
T* 8
T x23
cnot 7 x23
T* x23
cnot 8 x23
T* x23
cnot 7 x23
T x23
cnot 8 x23
cnot 7 8
H 7
T 6
T 7
cnot 6 7
T* 7
T x24
cnot 6 x24
T* x24
cnot 7 x24
T* x24
cnot 6 x24
T x24
cnot 7 x24
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x25
cnot 5 x25
T* x25
cnot 6 x25
T* x25
cnot 5 x25
T x25
cnot 6 x25
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 0
H x32
T 0
T x31
cnot 0 x31
T* x31
T x32
cnot 0 x32
T* x32
cnot x31 x32
T* x32
cnot 0 x32
T x32
cnot x31 x32
cnot 0 x31
H x32
H 0
T 0
T 1
cnot 0 1
T* 1
T x30
cnot 0 x30
T* x30
cnot 1 x30
T* x30
cnot 0 x30
T x30
cnot 1 x30
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x29
cnot 1 x29
T* x29
cnot 2 x29
T* x29
cnot 1 x29
T x29
cnot 2 x29
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x28
cnot 2 x28
T* x28
cnot 3 x28
T* x28
cnot 2 x28
T x28
cnot 3 x28
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x27
cnot 3 x27
T* x27
cnot 4 x27
T* x27
cnot 3 x27
T x27
cnot 4 x27
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x26
cnot 4 x26
T* x26
cnot 5 x26
T* x26
cnot 4 x26
T x26
cnot 5 x26
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x25
cnot 5 x25
T* x25
cnot 6 x25
T* x25
cnot 5 x25
T x25
cnot 6 x25
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x24
cnot 6 x24
T* x24
cnot 7 x24
T* x24
cnot 6 x24
T x24
cnot 7 x24
cnot 6 7
H 7
T 7
T 8
cnot 7 8
T* 8
T x23
cnot 7 x23
T* x23
cnot 8 x23
T* x23
cnot 7 x23
T x23
cnot 8 x23
cnot 7 8
H 8
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
cnot x21 bellA1
measure bellA1
cnot bellA1 bellA0
T 8
T 9
T* bellA0
H bellA0
measure bellA0
cz bellA0 x1
cz bellA0 x21
H bellB0
cnot bellB0 bellB1
cnot 9 bellB1
measure bellB1
cnot bellB1 bellB0
T x1
cnot bellB0 x1
T* x1
T x21
cnot bellB0 x21
T* x21
cnot x1 x21
cnot bellB0 x21
T x21
cnot x1 x21
cnot bellB0 x1
H bellB0
measure bellB0
cz bellB0 9
swap x36 x4
swap x35 x36
swap x34 x35
swap x33 x34
swap x32 x33
swap x31 x32
swap x30 x31
swap x3 x30
swap x29 x3
swap x28 x29
swap x27 x28
swap x26 x27
swap x25 x26
swap x24 x25
swap x23 x24
swap x13 x23
swap 9 x13
swap 8 9
reset bellA0
reset bellA1
reset bellB0
reset bellB1
H 9
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 8
cnot bellA0 8
T* 8
cnot bellA2 8
T* 8
cnot bellA0 8
T 8
cnot bellA2 8
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
cnot bellA0 7
T* 7
T 8
cnot 7 8
T 8
cnot bellA0 8
T* 8
cnot 7 8
T* 8
cnot bellA0 7
cnot bellA0 8
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 7
T 6
T 7
cnot 6 7
T* 7
T x23
cnot 6 x23
T* x23
cnot 7 x23
T* x23
cnot 6 x23
T x23
cnot 7 x23
cnot 6 7
H 6
T 5
T 6
cnot 5 6
T* 6
T x24
cnot 5 x24
T* x24
cnot 6 x24
T* x24
cnot 5 x24
T x24
cnot 6 x24
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x25
cnot 4 x25
T* x25
cnot 5 x25
T* x25
cnot 4 x25
T x25
cnot 5 x25
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 0
H x31
T 0
T x30
cnot 0 x30
T* x30
T x31
cnot 0 x31
T* x31
cnot x30 x31
T* x31
cnot 0 x31
T x31
cnot x30 x31
cnot 0 x30
H x31
H 0
T 0
T 1
cnot 0 1
T* 1
T x29
cnot 0 x29
T* x29
cnot 1 x29
T* x29
cnot 0 x29
T x29
cnot 1 x29
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x28
cnot 1 x28
T* x28
cnot 2 x28
T* x28
cnot 1 x28
T x28
cnot 2 x28
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x27
cnot 2 x27
T* x27
cnot 3 x27
T* x27
cnot 2 x27
T x27
cnot 3 x27
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x26
cnot 3 x26
T* x26
cnot 4 x26
T* x26
cnot 3 x26
T x26
cnot 4 x26
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x25
cnot 4 x25
T* x25
cnot 5 x25
T* x25
cnot 4 x25
T x25
cnot 5 x25
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x24
cnot 5 x24
T* x24
cnot 6 x24
T* x24
cnot 5 x24
T x24
cnot 6 x24
cnot 5 6
H 6
T 6
T 7
cnot 6 7
T* 7
T x23
cnot 6 x23
T* x23
cnot 7 x23
T* x23
cnot 6 x23
T x23
cnot 7 x23
cnot 6 7
H 7
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 7
cnot bellA0 7
T* 7
T 8
cnot 7 8
T 8
cnot bellA0 8
T* 8
cnot 7 8
T* 8
cnot bellA0 7
cnot bellA0 8
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 8
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 8
cnot bellA0 8
T* 8
cnot bellA2 8
T* 8
cnot bellA0 8
T 8
cnot bellA2 8
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 8
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 7
cnot bellA0 7
T* 7
cnot bellA2 7
T* 7
cnot bellA0 7
T 7
cnot bellA2 7
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 7
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
cnot bellA0 6
T* 6
T 7
cnot 6 7
T 7
cnot bellA0 7
T* 7
cnot 6 7
T* 7
cnot bellA0 6
cnot bellA0 7
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 6
T 5
T 6
cnot 5 6
T* 6
T x23
cnot 5 x23
T* x23
cnot 6 x23
T* x23
cnot 5 x23
T x23
cnot 6 x23
cnot 5 6
H 5
T 4
T 5
cnot 4 5
T* 5
T x24
cnot 4 x24
T* x24
cnot 5 x24
T* x24
cnot 4 x24
T x24
cnot 5 x24
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x25
cnot 3 x25
T* x25
cnot 4 x25
T* x25
cnot 3 x25
T x25
cnot 4 x25
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 0
H x30
T 0
T x29
cnot 0 x29
T* x29
T x30
cnot 0 x30
T* x30
cnot x29 x30
T* x30
cnot 0 x30
T x30
cnot x29 x30
cnot 0 x29
H x30
H 0
T 0
T 1
cnot 0 1
T* 1
T x28
cnot 0 x28
T* x28
cnot 1 x28
T* x28
cnot 0 x28
T x28
cnot 1 x28
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x27
cnot 1 x27
T* x27
cnot 2 x27
T* x27
cnot 1 x27
T x27
cnot 2 x27
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x26
cnot 2 x26
T* x26
cnot 3 x26
T* x26
cnot 2 x26
T x26
cnot 3 x26
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x25
cnot 3 x25
T* x25
cnot 4 x25
T* x25
cnot 3 x25
T x25
cnot 4 x25
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x24
cnot 4 x24
T* x24
cnot 5 x24
T* x24
cnot 4 x24
T x24
cnot 5 x24
cnot 4 5
H 5
T 5
T 6
cnot 5 6
T* 6
T x23
cnot 5 x23
T* x23
cnot 6 x23
T* x23
cnot 5 x23
T x23
cnot 6 x23
cnot 5 6
H 6
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 6
cnot bellA0 6
T* 6
T 7
cnot 6 7
T 7
cnot bellA0 7
T* 7
cnot 6 7
T* 7
cnot bellA0 6
cnot bellA0 7
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 7
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 7
cnot bellA0 7
T* 7
cnot bellA2 7
T* 7
cnot bellA0 7
T 7
cnot bellA2 7
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 7
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 6
cnot bellA0 6
T* 6
cnot bellA2 6
T* 6
cnot bellA0 6
T 6
cnot bellA2 6
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 6
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
cnot bellA0 5
T* 5
T 6
cnot 5 6
T 6
cnot bellA0 6
T* 6
cnot 5 6
T* 6
cnot bellA0 5
cnot bellA0 6
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 5
T 4
T 5
cnot 4 5
T* 5
T x23
cnot 4 x23
T* x23
cnot 5 x23
T* x23
cnot 4 x23
T x23
cnot 5 x23
cnot 4 5
H 4
T 3
T 4
cnot 3 4
T* 4
T x24
cnot 3 x24
T* x24
cnot 4 x24
T* x24
cnot 3 x24
T x24
cnot 4 x24
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x25
cnot 2 x25
T* x25
cnot 3 x25
T* x25
cnot 2 x25
T x25
cnot 3 x25
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 0
H x29
T 0
T x28
cnot 0 x28
T* x28
T x29
cnot 0 x29
T* x29
cnot x28 x29
T* x29
cnot 0 x29
T x29
cnot x28 x29
cnot 0 x28
H x29
H 0
T 0
T 1
cnot 0 1
T* 1
T x27
cnot 0 x27
T* x27
cnot 1 x27
T* x27
cnot 0 x27
T x27
cnot 1 x27
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x26
cnot 1 x26
T* x26
cnot 2 x26
T* x26
cnot 1 x26
T x26
cnot 2 x26
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x25
cnot 2 x25
T* x25
cnot 3 x25
T* x25
cnot 2 x25
T x25
cnot 3 x25
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x24
cnot 3 x24
T* x24
cnot 4 x24
T* x24
cnot 3 x24
T x24
cnot 4 x24
cnot 3 4
H 4
T 4
T 5
cnot 4 5
T* 5
T x23
cnot 4 x23
T* x23
cnot 5 x23
T* x23
cnot 4 x23
T x23
cnot 5 x23
cnot 4 5
H 5
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 5
cnot bellA0 5
T* 5
T 6
cnot 5 6
T 6
cnot bellA0 6
T* 6
cnot 5 6
T* 6
cnot bellA0 5
cnot bellA0 6
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 6
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 6
cnot bellA0 6
T* 6
cnot bellA2 6
T* 6
cnot bellA0 6
T 6
cnot bellA2 6
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 6
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 5
cnot bellA0 5
T* 5
cnot bellA2 5
T* 5
cnot bellA0 5
T 5
cnot bellA2 5
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 5
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
cnot bellA0 4
T* 4
T 5
cnot 4 5
T 5
cnot bellA0 5
T* 5
cnot 4 5
T* 5
cnot bellA0 4
cnot bellA0 5
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 4
T 3
T 4
cnot 3 4
T* 4
T x23
cnot 3 x23
T* x23
cnot 4 x23
T* x23
cnot 3 x23
T x23
cnot 4 x23
cnot 3 4
H 3
T 2
T 3
cnot 2 3
T* 3
T x24
cnot 2 x24
T* x24
cnot 3 x24
T* x24
cnot 2 x24
T x24
cnot 3 x24
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x25
cnot 1 x25
T* x25
cnot 2 x25
T* x25
cnot 1 x25
T x25
cnot 2 x25
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 0
H x28
T 0
T x27
cnot 0 x27
T* x27
T x28
cnot 0 x28
T* x28
cnot x27 x28
T* x28
cnot 0 x28
T x28
cnot x27 x28
cnot 0 x27
H x28
H 0
T 0
T 1
cnot 0 1
T* 1
T x26
cnot 0 x26
T* x26
cnot 1 x26
T* x26
cnot 0 x26
T x26
cnot 1 x26
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x25
cnot 1 x25
T* x25
cnot 2 x25
T* x25
cnot 1 x25
T x25
cnot 2 x25
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x24
cnot 2 x24
T* x24
cnot 3 x24
T* x24
cnot 2 x24
T x24
cnot 3 x24
cnot 2 3
H 3
T 3
T 4
cnot 3 4
T* 4
T x23
cnot 3 x23
T* x23
cnot 4 x23
T* x23
cnot 3 x23
T x23
cnot 4 x23
cnot 3 4
H 4
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 4
cnot bellA0 4
T* 4
T 5
cnot 4 5
T 5
cnot bellA0 5
T* 5
cnot 4 5
T* 5
cnot bellA0 4
cnot bellA0 5
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 5
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 5
cnot bellA0 5
T* 5
cnot bellA2 5
T* 5
cnot bellA0 5
T 5
cnot bellA2 5
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 5
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 4
cnot bellA0 4
T* 4
cnot bellA2 4
T* 4
cnot bellA0 4
T 4
cnot bellA2 4
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 4
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
cnot bellA0 3
T* 3
T 4
cnot 3 4
T 4
cnot bellA0 4
T* 4
cnot 3 4
T* 4
cnot bellA0 3
cnot bellA0 4
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 3
T 2
T 3
cnot 2 3
T* 3
T x23
cnot 2 x23
T* x23
cnot 3 x23
T* x23
cnot 2 x23
T x23
cnot 3 x23
cnot 2 3
H 2
T 1
T 2
cnot 1 2
T* 2
T x24
cnot 1 x24
T* x24
cnot 2 x24
T* x24
cnot 1 x24
T x24
cnot 2 x24
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x25
cnot 0 x25
T* x25
cnot 1 x25
T* x25
cnot 0 x25
T x25
cnot 1 x25
cnot 0 1
H 0
H x27
T 0
T x26
cnot 0 x26
T* x26
T x27
cnot 0 x27
T* x27
cnot x26 x27
T* x27
cnot 0 x27
T x27
cnot x26 x27
cnot 0 x26
H x27
H 0
T 0
T 1
cnot 0 1
T* 1
T x25
cnot 0 x25
T* x25
cnot 1 x25
T* x25
cnot 0 x25
T x25
cnot 1 x25
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x24
cnot 1 x24
T* x24
cnot 2 x24
T* x24
cnot 1 x24
T x24
cnot 2 x24
cnot 1 2
H 2
T 2
T 3
cnot 2 3
T* 3
T x23
cnot 2 x23
T* x23
cnot 3 x23
T* x23
cnot 2 x23
T x23
cnot 3 x23
cnot 2 3
H 3
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 3
cnot bellA0 3
T* 3
T 4
cnot 3 4
T 4
cnot bellA0 4
T* 4
cnot 3 4
T* 4
cnot bellA0 3
cnot bellA0 4
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 4
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 4
cnot bellA0 4
T* 4
cnot bellA2 4
T* 4
cnot bellA0 4
T 4
cnot bellA2 4
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 4
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 3
cnot bellA0 3
T* 3
cnot bellA2 3
T* 3
cnot bellA0 3
T 3
cnot bellA2 3
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 3
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
cnot bellA0 2
T* 2
T 3
cnot 2 3
T 3
cnot bellA0 3
T* 3
cnot 2 3
T* 3
cnot bellA0 2
cnot bellA0 3
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 2
T 1
T 2
cnot 1 2
T* 2
T x23
cnot 1 x23
T* x23
cnot 2 x23
T* x23
cnot 1 x23
T x23
cnot 2 x23
cnot 1 2
H 1
T 0
T 1
cnot 0 1
T* 1
T x24
cnot 0 x24
T* x24
cnot 1 x24
T* x24
cnot 0 x24
T x24
cnot 1 x24
cnot 0 1
H 0
H x26
T 0
T x25
cnot 0 x25
T* x25
T x26
cnot 0 x26
T* x26
cnot x25 x26
T* x26
cnot 0 x26
T x26
cnot x25 x26
cnot 0 x25
H x26
H 0
T 0
T 1
cnot 0 1
T* 1
T x24
cnot 0 x24
T* x24
cnot 1 x24
T* x24
cnot 0 x24
T x24
cnot 1 x24
cnot 0 1
H 1
T 1
T 2
cnot 1 2
T* 2
T x23
cnot 1 x23
T* x23
cnot 2 x23
T* x23
cnot 1 x23
T x23
cnot 2 x23
cnot 1 2
H 2
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 2
cnot bellA0 2
T* 2
T 3
cnot 2 3
T 3
cnot bellA0 3
T* 3
cnot 2 3
T* 3
cnot bellA0 2
cnot bellA0 3
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 3
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 3
cnot bellA0 3
T* 3
cnot bellA2 3
T* 3
cnot bellA0 3
T 3
cnot bellA2 3
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 3
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 2
cnot bellA0 2
T* 2
cnot bellA2 2
T* 2
cnot bellA0 2
T 2
cnot bellA2 2
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 2
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 1
T 0
T 1
cnot 0 1
T* 1
T x23
cnot 0 x23
T* x23
cnot 1 x23
T* x23
cnot 0 x23
T x23
cnot 1 x23
cnot 0 1
H 0
H x25
T 0
T x24
cnot 0 x24
T* x24
T x25
cnot 0 x25
T* x25
cnot x24 x25
T* x25
cnot 0 x25
T x25
cnot x24 x25
cnot 0 x24
H x25
H 0
T 0
T 1
cnot 0 1
T* 1
T x23
cnot 0 x23
T* x23
cnot 1 x23
T* x23
cnot 0 x23
T x23
cnot 1 x23
cnot 0 1
H 1
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 1
cnot bellA0 1
T* 1
T 2
cnot 1 2
T 2
cnot bellA0 2
T* 2
cnot 1 2
T* 2
cnot bellA0 1
cnot bellA0 2
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 2
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 2
cnot bellA0 2
T* 2
cnot bellA2 2
T* 2
cnot bellA0 2
T 2
cnot bellA2 2
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 2
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 1
cnot bellA0 1
T* 1
cnot bellA2 1
T* 1
cnot bellA0 1
T 1
cnot bellA2 1
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 1
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 0
H x24
T 0
T x23
cnot 0 x23
T* x23
T x24
cnot 0 x24
T* x24
cnot x23 x24
T* x24
cnot 0 x24
T x24
cnot x23 x24
cnot 0 x23
H x24
H 0
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T 1
cnot 0 1
T 1
cnot bellA0 1
T* 1
cnot 0 1
T* 1
cnot bellA0 0
cnot bellA0 1
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H 1
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 1
cnot bellA0 1
T* 1
cnot bellA2 1
T* 1
cnot bellA0 1
T 1
cnot bellA2 1
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 1
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T* 0
cnot bellA0 0
T 0
cnot bellA2 0
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 0
H x23
H bellA0
cnot bellA0 bellA1
cnot x22 bellA1
measure bellA1
cnot bellA1 bellA0
T 0
cnot bellA0 0
T* 0
T x23
cnot 0 x23
T x23
cnot bellA0 x23
T* x23
cnot 0 x23
T* x23
cnot bellA0 0
cnot bellA0 x23
H bellA0
measure bellA0
cz bellA0 x22
T x22
reset bellA0
reset bellA1
H x23
H 0
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
measure bellA1
cnot bellA1 bellA0
H bellA2
cnot bellA2 bellA3
cnot x21 bellA3
measure bellA3
cnot bellA3 bellA2
cnot bellA0 bellA2
T* bellA2
T 0
cnot bellA0 0
T* 0
cnot bellA2 0
T* 0
cnot bellA0 0
T 0
cnot bellA2 0
cnot bellA0 bellA2
H bellA0
measure bellA0
cz bellA0 x1
H bellA2
measure bellA2
cz bellA2 x21
T x1
T x21
reset bellA0
reset bellA1
reset bellA2
reset bellA3
H 0
H x22
H bellA0
cnot bellA0 bellA1
cnot x1 bellA1
cnot x21 bellA1
measure bellA1
cnot bellA1 bellA0
T* bellA0
H bellA0
measure bellA0
cz bellA0 x1
cz bellA0 x21
T x1
T x21
T x22
cnot x1 x22
T* x22
cnot x21 x22
T x22
cnot x1 x22
T* x22
cnot x21 x22
reset bellA0
reset bellA1
H x22
cnot x1 x21
END
