# parallel_root_t.qc - subcircuit to assist in computing equivalent to two
#                      parallel root(t) gates in a, b, given magic state in c

.v a b c
.i a b c

BEGIN

X c

cnot c a
cnot c b
tof a b c

T c

tof a b c
cnot c b
cnot c a

END

