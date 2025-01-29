# maj.qc - computes maj(a, b, c) into c, with a, b dirty after
.v a b c
.i a b c
BEGIN
cnot c a
cnot c b
tof a b c
END
