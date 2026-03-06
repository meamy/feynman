.v a b c d
.i a b c d

BEGIN

cnot b c
T c
T a
cnot b a
T a
cnot d a
T a
cnot b a
T a
cnot c a
cnot d a
T a
cnot b a
cnot b c

END