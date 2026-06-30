# Result Circuit
.v a b c
.i a b c
.o a b c
BEGIN 
cnot c b
cnot a b
X b
Y b
cnot c a
H a
T c
cnot c b
cnot b a
END