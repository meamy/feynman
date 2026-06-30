# Result Circuit
.v a b c
.i a b c
.o a b c
BEGIN 
cnot b a
cnot a b
X b
H b
cnot b a
Y b
cnot c b
H b
cnot b c
Z c
cnot c b
X a
END
