.v a b c d
.i a b c d
BEGIN
cnot a b
cnot b c
T c 
cnot c d
T d
cnot c d
cnot b c
cnot a b
END