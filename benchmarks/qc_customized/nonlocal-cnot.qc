.v x y
.i x y
.o x y
BEGIN
H b0
cnot b0 b1

cnot x b1
measure b1
cnot b1 b0

cnot b0 y

H b0
measure b0
cz b0 x

reset b0
reset b1
END