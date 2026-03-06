.v a b c b0 b1
.i a b c

BEGIN
T c
# Bell state
H b0
cnot b0 b1

# Entangler
cnot c b1
measure b1
cnot b1 b0

cnot b0 b
cnot b a
H a
cnot b0 a
Y b
cnot b0 b

# disentangler
H b0
measure b0
cz b0 c

cnot a b
X b

#reset
reset b0
reset b1

END