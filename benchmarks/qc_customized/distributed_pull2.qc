.v a b c b0 b1 b2 b3
.i a b c

BEGIN
X a

# Bell state preparation
H b0
cnot b0 b1

# Cat entangler
cnot b b1
measure b1
cnot b1 b0

cnot b0 c

# Cat disentangler
H b0
measure b0
cz b0 b

Z c

# Bell state preparation
H b2
cnot b2 b3

# Cat entangler
cnot c b3
measure b3
cnot b3 b2

cnot b2 b
X a
H b
X a
cnot b2 b

# Cat disentangler
H b2
measure b2
cz b2 c

X a
Y b
X a
cnot b a
X a
H b
cnot b a
cnot a b
X a
X b

#reset
reset b0
reset b1
reset b2
reset b3

END