.v a b c d b0 b1 b2 b3
.i a b c d

BEGIN
# First Bell state preparation
H b0
cnot b0 b1

# Entangler must be set up right before the first index of the the non-local gate in the hyperedge
# Cat entangler 1
cnot b b1
measure b1
cnot b1 b0

cnot b0 c
T c
T a
cnot b0 a
T a
cnot d a
T a
cnot b0 a
T a

# Second Bell state preparation
H b2
cnot b2 b3

# Cat entangler 2
cnot c b3
measure b3
cnot b3 b2

cnot b2 a

# I make a mistake before this. The original procedure is correct
# The disentangler must be set up right after the last index of the non-local cnot gate

# Cat disentangler 2
H b2
measure b2
cz b2 c

cnot d a
T a
cnot b0 a
cnot b0 c

# Cat disentangler 1
H b0
measure b0
H b
cnot b0 b
H b

# Reset all bell pairs
reset b0
reset b1
reset b2
reset b3
END