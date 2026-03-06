.v a b c d bell0 bell1 bell2 bell3 bell4 bell5
.i a b c d
.o a b c d
BEGIN
H b

# Bell state 1
H bell0
cnot bell0 bell1

# entangler 1
cnot c bell1
measure bell1
cnot bell1 bell0

cz bell0 b
H b
H d

cz c d

# Bell state 2
H bell2
cnot bell2 bell3

# entangler 2
cnot a bell3
measure bell3
cnot bell3 bell2

cz bell2 d

# distangler 2
H bell2
measure bell2
cz bell2 a

#disentangler 1
H bell0
measure bell0
cz bell0 c

H d
H c
T b
H a

# Bell state 3
H bell4
cnot bell4 bell5

#entangler 3
cnot c bell5
measure bell5
cnot bell5 bell4

cz bell4 a
H a
H b
cz bell4 b

# distangler 3
H bell4
measure bell4
cz bell4 c

cz a b
H b

reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5

END