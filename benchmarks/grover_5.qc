#Use the input state "|0>^5|1>".  After each iteration you should see the state corresponding 
#the toffoli oracle increase in amplitude maximizing at the 4th iteration.

.v a b c d e Workspace 0 1 2
.i a b c d e
.o a b c d e
.c


BEGIN
H a
H b
H c
H d
H e

H a
H b
H c
H d
H e

X e
X a
X b
X c
X d
H 0
Z a b 0
H 0
H 1
Z c 0 1
H 1
H e
Z d 1 e
H e
H 1
Z c 0 1
H 1
H 0
Z a b 0
H 0
X e
X a
X b
X c
X d

H a
H b
H c
H d
H e

H a
H b
H c
H d
H e

X e
X a
X b
X c
X d
H 0
Z a b 0
H 0
H 1
Z c 0 1
H 1
H e
Z d 1 e
H e
H 1
Z c 0 1
H 1
H 0
Z a b 0
H 0
X e
X a
X b
X c
X d

H a
H b
H c
H d
H e

H a
H b
H c
H d
H e

X e
X a
X b
X c
X d
H 0
Z a b 0
H 0
H 1
Z c 0 1
H 1
H e
Z d 1 e
H e
H 1
Z c 0 1
H 1
H 0
Z a b 0
H 0
X e
X a
X b
X c
X d

H a
H b
H c
H d
H e

H a
H b
H c
H d
H e

X e
X a
X b
X c
X d
H 0
Z a b 0
H 0
H 1
Z c 0 1
H 1
H e
Z d 1 e
H e
H 1
Z c 0 1
H 1
H 0
Z a b 0
H 0
X e
X a
X b
X c
X d

H a
H b
H c
H d
H e
END
