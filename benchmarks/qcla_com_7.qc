.v a0 b0 c0 a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 a4 b4 c4 d4 a5 b5 c5 d5 a6 b6 c6
.i a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6

BEGIN

X a0
X a1
X a2
X a3
X a4
X a5
X a6

H c0
H c1
H c2
H d2
H c3
H c4
H d4
H c5
H d5
H c6

Z a0 b0 c0
Z a1 b1 c1
Z a2 b2 d2
Z a3 b3 c3
Z a4 b4 d4
Z a5 b5 d5
Z a6 b6 c6

tof a1 b1
tof a2 b2
tof a3 b3
tof a4 b4
tof a5 b5
tof a6 b6

Z b2 b3 c2
Z b4 b5 c4

H c0
H c2
H d2
H c4
H d4
H c5

Z c4 b6 c5
Z c0 b1 c1
Z d4 b5 d5

H c5
H c1
H d5

Z d2 b3 c3
Z c1 c2 c3
Z d5 b6 c6

H c3

Z c3 c5 c6

H c6
H c3
H c5
H d5

Z c1 c2 c3
Z d4 b5 d5
Z c4 b6 c5

H c1

Z c0 b1 c1
Z d2 b3 c3

H c0
H c2
H d2
H c4
H d4

Z b2 b3 c2
Z b4 b5 c4

tof a1 b1
tof a2 b2
tof a3 b3
tof a4 b4
tof a5 b5
tof a6 b6

Z a0 b0 c0
Z a1 b1 c1
Z a2 b2 d2
Z a3 b3 c3
Z a4 b4 d4
Z a5 b5 d5

H c0
H c1
H c2
H d2
H c3
H c4
H d4
H c5
H d5

X a0
X a1
X a2
X a3
X a4
X a5
X a6
X c6

END
