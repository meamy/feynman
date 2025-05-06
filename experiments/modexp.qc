.v a b c d e
.i

BEGIN CS a b
 Rz(pi/2^2) a;
 Rz(pi/2^2) b;
 cnot a b;
 Rz(-pi/2^2) b;
 cnot a b;
END

BEGIN CT a b
 Rz(pi/2^3) a;
 Rz(pi/2^3) b;
 cnot a b;
 Rz(-pi/2^3) b;
 cnot a b;
END

BEGIN CrtT a b
 Rz(pi/2^4) a;
 Rz(pi/2^4) b;
 cnot a b;
 Rz(-pi/2^4) b;
 cnot a b;
END

BEGIN CrtrtT a b
 Rz(pi/2^5) a;
 Rz(pi/2^5) b;
 cnot a b;
 Rz(-pi/2^5) b;
 cnot a b;
END

BEGIN CSd a b
 Rz(-pi/2^2) a;
 Rz(-pi/2^2) b;
 cnot a b;
 Rz(pi/2^2) b;
 cnot a b;
END

BEGIN CTd a b
 Rz(-pi/2^3) a;
 Rz(-pi/2^3) b;
 cnot a b;
 Rz(pi/2^3) b;
 cnot a b;
END

BEGIN CrtTd a b
 Rz(-pi/2^4) a;
 Rz(-pi/2^4) b;
 cnot a b;
 Rz(pi/2^4) b;
 cnot a b;
END

BEGIN CrtrtTd a b
 Rz(-pi/2^5) a;
 Rz(-pi/2^5) b;
 cnot a b;
 Rz(pi/2^5) b;
 cnot a b;
END

BEGIN qft5(a b c d e)

H e;

CS d e;

H d;

CT c e;
CS c d;

H c;

CrtT b e;
CT b d;
CS b c

H b;

CrtrtT a e;
CrtT a d;
CT a c;
CS a b;

H a;

cnot a e;
cnot e a;
cnot a e;
cnot b d;
cnot d b;
cnot b d;

END

BEGIN qft5inv(a b c d e)

cnot a e;
cnot e a;
cnot a e;
cnot b d;
cnot d b;
cnot b d;

H a;

CrtrtTd a e;
CrtTd a d;
CTd a c;
CSd a b;

H b;

CrtTd b e;
CTd b d;
CSd b c;

H c;

CTd c e;
CSd c d;


H d;

CSd d e;

H e;

END

BEGIN qftadd3(a b c d e)

  qft5 a b c d e;

  Rz(3pi/2^4) a;
  Rz(3pi/2^3) b;
  Rz(3pi/2^2) c;
  Rz(3pi/2^1) d;
  Rz(pi) e;

  qft5inv a b c d e;

END

BEGIN

X a;

qftadd3 a b c d e;
qftadd3 a b c d e;

cnot d e;

END

