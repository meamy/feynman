.v q1 q2 a1 a2 a3 x1 x2 x3 x4 t
.i x1 x2 x3 x4

BEGIN pre p1 p2 x1 x2 x3 x4 t
  tof x1 t
  tof t x2 p1
  tof p1 t
  tof t x3 p2
  tof p2 t
  tof t x4 p1
  tof t x4 p2
  tof p1 p2 t
END

BEGIN fred a b c
  tof b c
  tof a c b
  tof b c
END

BEGIN
  X t
  pre q1 q2 x1 x2 x3 x4 t

  fred q1 x1 x2
  fred q1 x2 x3
  fred q1 x3 x4

  fred q2 x1 x3
  fred q2 x2 x4
END
