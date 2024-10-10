// v = ["x", "y", "z"]
// testcase10 = WSeq 1 $ [WReset 2 "z"] ++
//                       toStmt 4 circ ++
//                       [WWhile 101 $ WGate 102 $ CNOT "x" "y"] ++
//                       toStmt 103 circ
//   where
//     toStmt i xs = go i xs where
//       go i []     = []
//       go i (x:xs) = (WGate (i+1) x):(go (i+2) xs)
//     circ = [X "x"] ++ ccx "x" "y" "z" ++ [T "z"] ++ ccx "x" "y" "z" ++ [X "x"]
//     ccx x y z = [H z] ++ ccz x y z ++ [H z]
//     ccz x y z = [T x, T y, T z, CNOT x y, CNOT y z,
//                  CNOT z x, Tinv x, Tinv y, T z, CNOT y x,
//                  Tinv x, CNOT y z, CNOT z x, CNOT x y]

include "stdgates.inc";

qubit a;
qubit b;
qubit c;

gate ccz p, q, r {
    t p;
    t q;
    t r;
    cx p, q;
    cx q, r;
    cx r, p;
    tdg p;
    tdg q;
    t r;
    cx q, p;
    tdg p;
    cx q, r;
    cx r, p;
    cx p, q;
}

gate ccx p, q, r {
    h r;
    ccz p, q, r;
    h r;
}

def circ(qubit p, qubit q, qubit r) {
    x p;
    ccx p, q, r;
    t r;
    ccx p, q, r;
    x p;
}

reset c;
circ(a, b, c);
while (true) {
    cx a, b;
}
circ(a, b, c);
