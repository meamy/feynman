// v = ["x", "y", "z"]
// testcase5 = WSeq 1 [WGate 2 $ T "y",
//                     WWhile 4 $ WGate 5 $ H "x",
//                     WGate 6 $ Tinv "y"]

include "stdgates.inc";

qubit a;
qubit b;

t b;
while (true) {
    h a;
}
tdg y;
