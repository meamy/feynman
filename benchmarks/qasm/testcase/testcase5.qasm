// vars = ["x", "y"]
// testcase5 = WSeq 1 [WGate 2 $ T "y",
//                     WWhile 4 $ WGate 5 $ H "x",
//                     WGate 6 $ Tinv "y"]

include "stdgates.inc";

qubit x;
qubit y;

t y;
while (true) {
    h x;
}
tdg y;
