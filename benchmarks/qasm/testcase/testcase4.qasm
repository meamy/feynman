// vars = ["x", "y"]
// testcase4 = WSeq 1 [WGate 2 $ CNOT "x" "y",
//                     WGate 4 $ T "y",
//                     WGate 6 $ CNOT "x" "y",
//                     WWhile 8 $ WGate 9 $ Swap "x" "y",
//                     WGate 11 $ CNOT "x" "y",
//                     WGate 13 $ Tinv "y",
//                     WGate 14 $ CNOT "x" "y"]

include "stdgates.inc";

qubit x;
qubit y;

cx x, y;
t y;
cx x, y;
while (true) {
    swap x, y;
}
cx x, y;
tdg y;
cx x, y;
