// vars = ["x", "y"]
// testcase4 = WSeq 1 [WGate 2 $ CNOT "x" "y",
//                     WGate 4 $ T "y",
//                     WGate 6 $ CNOT "x" "y",
//                     WWhile 8 $ WGate 9 $ Swap "x" "y",
//                     WGate 11 $ CNOT "x" "y",
//                     WGate 13 $ Tinv "y",
//                     WGate 14 $ CNOT "x" "y"]

include "stdgates.inc"

qubit a;
qubit b;

cx a, b;
t b;
cx a, b;
while (true) {
    swap a, b;
}
cx a, b;
tdg b;
cx a, b;
