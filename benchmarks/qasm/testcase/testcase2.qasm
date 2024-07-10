// vars = ["x", "y"]
// testcase2 = WSeq 1 [WGate 2 $ T "x",
//                     WIf 4 (WGate 5 $ CNOT "x" "y") (WSkip 6),
//                     WGate 7 $ Tinv "x"]

include "stdgates.inc";

qubit x;
qubit y;

t x;
if (true) {
    cx x, y;
}
tdg x;
