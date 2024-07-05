// v = ["x", "y", "z"]
// testcase2 = WSeq 1 [WGate 2 $ T "x",
//                     WIf 4 (WGate 5 $ CNOT "x" "y") (WSkip 6),
//                     WGate 7 $ Tinv "x"]

include "stdgates.inc";

qubit a;
qubit b;

t a;
if (true) {
    cx a, b;
}
tdg a;
