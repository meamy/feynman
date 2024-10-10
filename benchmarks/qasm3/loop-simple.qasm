// vars = ["x", "y"]
// testcase1 = WSeq 1 [WGate 2 $ T "x",
//                     WWhile 4 $ WGate 5 $ CNOT "x" "y",
//                     WGate 6 $ Tinv "x"]

include "stdgates.inc";

qubit a;
qubit b;

t a;
while (true) {
    cx a, b;
}
tdg a;
