// v = ["x", "y", "z"]
// testcase7 = WSeq 1 [WGate 2 $ T "x",
//                     WGate 4 $ H "x",
//                     WWhile 6 $ WGate 7 $ T "y",
//                     WGate 9 $ H "x",
//                     WGate 10 $ Tinv "x"]

include "stdgates.inc";

qubit a;
qubit b;

t a;
h a;
while (true) {
    t b;
}
h a;
tdg a;
