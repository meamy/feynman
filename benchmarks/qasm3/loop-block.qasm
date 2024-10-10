// v = ["x", "y", "z"]
// testcase8 = WSeq 1 [WGate 2 $ T "x",
//                     WGate 4 $ H "x",
//                     WWhile 6 $ WGate 7 $ T "x",
//                     WGate 9 $ H "x",
//                     WGate 10 $ Tinv "x"]

include "stdgates.inc";

qubit a;
qubit b;

t a;
h a;
while (true) {
    t a;
}
h a;
tdg a;
