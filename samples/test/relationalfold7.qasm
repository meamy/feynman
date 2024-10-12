// vars = ["x", "y"]
// testcase7 = WSeq 1 [WGate 2 $ T "y",
//                     WReset 4 "x",
//                     WWhile 6 $ WSeq 7 [WGate 8 $ T "y",
//                                        WGate 7 $ T "x"],
//                     WGate 9 $ Tinv "y"]

include "stdgates.inc";

qubit a;
qubit b;

t b;
reset a;
while (true) {
    t b;
    t a;
}
tdg b;
