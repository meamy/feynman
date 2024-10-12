// v = ["x", "y", "z"]
// testcase9 = WSeq 1 [WGate 2 $ T "y",
//                     WWhile 4 $ WSeq 5 [WGate 6 $ Swap "x" "y",
//                                        WGate 8 $ Swap "y" "z"],
//                     WGate 10 $ Tinv "y"]
// 

include "stdgates.inc";

qubit a;
qubit b;
qubit c;

t b;
while (true) {
    swap a, b;
    swap b, c;
}
tdg b;
