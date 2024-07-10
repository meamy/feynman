// vars = ["x", "y"]
// testcase6 = WSeq 1 [WGate 2 $ T "y",
//                     WWhile 4 $ WSeq 5 [WGate 6 $ T "x",
//                                        WWhile 7 $ (WGate 8 $ X "y")],
//                     WGate 9 $ Tinv "y"]

include "stdgates.inc";

qubit x;
qubit y;

t y;
while (true) {
    t x;
    while (true) {
        x y;
    }
}
tdg y;
