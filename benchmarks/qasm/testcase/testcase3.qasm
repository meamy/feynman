// vars = ["x", "y"]
// testcase3 = WSeq 1 [WGate 2 $ T "x",
//                     WReset 4 "x",
//                     WGate 5 $ T "x"]

include "stdgates.inc";

qubit x;
qubit y;

t x;
reset x;
t x;
