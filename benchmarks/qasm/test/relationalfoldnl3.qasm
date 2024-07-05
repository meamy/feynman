// v = ["x", "y", "z"]
// testcase3 = WSeq 1 [WGate 2 $ T "x",
//                     WReset 4 "x",
//                     WGate 5 $ T "x"]

include "stdgates.inc";

qubit a;

t a;
reset a;
t a;
