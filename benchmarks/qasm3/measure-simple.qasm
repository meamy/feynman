// vars = ["x"]
// testcase_measure = WSeq 1 [WGate 2 $ T "x",
//                           WMeasure 3 "x",
//                           WGate 4 $ T "x"]

include "stdgates.inc";

qubit a;

t a;
measure a;
t a;