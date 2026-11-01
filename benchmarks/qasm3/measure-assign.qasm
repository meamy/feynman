// vars = ["x"]
// testcase_measure_assign = WSeq 1 [WGate 2 $ T "x",
//                                  WMeasure 3 "x",
//                                  WGate 4 $ T "x"]

include "stdgates.inc";

qubit a;
bit c;

t a;
c = measure a;
t a;