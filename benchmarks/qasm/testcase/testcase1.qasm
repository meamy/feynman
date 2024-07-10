// vars = ["x", "y"]
// testcase1 = WSeq 1 [WGate 2 $ T "x",
//                     WWhile 4 $ WGate 5 $ CNOT "x" "y",
//                     WGate 6 $ Tinv "x"]
// test1 = genSubstList vars vars testcase1
// test2 = execState (applyStmt testcase1) (initialState vars vars)

include "stdgates.inc";

qubit x;
qubit y;

t x;
while (true) {
    cx x, y;
}
tdg x;
