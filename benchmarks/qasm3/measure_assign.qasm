OPENQASM 3.0;
include "stdgates.inc";

qubit[2] q;
bit[2] c;

// Prepare Bell pair
h q[0];
cx q[0], q[1];

// Measure assignment (assignment syntax)
c[0] = measure q[0];

// Measure assignment (arrow syntax)
measure q[1] -> c[1];

