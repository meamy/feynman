/* CPMG XY4 decoupling
 * This example demonstrates the use of stretch to
 * specify design intent on gate alignment, without
 * being tied to physical qubits and gates.
*/
include "stdgates.inc";

stretch g;

qubit[3] q;
barrier q;
cx q[0], q[1];
delay[g] q[2];
U(pi/4, 0, pi/2) q[2];
delay[2*g] q[2];
barrier q;
