/* Measuring the relaxation time of a qubit
 * This example demonstrates the repeated use of fixed delays.
*/
include "stdgates.inc";

duration stride = 1us;            // time resolution of points taken
const int[32] points = 50;              // number of points taken
const int[32] shots = 1000;             // how many shots per point

int[32] counts0;
int[32] counts1 = 0;   // surviving |1> populations of qubits

extern tabulate(int[32], int[32], int[32]);

bit c0;
bit c1;

defcalgrammar "openpulse";

// define a gate calibration for an X gate on any qubit
defcal x q {
   play drive(q), gaussian(100, 30, 5);
}

for int[32] p in [0 : points-1] {
    for uint i in [1 : shots] {
        // start of a basic block
        reset $0;
        reset $1;
        // excite qubits
        x $0;
        x $1;
        // wait for a fixed time indicated by loop counter
        delay[p * stride] $0;
        // wait for a fixed time indicated by loop counters
        delay[p * durationof({x $1;})];
        // read out qubit states
        c0 = measure $0;
        c1 = measure $1;
        // increment counts memories, if a 1 is seen
        counts0 += int[1](c0);
        counts1 += int[1](c1);
    }
    // log survival probability curve
    tabulate(counts0, shots, p);
    tabulate(counts1, shots, p);
}
