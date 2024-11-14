// Repetition code gate teleportation
include "stdgates.inc";

// declarations
const int[32] n = 3;
extern vote(bit[n]) -> bit;

def logical_meas(qubit[3] d) -> bit {
    bit[3] c;
    bit r;
    measure d -> c;
    r = vote(c);
    return r;
}

qubit[3] q;
qubit[3] a;
bit r;

// prep magic state
rz(pi/4) a;

// entangle two logical registers
cx q, a;

// measure out the ancilla
r = logical_meas(a);

// if we get a logical |1> then we need to apply a logical Z correction
if (r == 1) z q;
