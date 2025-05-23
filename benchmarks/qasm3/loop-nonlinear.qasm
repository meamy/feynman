include "stdgates.inc";

qubit a;
qubit b;
qubit c;

gate ccz p, q, r {
    t p;
    t q;
    t r;
    cx p, q;
    cx q, r;
    cx r, p;
    tdg p;
    tdg q;
    t r;
    cx q, p;
    tdg p;
    cx q, r;
    cx r, p;
    cx p, q;
}

gate ccx p, q, r {
    h r;
    ccz p, q, r;
    h r;
}

gate circ p, q, r {
    x p;
    ccx p, q, r;
    t r;
    ccx p, q, r;
    x p;
}

reset c;
x a;
ccx a, b, c;
t c;
ccx a, b, c;
x a;
while (true) {
    cx a, b;
}
x a;
ccx a, b, c;
tdg c;
ccx a, b, c;
x a;
