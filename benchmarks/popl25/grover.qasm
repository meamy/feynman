/*
 * Grover's search on a 64 bit function
 */
include "stdgates.inc";

qubit[64] work;
qubit[64] anc;
qubit target;

for uint i in [0:63] {
  reset work[i];
  reset anc[i];
}

reset target;
x target;

// for i in [0:1073741824*pi]
while(true) {
  // Superposition
  for uint i in [0:63] {
    h work[i];
  }

  // Oracle call
  ccx work[0], work[1], anc[0];
  for uint i in [0:60] {
    ccx work[i+2], anc[i], anc[i+1];
  }
  h target;
  ccx work[63], anc[61], target;
  h target;
  for uint i in [0:60] {
    ccx work[i+2], anc[i], anc[i+1];
  }
  ccx work[0], work[1], anc[0];

  // Diffusion
  for uint i in [0:63] {
    h work[i];
    x work[i];
  }
  ccx work[0], work[1], anc[0];
  for uint i in [0:59] {
    ccx work[i+2], anc[i], anc[i+1];
  }
  h work[63];
  ccx work[62], anc[60], work[63];
  h work[63];
  for uint i in [0:59] {
    ccx work[i+2], anc[i], anc[i+1];
  }
  ccx work[0], work[1], anc[0];
  for uint i in [0:63] {
    x work[i];
    h work[i];
  }
}
