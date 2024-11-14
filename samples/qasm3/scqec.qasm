/*
 * Surface code quantum memory.
 *
 * Estimate the failure probability as a function
 * of parameters at the top of the file.
 */
include "stdgates.inc";

const int[32] d = 3;         // code distance
const int[32] m = 10;        // number of syndrome measurement cycles
const int[32] shots = 1000;  // number of samples
const int[32] n = d**2;      // number of code qubits

uint[32] failures;  // number of observed failures

extern zfirst(creg[n - 1], int[32], int[32]);
extern send(creg[n -1 ], int[32], int[32], int[32]);
extern zlast(creg[n], int[32], int[32]) -> bit;

qubit[n] data;  // code qubits
qubit[n-1] ancilla;  // syndrome qubits
/*
 * Ancilla are addressed in a (d-1) by (d-1) square array
 * followed by 4 length (d-1)/2 arrays for the top,
 * bottom, left, and right boundaries.
 */

bit[n-1] layer;  // syndrome outcomes in a cycle
bit[n] data_outcomes;  // data outcomes at the end
bit outcome;  // logical outcome

/* Declare a sub-circuit for Hadamard gates on ancillas
 */
def hadamard_layer(qubit[n-1] ancilla) {
  // Hadamards in the bulk
  for uint[32] row in [0: d-2] {
    for uint[32] col in [0: d-2] {
      bit[32] sum = bit[32](row + col);
      if(sum[0] == 1)
        h ancilla[row * (d - 1) + col];
    }
  }
  // Hadamards on the left and right boundaries
  for uint[32] i in [0: d - 2] {
    h ancilla[(d - 1)**2 + (d - 1) + i];
  }
}

/* Declare a sub-circuit for a syndrome cycle.
 */
def cycle(qubit[n] data, qubit[n-1] ancilla) -> bit[n-1] {
  reset ancilla;
  hadamard_layer ancilla;

  // First round of CNOTs in the bulk
  for uint[32] row in [0: d - 2] {
    for uint[32] col in [0:d - 2] {
      bit[32] sum = bit[32](row + col);
      if(sum[0] == 0)
        cx data[row * d + col], ancilla[row * (d - 1) + col];
      if(sum[0] == 1) {
        cx ancilla[row * (d - 1) + col], data[row * d + col];
      }
    }
  }
  // First round of CNOTs on the bottom boundary
  for uint[32] i in [0: (d - 3) / 2] {
    cx data[d * (d - 1) + 2 * i], ancilla[(d - 1) ** 2 + ( d- 1) / 2 + i];
  }
  // First round of CNOTs on the right boundary
  for uint[32] i in [0: (d - 3) / 2] {
    cx ancilla[(d - 1) ** 2 + 3 * (d - 1) / 2 + i], data[2 * d - 1 + 2 * d * i];
  }
  // Remaining rounds of CNOTs, go here ...

  hadamard_layer ancilla;
  return measure ancilla;
}

// Loop over shots
for uint[32] shot in [1: shots] {

  // Initialize
  reset data;
  layer = cycle(data, ancilla);
  zfirst(layer, shot, d);

  // m cycles of syndrome measurement
  for int[32] i in [1: m] {
    layer = cycle(data, ancilla);
    send(layer, shot, i, d);
  }

  // Measure
  data_outcomes = measure data;

  outcome = zlast(data_outcomes, shot, d);
  failures += int[1](outcome);
}

/* The ratio of "failures" to "shots" is our result.
 * The data can be logged by the external functions too.
 */
