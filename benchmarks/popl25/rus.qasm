/*
 * Repeat-until-success circuit for Rz(theta),
 * cos(theta-pi)=3/5, from Nielsen and Chuang, Chapter 4.
 */
include "stdgates.inc";


qubit psi;
qubit[2] anc;
bit[2] flags = "11";

reset psi;
h psi;
t psi;

// braces are optional in this case
while(int[2](flags) != 0) {
  reset anc[0];
  reset anc[1];
  h anc[0];
  h anc[1];
  ccx anc[0], anc[1], psi;
  s psi;
  ccx anc[0], anc[1], psi;
  z psi;
  h anc[0];
  h anc[1];
  measure anc[0:1] -> flags[0:1];
}

tdg psi;
h psi;
