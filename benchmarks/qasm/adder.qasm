OPENQASM 2.0;
include "qelib1.inc";

gate adder<n> a,b,c,d {
  CX a[0],b[0];
}
