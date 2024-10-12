/* CPMG XY4 decoupling w/ boxing
 * This example demonstrates the use of referential delays
 * and time alignment.
*/
include "stdgates.inc";

stretch a;
duration start_stretch = -0.5 * durationof({x $0;}) + a;
duration middle_stretch = -0.5 * durationof({x $0;}) - 5 * durationof({y $0;}) + a;
duration end_stretch = -0.5 * durationof({y $0;}) + a;

box {
  delay[start_stretch] $0;
  x $0;
  delay[middle_stretch] $0;
  y $0;
  delay[middle_stretch] $0;
  x $0;
  delay[middle_stretch] $0;
  y $0;
  delay[end_stretch] $0;

  cx $2, $3;
  cx $1, $2;
  u $3;
}
