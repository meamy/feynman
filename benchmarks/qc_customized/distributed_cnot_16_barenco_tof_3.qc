# Hyperedge cut (ebits): 5

# Actual ebits used (Synthesis): 8
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/barenco_tof_3.qc):
#   Qubits: 5
#   H: 8
#   T: 28
#   cnot: 24
#   Depth: 31
#   T depth: 13
# Result (10.102ms):
#   Qubits: 21
#   H: 22
#   T: 20
#   cnot: 44
#   cz: 8
#   measure: 16
#   reset: 16
#   Depth: 57
#   T depth: 18


# Result Circuit
.v 1 2 3 4 5 bell0 bell1 bell10 bell11 bell12 bell13 bell14 bell15 bell2 bell3 bell4 bell5 bell6 bell7 bell8 bell9
.i 1 2 3 4 5
.o 1 2 3 4 5
BEGIN 
H 5
T 5
H bell0
cnot bell0 bell1
cnot 3 bell1
measure bell1
cnot bell1 bell0
cnot bell0 5
T* 5
H bell2
cnot bell2 bell3
cnot 4 bell3
measure bell3
cnot bell3 bell2
cnot bell2 5
T 5
cnot bell0 5
H bell0
measure bell0
cz bell0 3
T* 5
cnot bell2 5
H bell2
measure bell2
cz bell2 4
T 4
H bell4
cnot bell4 bell5
cnot 3 bell5
measure bell5
cnot bell5 bell4
cnot bell4 4
T* 4
cnot bell4 4
H bell4
measure bell4
cz bell4 3
H 4
T 4
H bell6
cnot bell6 bell7
cnot 1 bell7
measure bell7
cnot bell7 bell6
cnot bell6 4
T* 4
H bell8
cnot bell8 bell9
cnot 2 bell9
measure bell9
cnot bell9 bell8
cnot bell8 4
T 4
cnot bell6 4
T* 4
cnot bell8 4
H 4
T* 5
H bell10
cnot bell10 bell11
cnot 3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 5
T 5
H bell12
cnot bell12 bell13
cnot 4 bell13
measure bell13
cnot bell13 bell12
cnot bell12 5
T* 5
cnot bell10 5
H bell10
measure bell10
cz bell10 3
T 5
cnot bell12 5
H bell12
measure bell12
cz bell12 4
H 5
T* 4
H bell14
cnot bell14 bell15
cnot 3 bell15
measure bell15
cnot bell15 bell14
cnot bell14 4
T 4
cnot bell14 4
H bell14
measure bell14
cz bell14 3
H 4
T* 4
cnot bell6 4
T 4
cnot bell8 4
T* 4
cnot bell6 4
H bell6
measure bell6
cz bell6 1
T 4
cnot bell8 4
H bell8
measure bell8
cz bell8 2
H 4
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
reset bell6
reset bell7
reset bell8
reset bell9
reset bell10
reset bell11
reset bell12
reset bell13
reset bell14
reset bell15
END
