Build profile: -w ghc-8.8.4 -O1
In order, the following will be built (use -v for more details):
 - Feynman-0.1.0.0 (lib) (file src/Feynman/Synthesis/HypergraphPartition/PartitionConfigs.hs changed)
 - Feynman-0.1.0.0 (exe:feynopt) (dependency rebuilt)
Preprocessing library for Feynman-0.1.0.0...
Building library for Feynman-0.1.0.0...
[36 of 38] Compiling Feynman.Synthesis.HypergraphPartition.PartitionConfigs ( src/Feynman/Synthesis/HypergraphPartition/PartitionConfigs.hs, /Users/duykhangnguyentruong/Development/feynman/dist-newstyle/build/x86_64-osx/ghc-8.8.4/Feynman-0.1.0.0/build/Feynman/Synthesis/HypergraphPartition/PartitionConfigs.o )
[37 of 38] Compiling Feynman.Synthesis.HypergraphPartition.HGraphBuilder ( src/Feynman/Synthesis/HypergraphPartition/HGraphBuilder.hs, /Users/duykhangnguyentruong/Development/feynman/dist-newstyle/build/x86_64-osx/ghc-8.8.4/Feynman-0.1.0.0/build/Feynman/Synthesis/HypergraphPartition/HGraphBuilder.o ) [Feynman.Synthesis.HypergraphPartition.PartitionConfigs changed]
Preprocessing executable 'feynopt' for Feynman-0.1.0.0...
Building executable 'feynopt' for Feynman-0.1.0.0...
Linking /Users/duykhangnguyentruong/Development/feynman/dist-newstyle/build/x86_64-osx/ghc-8.8.4/Feynman-0.1.0.0/x/feynopt/build/feynopt/feynopt ...
# Hyperedge cut (ebits): 4

# Actual ebits used (Synthesis): 4
# Distribution Verification: PASS
# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc_customized/test_target.qc):
#   Qubits: 6
#   cnot: 5
#   Depth: 5
#   T depth: 0
# Result (7.711ms):
#   Qubits: 14
#   H: 8
#   cnot: 19
#   cz: 5
#   measure: 8
#   reset: 9
#   Depth: 23
#   T depth: 0


# Result Circuit
.v a b c d e f bell0 bell1 bell2 bell3 bell4 bell5 bell6 bell7
.i a b c d e f
.o a b c d e f
BEGIN 
H bell0
cnot bell0 bell1
cnot e bell1
measure bell1
cnot bell1 bell0
cnot bell0 f
H bell0
measure bell0
cz bell0 e
H bell2
cnot bell2 bell3
cnot c bell3
measure bell3
cnot bell3 bell2
cnot bell2 f
H bell2
measure bell2
cz bell2 c
cnot b f
H bell4
cnot bell4 bell5
cnot f bell5
measure bell5
cnot bell5 bell4
cnot d bell4
cnot a bell4
H bell6
cnot bell6 bell7
cnot bell4 bell7
measure bell7
cnot bell7 bell6
reset bell7
cnot f bell6
cnot bell6 f
H bell6
measure bell6
cz bell6 a
cz bell6 d
H bell4
measure bell4
cz bell4 f
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
reset bell6
reset bell7
END
