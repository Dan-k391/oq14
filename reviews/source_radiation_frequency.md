# Actual outgoing source fields at positive frequency

Author compile PASS, October 23, 2026. Six selected declarations; Lean 4.19.0,
all reports use only propext, Classical.choice and Quot.sound, with no warnings.
Source: `lean/SourceRadiationFrequency.lean`.
Source SHA256: `4c458c2eab89799841a16db7cfc0df9b5c5115491c6e2a34b9a899afa6364eb3`.
Final log: `lean/logs/SourceRadiationFrequency-final.log`, exit 0.
Log SHA256: `f06bd64a5524761018d21ab1b1b48c5113d08ae2cd0e09bc5c357b9dd42303c8`.

The exact defect under E(kx), H(kx) is 1/k times the unit-frequency
defect at kx. The normalized cross product and the oscillatory phase are
checked explicitly, including the total definitions at zero. Both actual
TM and TE sources inherit radiation along every path escaping to infinity.
The final statements assemble both actual weak curl equations with that
radiation condition, using the respective layer dispersion conditions.

Tests still avoid the source point. This establishes neither its distributional
normalization nor the full spatial dyadic Green identification. The module
is unregistered pending independent audit and a later aggregate release.
