# Actual weak div–curl regularity

`lean/WeakPoynting/DivCurlRegularity.lean` is frozen at SHA-256 `b9402e4487eded306ffc4f4c4f5fc5773562a4bf00fa880b897d2ec13578c7d4`. Its direct Lean 4.19.0 build exited zero with eight selected reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Complete compiler output and source-scoped provenance are in `divcurl-regularity-verification.txt` and `divcurl-regularity-provenance.json`.

The main result is `OQ14.DivCurlRegularity.compact_weak_derivatives_energy`. For an actual complex L2 vector field on Euclidean three-space, with compact-support representatives and genuine distributional L2 curl and divergence, it constructs all nine actual weak L2 coordinate derivatives. It also proves the exact equality between their total squared L2 norm and the sum of the curl and divergence squared L2 norms. No differentiability, derivative-existence, or H1 premise is imposed on the field.

The construction applies the independently proved Schwartz identity to differences of the explicit compact smooth approximants. Each derivative is bounded by twice the curl-divergence product norm; this factor follows from three curl terms plus one divergence term and the actual finite-product maximum norm. Curl and divergence convergence therefore makes every derivative sequence Cauchy. Completeness of actual scalar L2 supplies the limits. Continuity of the genuine compact-test pairings proves that those limits are weak derivatives. Finite sums and norm continuity then pass the exact energy equality to the limit.

The helper `weak_derivatives_of_approximation` states the explicit convergence argument for a supplied Schwartz sequence; the main compact-field theorem discharges that premise with the already proved convolution construction. Thus the final regularity theorem does not assume a density or approximation theorem shaped like its desired conclusion.

The hotspot agent independently read both this module and `DivCurlCompact.lean` and found no defect in the reflected divergence sign, compact representative construction, graph convergence, derivative estimate, completeness argument, weak-test limit, or energy equality. Parent registration and aggregate clean-build status are maintained separately by the coordinator.

This module concerns whole-space compact fields. Regional Maxwell magnetic regularity is developed separately in `LocalRegularity.lean`; no boundary trace, full Maxwell solution existence, or unrestricted scattering claim follows from this module alone.
