# Actual scalar source radiation estimate

ScalarRadiation has thirteen checked exports. For a compactly supported L1
source in the radius-R ball, the actual gradient response minus
`ik unitCoordinate(x)` times the actual scalar response is bounded outside
radius 2R by

`((2 |k| R + 1) / (pi |x|^2)) integral |rho|`.

The proof derives the radial gradient factorization, controls the change
of unit direction from x to x-y, and establishes absolute integrability
of both individual source responses before subtracting their integrals.
Along any path escaping to infinity in norm, the radius times that defect
converges to zero by the quantitative bound and the squeeze theorem.
No path continuity is required.

This file concerns the actual gradient-kernel response. Identifying it as
the classical derivative of the scalar response outside the source is a
separate ScalarExterior step. This file does not assert vector radiation
or the Silver–Müller condition.

The root compilation succeeded and emitted the importable object with
thirteen standard-only axiom reports. Counterexamples independently read
and approved the complete source, including the appended path-limit
theorem. The source is outside the 1058-declaration saved batch.
