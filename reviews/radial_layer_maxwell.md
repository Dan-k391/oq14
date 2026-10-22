# Independent audit: RadialLayerMaxwell

Frozen source: lean/RadialLayerMaxwell.lean.
SHA256: AA3677C8EAF6834DF5BF699AEDCEE090DB77B87070F8AFFDF1406D98978A2FCC.

Independent complete-source mathematical review and pinned compiler PASS:
exit 0, no warnings, all six reports standard-only.
Log: lean/logs/RadialLayerMaxwell-independent-continuation.log.

The literal layer basis value is smooth on positive radii using actual
complex Riccati differentiability. Its true derivative is sigma times the
actual layer momentum, and that derivative has the actual centrifugal
Riccati second derivative. The actual normalized quotient therefore satisfies
the scalar Helmholtz equation; the explicit all-degree TE and normalized TM
layer fields satisfy the genuine Maxwell equations away from the origin.

All radial smoothness and differential equations are discharged from the
actual layer definitions, not supplied as final assumptions. Nonzero q and
sigma, dispersion and homogeneous harmonic polynomial data are explicit.
TE additionally uses nonzero k; TM uses nonzero epsilon. Sigma is the basis
state normalization, whose TE/TM physical interface specialization is separate.
No interface matching, global weak gluing, radiation or Green reconstruction
is asserted by these local layer PDE results.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `aa3677c8eaf6834df5bf699aedcee090db77b87070f8affdf1406d98978a2fcc`. Independent log `lean/logs/RadialLayerMaxwell-independent-continuation.log`, SHA256 `f9c4dc5e3fa79d2d37b0d997f52352a6f3604861f7b5f988961f70e0e50f17a2`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
