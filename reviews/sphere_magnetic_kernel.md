# Actual magnetic sphere kernel

Frozen source: lean/SphereMagneticKernel.lean.
SHA256: 055D73C364425ED3690461D0713574A662C3F1A9DFF2BE50A1D56ABCC83C639C.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all eight reports standard-only. Log: lean/logs/SphereMagneticKernel-final.log.
Independent audit pending.

The literal sphere-integral electric tensor is differentiated using the
actual dominated Frechet integral formula. Its actual curl is I*k times
K, where K is a genuine transverse sphere integral. The cubic angular
moments cancel algebraically inside integrable actual surface integrals.
The new magnetic tensor K is continuous everywhere and obeys the same
uniform entryBound as J. Its actual incoming/outgoing representation is
(magneticDyadic(k)+magneticDyadic(-k))/(2I) off the source at nonzero k;
the definition magneticDyadic is precisely the gradient/cyclic-index
magnetic kernel underlying the existing actual magnetic convolution.

The curl identity holds without excluding zero frequency or the origin.
The incoming/outgoing formula requires nonzero frequency and displacement.
Actual reflected parity, whole-plane tails and physical finite-stack Green
identification remain separate constructions.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 8 reports use only standard foundations. Final source SHA256 `055d73c364425ed3690461d0713574a662c3f1a9dff2be50a1d56abcc83c639c`. Independent log `lean/logs/SphereMagneticKernel-root-audit.log`, SHA256 `4d859405df7159027edd7e037d5f5a9b6b6378892cda707b24376b057b789349`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
