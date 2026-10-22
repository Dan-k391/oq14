# Exact Newton action on genuine constant-ball sources

Source: `lean/StaticBallNewton.lean`.
SHA256: `5255F946DA4B3732C9B0EB742836738239F0C877EBCA619EC452CCE53246CA12`.

Author final pinned Lean 4.19 compiler and object emission pass with exit 0,
no warnings, and all eight reports using only propext, Classical.choice, and
Quot.sound. Log: `lean/logs/StaticBallNewton-final.log`.
Root independent full-source mathematical and pinned compiler review PASS
at the same hash, no warnings and all eight standard-only reports.
Independent log: `lean/logs/StaticBallNewton-root-audit-final.log`.

The source is a genuine vector L2 element assembled from actual scalar ball
indicator L2 elements times an arbitrary complex polarization vector. Its AE
representative is proved to be exactly the constant-ball source in physical
Euclidean coordinates. The response is a genuine vector L2 element assembled
from the proved actual weak Hessian times that vector.

A general Fourier-component formula for the existing Newton operator is
derived from its already proved physical-projection Hessian symbol. The ball
source and explicit response Fourier components agree by the previous actual
ball symbol theorem. Injectivity of the actual Fourier equivalence and the
actual coordinate isometries prove equality of the existing Newton operator
applied to this source and the explicit response. No operator identity is a
premise. The interior value -P_i/3 is then derived from the actual explicit
Hessian and its finite coordinate sum.

Scope: any positive radius, ball centered at zero, any constant complex
polarization vector, genuine full-space L2 equality and AE interior response.
Translation to arbitrary centers, separated-ball interactions, the isolated
sphere self-consistency factor, and dynamic or finite-stack Green estimates
are separate steps. The existing Newton operator already has its actual
distributional spatial convolution identification in NewtonL2/NewtonL1L2.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 8 reports using only standard foundations. Final source SHA256 `5255f946da4b3732c9b0eb742836738239f0c877ebca619ec452cce53246ca12`. Independent log: `lean/logs/StaticBallNewton-root-audit-final.log`; log SHA256 `b2ec9e780c013f3440dcd7bbb380b39ce903e90da90304d01c3c93fecb5f8cbb`. This certifies the stated scope, not either complete OQ14 construction.
