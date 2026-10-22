# Independent audit: LocalRadialHarmonic

Frozen source: lean/LocalRadialHarmonic.lean.
SHA256: CD2429A35CD58B9241492ECE3349B609085F4B9F554C4BDE36E37391BA1C1BE3.

Independent complete-source mathematical review and pinned Lean compiler PASS.
The compiler exits 0 without warnings; all six reports use only propext,
Classical.choice, and Quot.sound. Log:
lean/logs/LocalRadialHarmonic-independent-continuation.log.

Actual derivatives of eta(norm x) on punctured Euclidean three-space yield
its Laplacian eta'' + 2 eta'/r. Product differentiation with an actual
homogeneous harmonic polynomial gives the additional 2l eta'/r term, using
the actual Euler identity and polynomial Laplacian. A literal scalar radial
ODE then implies the actual scalar Helmholtz equation for the product.

The origin is excluded. Smoothness on positive radii, homogeneity, harmonicity,
and the radial ODE are explicit mathematical hypotheses; no Helmholtz or
reconstruction conclusion is assumed. Specialization to actual regular and
outgoing radial functions and all Maxwell/interface work are separate steps.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 6 reports using only standard foundations. Final source SHA256 `cd2429a35cd58b9241492ece3349b609085f4b9f554c4bde36e37391ba1c1be3`. Independent log: `lean/logs/LocalRadialHarmonic-independent-continuation.log`; log SHA256 `33fb77994b1ed8afa8e85396580d8f41707e63985e9148733dc9472ffceaa916`. This certifies the stated scope, not either complete OQ14 construction.
