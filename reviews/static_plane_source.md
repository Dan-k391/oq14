# Genuine whole-plane L1 static source fields

Frozen source: lean/StaticPlaneSource.lean.
SHA256: 5EB012FD73726040844BEFAA02CE1B46F7F28F5C9B45AEF4B79FB6D1BC4427DA.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all five reports standard-only. Log: lean/logs/StaticPlaneSource-final.log.
Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

For any actual integrable scalar source whose nonzero values have absolute
height at least positive d AE, the literal static Hessian convolution field
is genuinely integrable over the whole observation plane. Its actual L1 mass
is at most (3/d) times actual source L1 mass. Product integrability is derived
from actual jointly measurable kernels, actual fiber plane bounds, and the
source integrability; genuine Fubini swaps the actual integrals.

No plane integrability, operator bound or convergence is supplied as a
hypothesis. This is a literal off-support spatial integral, not a restriction
of an arbitrary 3D L2 representative. Any application to such an operator
requires its existing exterior spatial identification. Finite-stack physical
Green identification and dynamic/flux bounds remain separate.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `5eb012fd73726040844befaa02ce1b46f7f28f5c9b45aef4b79fb6d1bc4427da`. Independent log `lean/logs/StaticPlaneSource-root-audit.log`, SHA256 `e7da3fe974d5e5adf341e949878165506e3d6b55423da79ee4c5ff0c69c20a5d`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
