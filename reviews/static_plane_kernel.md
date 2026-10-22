# Genuine static Hessian plane L1 kernel bound

Frozen source: lean/StaticPlaneKernel.lean.
SHA256: 571D2DAAA4B16170EF857F40F62B6885F9A3DB6D7FE25549E0683C3E5F7A7AF1.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all twelve reports standard-only. Log: lean/logs/StaticPlaneKernel-final.log.
Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

An actual inverse-cube envelope is integrated on the genuine Euclidean plane:
a radius-d disk has constant value d inverse cubed, and its complement has
norm inverse cubed. Its actual integral is 3*pi/d. Horizontal translation is
derived using measure preservation. Actual coordinate geometry gives both
source-height and horizontal-distance lower bounds for distance to a plane point.

The literal Hessian of 1/(4*pi*norm z) has norm at most 1/(pi*norm z cubed),
derived from the already proved exact ball kernel identity and actual Hessian
norm bound. Consequently, for any source point with absolute height at least
positive d, each actual Hessian coordinate is integrable over the whole plane,
with actual integral of its norm at most 3/d.

No plane integrability or operator bound is an input. This theorem concerns
the literal spatial kernel. It does not restrict an arbitrary 3D L2
representative to a plane, nor identify a physical finite-stack Green kernel.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 12 reports use only standard foundations. Final source SHA256 `571d2daaa4b16170ef857f40f62b6885f9a3db6d7fe25549e0683c3e5f7a7af1`. Independent log `lean/logs/StaticPlaneKernel-root-audit.log`, SHA256 `4afe15e9f485cbe8232760868983f126d24efe4708b4a006183eae36f5a82991`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
