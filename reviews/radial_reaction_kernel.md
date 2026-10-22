# Actual scalar reaction and first mixed derivative bounds

Source: `lean/RadialReactionKernel.lean`.
SHA256: `81F3164698E7DB64D66B4CE0B43CBAD1CB32F52EE3BB97C1D81D6753CC9773B5`.

Author final compiler exit 0, no warnings; importable object 349552 bytes. All ten selected dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact log: `lean/logs/RadialReactionKernel-final.log`.

The literal scalarGreen minus its regular-irregular term is identified algebraically with gamma*regular(x)*regular(y). Genuine derivatives of the actual finite Riccati functions supply its left, right, and mixed first radial derivatives. Positivity of the actual derivative gives regular monotonicity in the proved barrier. Its actual logarithmic derivative upper bound then yields |regularD(x)|<=(l+1)/a*regular(s) for a<=x<=s<=R and a>0.

For either zero or one derivative in each variable, the actual scalar reaction derivative norm on [a,s]^2 is bounded by

    max(1,1/a)^2 * (l+1)^2 * norm(gamma) * regular(l,s)^2.

This is explicitly an annular estimate. It does not cover source compacts containing the origin; the raw finite Riccati formula at zero is not its analytic extension. An actual entire-extension construction is a separate successor. No spatial dyadic expansion is claimed.

Status: author PASS and root complete-source mathematical audit plus independent pinned compiler PASS (session 5105), exact frozen hash; no warnings and all ten reports standard-only. Source frozen.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 10 reports using only standard foundations. Final source SHA256 `81f3164698e7db64d66b4ce0b43cbad1cb32f52ee3bb97c1d81d6753cc9773b5`. Independent log: `lean/logs/RadialReactionKernel-root-audit.log`; log SHA256 `f4d2dc3311a31de40f6e1c344fc06ee3539f745a22cbcc73a01a47f820d465fb`. This certifies the stated scope, not either complete OQ14 construction.
