# Actual material residual of finite isolated-sphere trials

Source: `lean/FiniteSphereResidual.lean`.
SHA256: `D0BED195731DA120F4F037FFA174B690A8C02622F76E3C865C6E8B0E80247A5A`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and both reports use only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/FiniteSphereResidual-final.log`. Root independent complete-source mathematical review and pinned compiler also pass: exit 0, no warnings, standard-only reports. See the corresponding lean/logs/FiniteSphereResidual-root-audit.log audit log.

The actual existing weighted static block applied to the genuine sum of
isolated-sphere weighted trials is compared with the genuine sum of piecewise
constant weighted incident sources. On each geometrically separated actual
ball, the residual is proved AE exactly minus sqrt(chi) times the actual
Newton operator on the sum of all other physical polarization sources.
The self term cancels by the already derived exact sphere identity.

Outside the actual finite ball union the residual is proved AE zero, using
the actual coefficient and genuine source representatives. No interaction
norm smallness, source convergence, or residual conclusion is assumed.
Quantitative global L2 norm bounds and the resulting inverse/asymptotic
comparison are the next steps.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 2 reports using only standard foundations. Final source SHA256 `d0bed195731da120f4f037ffa174b690a8c02622f76e3c865c6e8b0e80247a5a`. Independent log: `lean/logs/FiniteSphereResidual-root-audit.log`; log SHA256 `56b8aec9e2e1229c8c7acc575907c2d8b785e172b78cc8d881f69a23bedfe732`. This certifies the stated scope, not either complete OQ14 construction.
