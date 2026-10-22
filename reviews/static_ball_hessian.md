# Actual global weak Hessian and Poisson source of the ball potential

Source: `lean/StaticBallHessian.lean`.
SHA256: `6CFA65CFDF9DE09786C581937E271E1B65D57A67BA32DE7E5B27C1F8F0DE7693`.

Author pinned Lean 4.19 compilation and object emission completed with exit 0,
without warnings. All 14 selected reports are standard-only. Importable
object: 731768 bytes. Independent review is pending.

The actual gradient is force(R,norm(x))*x_j. It is globally continuous.
Actual off-origin/off-sphere derivatives give the explicit Hessian:
`-delta_ij/3` inside and `R^3*(x_i*x_j/r^5-delta_ij/(3*r^3))` outside.
Its local integrability is proved from an exterior formula whose denominator
is clipped below R/2; the clipped formula is genuinely continuous. The
existing RadialInterface weak integration-by-parts theorem then proves
global weak Hessian pairings, including the interface.

The complex scalar potential's actual first derivative is identified with
that gradient. Two actual integrations by parts give the full potential
Hessian pairing. The explicit Hessian trace is proved AE equal to minus the
actual ball indicator, using the null sphere and actual coordinate norm
identity. This proves the global weak equation -Delta(Psi_R)=1_ball, rather
than assuming that no boundary delta is present.

This module does not yet identify the explicit Hessian with the actual
Newton/projection operator applied to a genuine constant-ball L2 source.
Global L2 construction and that operator identification remain necessary
before the manuscript's exact -P/3 source-response theorem can be claimed.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 14 reports using only standard foundations. Final source SHA256 `6cfa65cfdf9de09786c581937e271e1b65d57a67ba32de7e5b27c1f8f0de7693`. Independent log: `lean/logs/StaticBallHessian-root-audit.log`; log SHA256 `14717af444c9d89377b554a1e7cb8e1e24daa307dd3c5e8c90d8d17546b02426`. This certifies the stated scope, not either complete OQ14 construction.
