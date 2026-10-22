# Actual Schwartz weak Hessian of the uniform-ball potential

Source: `lean/StaticBallSchwartz.lean`.
SHA256: `C5F2D5D6D25EB79A00F99F239D612F95065E7125D0E77447BD4E1FB621B653AB`.

The author final compiler and object emission pass with exit 0, no warnings,
and all seven reports using only propext, Classical.choice, and Quot.sound.
The final compiler/object log is
`lean/logs/StaticBallSchwartz-final.log`.
Root independent full-source mathematical and pinned compiler review PASS
at the same exact hash, no warnings and all seven reports standard-only
(session 70526).

The new one-dimensional FTC uses actual finite-interval off-countable FTC
and the proved convergence of integrals over expanding intervals. Vanishing
boundary values at both infinities are hypotheses of this generic theorem.
For actual coordinate lines these hypotheses are then proved: their norm
dominates the absolute line coordinate, Schwartz functions vanish at infinity,
and the actual uniform-ball gradient has the proved uniform bound R/3.

Fubini removes the transverse origin and the finite sphere intersections.
The genuine L2 pairing bounds provide the integrability of both derivative
products. This proves that the explicit Hessian L2 element is the actual weak
derivative of the explicit gradient L2 element against every Schwartz test.
No operator identification is assumed. Fourier and Newton identification
remain the next steps.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 7 reports using only standard foundations. Final source SHA256 `c5f2d5d6d25eb79a00f99f239d612f95065e7125d0e77447bd4e1fb621b653ab`. Independent log: `lean/logs/StaticBallSchwartz-root-audit.log`; log SHA256 `4ec3bfd9dcb59de54f563575f1b0d7ff9da14e76c3a8f5858bb5c11f38b98dbf`. This certifies the stated scope, not either complete OQ14 construction.
