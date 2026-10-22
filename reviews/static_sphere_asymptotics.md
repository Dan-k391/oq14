# Constructed actual single-sphere source-error family

Source: `lean/StaticSphereAsymptotics.lean`.
SHA256: `A5341C77541AE25A22D98827166AEEE4395C29F1BBE4CB96BCCA9139E9784FF8`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and both reports use only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticSphereAsymptotics-final.log`.
Root independent full-source mathematical and pinned compiler review PASS,
no warnings and both reports standard-only.
Log: `lean/logs/StaticSphereAsymptotics-root-audit.log`.

The actual singleton-ball support data are constructed from the geometric
enclosing-ball inequality. For all sufficiently small positive a, the actual
ball radius rho*a lies in the fixed enclosing ball, the actual perturbation
bound is derived to be at most one half, and the actual existing parity-kernel
inverse applies. The positive smallness radius is proved to exist from an
explicit kernel-dependent scalar constant; no operator smallness premise is
left in the family theorem.

Actual incident local Frechet derivative bounds M/a and actual center
amplitude bounds A/a, together with the literal weighted forcing relation,
imply weighted and physical L2 source errors O(a*sqrt(a)) and actual
coordinatewise L1 errors O(a^3). The physical source and material-weighted
unknown remain explicitly distinct.

Scope: one sphere, arbitrary fixed center, fixed enclosing radius, and the
literal explicit parity kernel. The incident hypotheses still need to be
proved for a specific background family. This is not a finite-stack Green
identification, a moving-gap flux limit, or a multiple-sphere asymptotic theorem.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 2 reports using only standard foundations. Final source SHA256 `a5341c77541ae25a22d98827166aeee4395c29f1bbe4cb96bcca9139e9784ff8`. Independent log: `lean/logs/StaticSphereAsymptotics-root-audit.log`; log SHA256 `9f4a4521b3ec9abd4eab0acb2cf322c433373384e65c4685371971545f3566c2`. This certifies the stated scope, not either complete OQ14 construction.
