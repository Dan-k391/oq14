# Actual incident variation and weighted sphere forcing

Source: `lean/StaticSphereForcing.lean`.
SHA256: `ABAE829B7E55E5CC40B131116162E62AD2F879CEBBBB1FE3E225239B1DCE9F79`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all four reports using only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticSphereForcing-final.log`. Root independent full-source
mathematical and pinned compiler review PASS, no warnings and all four reports
standard-only. Log: `lean/logs/StaticSphereForcing-root-audit.log`.

The genuine scalar ball indicator has its actual L2 norm sqrt(volume(ball)).
The actual constant-ball vector source norm is bounded by the sum of the
polarization component norms times this volume factor, at arbitrary centers.

For actual weighted incident forcing, a pointwise local incident variation
bound M gives an actual L2 forcing difference bound
3 sqrt(chi) M sqrt(volume(ball)). The proof uses actual L2 representatives,
the actual susceptibility multiplier, source subtraction, and an actual
translated ball-indicator majorant. A separate mean-value theorem discharges
M=L R from actual differentiability and actual Frechet derivative bounds L
on the convex ball. No response or Green convergence conclusion is assumed.

Quantitative incident derivative bounds for a specific background family,
the resulting radius powers, and finite-stack Green identification remain
separate inputs/constructions.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 4 reports using only standard foundations. Final source SHA256 `abae829b7e55e5cc40b131116162e62ad2f879cebbbb1fe3e225239b1dce9f79`. Independent log: `lean/logs/StaticSphereForcing-root-audit.log`; log SHA256 `885e3a7850616c8c512151fbdd02ac4179328d1a9859c1136571a5827e9cda2d`. This certifies the stated scope, not either complete OQ14 construction.
