# Exact isolated static sphere polarization

Source: `lean/StaticSpherePolarization.lean`.
SHA256: `4D1C63F886D799D7927B31D92A7FEA25097FCD7E1921D00398CD08CBFB4D1456`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all four reports using only propext, Classical.choice, and Quot.sound.
Final compiler/object log:
`lean/logs/StaticSpherePolarization-final.log`.
Root independent full-source mathematical and pinned compiler review PASS
at the same hash, no warnings and all four standard-only reports.
Independent log: `lean/logs/StaticSpherePolarization-root-audit-final.log`.

For any positive radius, nonnegative real susceptibility chi, and constant
complex incident vector E, the actual source is the genuine ball L2 source
with polarization 3 chi/(chi+3) E. Using the proved action of the existing
Newton operator, its literal static self-consistency equation is derived:
rho = 1_ball chi (E + Newton rho). The interior total field is proved equal
to 3/(chi+3) E. Replacing chi by epsilon-1 gives the manuscript factor
(epsilon-1) 3/(epsilon+2). These identities are derived, not premises.

Scope: an isolated sphere centered at zero under a constant incident field,
with AE global source equation. Uniqueness against every possible L2 source,
translation to arbitrary centers, separated-sphere interactions, variable
incident fields, and dynamic/parity/finite-stack perturbations remain separate
steps. This module does not claim the manuscript's small-inclusion residual
or source convergence estimates.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 4 reports using only standard foundations. Final source SHA256 `4d1c63f886d799d7927b31d92a7fea25097fcd7e1921d00398cd08cbfb4d1456`. Independent log: `lean/logs/StaticSpherePolarization-root-audit-final.log`; log SHA256 `9867689306041c9bf8640e9a33ec029cc8fed9e1d2f8567c3a2acb6676dedf27`. This certifies the stated scope, not either complete OQ14 construction.
