# Actual finite-ball reaction fields and point moments

Frozen source: lean/FiniteSphereReaction.lean.
SHA256: 8F365FE6DE1D2F2149A346A20C55DD0B5BC650080CED9AF14E7181EC5D796E1F.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all five reports use only propext, Classical.choice, and Quot.sound.
Log: lean/logs/FiniteSphereReaction-final.log. Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

The genuine finite L2 source is identified AE with the sum of the genuine
individual ball sources; actual integrability is derived. The actual reaction
integral is exactly the sum of the actual individual ball reaction integrals.
It differs from the reaction kernel evaluated at each center and multiplied
by the actual volume-polarization moment by at most the derived kernel
Lipschitz constant times the sum of radius times actual coordinate source mass.

For any actual integrable physical source, its reaction field differs from
these finite point moments by at most entryBound times the actual coordinate
L1 difference from the genuine finite-ball trial, plus the preceding derived
moment error. The L1 error remains the literal integral in this theorem;
subsequent scaling instantiates the already proved actual material inverse
family, rather than assuming a response or Green convergence conclusion.
Physical finite-stack kernel identification and plane estimates remain open.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `8f365fe6de1d2f2149a346a20c55dd0b5bc650080ced9af14e7181ec5d796e1f`. Independent log `lean/logs/FiniteSphereReaction-root-audit.log`, SHA256 `1ea055328ecbd94e4c02da2ff3b34e044954a1f01c15146e07aa217afbf0ef97`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
