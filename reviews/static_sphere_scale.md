# Actual sphere volume and explicit perturbation scaling

Source: `lean/StaticSphereScale.lean`.
SHA256: `80C7A03793772FD8DBD127C2BE9D697A50DE4951447303776815EF88387582F9`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all nine reports using only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticSphereScale-final.log`. Root independent full-source
mathematical and pinned compiler review PASS, no warnings and all nine reports
standard-only. Log: `lean/logs/StaticSphereScale-root-audit.log`.

Actual three-dimensional ball volume and its square root are evaluated for
radius rho*a, including arbitrary centers. The material trial has a proved
norm bound by sqrt(chi) times the sum of the incident component norms times
the square root of this actual volume.

For 0<a<=1, the genuine kernel-derived explicit perturbation bound at gain
b/a is bounded by K*a, where K is defined explicitly using the fixed enclosing
radius, actual dynamic kernel L2 norms, actual parity reaction entry bound,
susceptibility bound, and volume coefficient. The existing support-volume
operator estimate discharges the actual operator bound. An explicit positive
smallness radius makes K*a<1/2 for all sufficiently small a. No operator norm
smallness or source convergence conclusion is assumed.

This deliberately uses the already proved weaker dynamic O(a^(3/2)) bound,
which suffices for the combined O(a) smallness. It does not relabel that
dynamic estimate as the manuscript's sharper O(a^2) estimate.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 9 reports using only standard foundations. Final source SHA256 `80c7a03793772fd8dbd127c2be9d697a50de4951447303776815ef88387582f9`. Independent log: `lean/logs/StaticSphereScale-root-audit.log`; log SHA256 `430cb55d0a5edede779c896c9cb441cb5f65bfaa1e5fea47da7b2853939f16eb`. This certifies the stated scope, not either complete OQ14 construction.
