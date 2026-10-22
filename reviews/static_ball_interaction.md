# Actual interaction between separated constant-ball sources

Source: `lean/StaticBallInteraction.lean`.
SHA256: `C5DFF3E5163C1050E1C467A2DCF8C6CDA509A8C1A945BD5C18C2C86E46D1AA5D`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and all five reports using only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticBallInteraction-final.log`. Root independent full-source
mathematical and pinned compiler review PASS, no warnings and all five reports
standard-only. Log: `lean/logs/StaticBallInteraction-root-audit.log`.

The actual Newton operator on a genuine constant-ball source is identified
with the previously constructed actual Hessian. Its actual exterior formula
gives a coordinate bound (4/3) R^3/distance^3 times the sum of polarization
component norms. Geometric separation of centers derives the actual distance
of an observation point in another small ball from this source center.

Linearity and actual finite L2 sum representatives then give a bound on the
actual Newton field of the sum of all other constant-ball sources. For
center separation delta and radii at most delta/4, the explicit interaction
bound contains each radius cubed divided by (delta/2)^3. Separation is a
geometric hypothesis, not an operator or convergence conclusion.

Scope: finite constant-ball trial sources and actual exterior cross fields.
This is not yet an operator norm estimate for all arbitrary L2 sources or
a completed multiple-sphere material residual/asymptotic theorem.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 5 reports using only standard foundations. Final source SHA256 `c5dff3e5163c1050e1c467a2dcf8c6cda509a8c1a945bd5c18c2c86e46d1aa5d`. Independent log: `lean/logs/StaticBallInteraction-root-audit.log`; log SHA256 `0faf43002304af61069db792e1ab42a040551bfe1e4259382fd660c82871d6e0`. This certifies the stated scope, not either complete OQ14 construction.
