# Actual parity reaction volume operators

Source: `lean/ParityReactionVolume.lean`.

SHA256: `D2E5B6A0CA5DA773AD96DB8058490383F5292A72CAEE3919C5F20A3EE292F244`.

Author pinned Lean 4.19 compilation and object emission completed with exit 0,
without warnings. All seven selected reports are standard-only. Importable
object: 322016 bytes.

The actual two-point spherical-integral parity kernels instantiate the
bounded material integral construction. Its output is identified AE with
the literal physical source integral, including both actual square-root
susceptibility multipliers. The resulting actual reaction operator norm is
at most `9*c.bound*volume.real K*entryBound k`. There is no postulated
operator identity or norm conclusion in the inputs.

The full explicit perturbation is the genuine dynamic remainder plus
`(B^2-1)*R_e + (B^(-2)-1)*R_m`. Its derived norm bound is the sum of the
square-root-volume dynamic estimate and the two absolute reaction
coefficients times the volume estimate. The positive static block then gives
actual invertibility when this numeric bound is below one, and an inverse
norm at most two when it is at most one half.

This module concerns the explicit Herglotz parity kernel. It does not identify
it with an actual finite-stack Green operator, assume a desired response
limit, or prove a leading isolated-sphere polarization. The small-ball
asymptotic threshold is a separate theorem in SmallParityInclusions.
Independent review is pending.

## Independent root verification for integration

Complete source reviewed and pinned compiler EXIT0 with no warnings. All 7 reports use standard foundations. Final source SHA256 `d2e5b6a0ca5da773ad96db8058490383f5292a72caee3919c5f20a3ee292f244`. Independent log: `lean/logs/ParityReactionVolume-independent-root.log`. The remaining complete Maxwell constructions are outside this audit.
