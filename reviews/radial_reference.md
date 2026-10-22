# Independent audit of exact constant radial propagation

Source: `lean/RadialReference.lean`.
SHA256: `F0B34F787F3D3941DFED3C5F34E3487D000215087BF63433ED00FA769A6DBC11`.

Independent full-source mathematical review: PASS. The matrix entries are
the actual sine/cosine fundamental solution for u'=sigma p and
p'=-(q^2/sigma)u. Its determinant-one proof follows from the trigonometric
identity with q and sigma nonzero. Both real matrix-column derivative
identities and the actual complex-state solution ODE are derived.

The exact quarter-wave width is pi/(2q). The ordered pair with the vacuum
quarter wave is proved diagonal, with entries -q/sigma and -sigma/q.
The recursively composed matrix powers have the actual corresponding
powers as diagonal entries. No transfer conclusion is supplied as a premise.

This proves an exact constant-coefficient reference model. Comparison with
actual variable radial layers, a large-radius limit, and any Maxwell Green
or amplification conclusion are separate theorems.

Independent pinned Lean 4.19 compiler log:
`lean/logs/RadialReference-independent-continuation.log`.
Independent compilation completed with exit 0, no warnings, and all seven
reports using only propext, Classical.choice, and Quot.sound.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 7 reports using only standard foundations. Final source SHA256 `f0b34f787f3d3941dfed3c5f34e3487d000215087bf63433ed00fa769a6dbc11`. Independent log: `lean/logs/RadialReference-independent-continuation.log`; log SHA256 `0d5f4256043b55edf39a58fed45640616a9844e8b593210cdb33d1a2ca4215fa`. This certifies the stated scope, not either complete OQ14 construction.
