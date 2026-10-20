# Actual dynamic operator controlled by support volume

Source: `lean/DynamicSupportVolume.lean`.

SHA256: `D7969C329D08FEF29B8ABF36AA65FDC105C9E4EFB9D5D28A11933705083D9B75`.

Author pinned Lean 4.19 compilation and object emission completed with exit 0.
All 13 selected dependency reports use only `propext`, `Classical.choice`,
and `Quot.sound`. Importable object: 463528 bytes.

The actual weighted dyadic dynamic remainder has norm at most
`c.bound * sqrt(volume.real K) * kernelSize k R`, where `kernelSize` is
the sum of the nine actual truncated physical kernel L2 norms at radius
`2*R`. The proof identifies actual convolution representatives, uses their
L2 Cauchy--Schwarz bound, and uses the actual output material support.
No operator convergence or small-volume conclusion is a hypothesis.

The enclosing radius is fixed, and the actual coefficient is bounded,
measurable, nonnegative, supported both in its enclosing ball and in a
measurable set of finite volume. The inverse results derive the actual
static-minus-dynamic block unit and inverse norm at most two when the
explicit bound is at most one half.

The finite-ball wrapper derives enclosing support, measurability, and finite
volume from actual centers and radii. It uses actual three-dimensional ball
volume and union subadditivity. Overlap is permitted because the bound is
an upper bound. For finitely many radii proportional to a, this gives a
square-root-volume bound of order a to the three-halves at fixed enclosing
radius, not the manuscript's sharper order a squared Schur estimate.

This does not yet include parity reactions, the exact isolated-sphere static
polarization, shrinking-gap plane estimates, or a physical background Green
limit. Independent review is pending.

## Independent root verification on resumption

Full source reviewed; pinned compiler EXIT0. All 13 reports use standard foundations. Exact source SHA256 `d7969c329d08fef29b8abf36aa65fdc105c9e4efb9d5d28a11933705083d9b75`. Independent log: `lean/logs/DynamicSupportVolume-independent-root.log`. The assumptions retain the stated scope and do not close the complete device construction.
