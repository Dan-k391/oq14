# DynamicConvolution verification

Frozen source: `lean/DynamicConvolution.lean`.
SHA256: `8911DD1CC2468ECD3D42E88373BF78C0728B418D109672F5CE210BA73D1EDB33`.

Clean pinned Lean 4.19 compilation completed October 20, 2026. All 13 exported
theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
There are no admissions or extra axioms.

Each actual real-frequency dyadic remainder entry is truncated to a ball and
proved integrable. Its L1 mass is at most
`(14 k^2/(4 pi)) (3/2) volume(ball(0,1)) R^2`.
This uses the proved all-radius pointwise bound, so no additional `|k| R`
restriction occurs.

The actual scalar L1-convolution operator is lifted through the measure-
preserving physical coordinate maps and insertions. Summing the nine entries
gives the conservative operator bound nine times the entry mass. For every
integrable square-integrable vector source, the resulting vector L2 field
equals the literal truncated spatial convolution almost everywhere.

The hotspots agent independently read and accepted the entire source on
October 20. Kernel mass, coordinate and insertion bounds, finite sums, and the
spatial representation passed without a substantive defect.

Removal of the truncation on a bounded material support and the resulting
concrete volume inverse are developed separately in DynamicVolume. No Maxwell
PDE conclusion is asserted by this module.
