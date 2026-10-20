# Dynamic volume equation: actual integral and inverse

Frozen source: `lean/DynamicVolume.lean`.

SHA256: `F651F6DCCF6DFB03FDE296B1AE8FC80742FF81DE91D855EE84465F3EC4CD8D69`.

The direct pinned Lean 4.19 compiler completed successfully on 2026-10-20. All 14 printed theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`. No admissions or new axioms are used.

The source proves that compactly supported bounded nonnegative contrast produces an actual integrable material source. On a ball of radius R, the convolution cutoff at 2R is exactly removable. The full dynamic remainder integrands are integrable for almost every observation point, and the weighted operator has the literal untruncated spatial integral representation. Its norm is bounded by `9 * entryMass k (2*R) * c.bound`.

The positive static operator minus this actual dynamic remainder is invertible when that bound is less than one. The module proves the inverse bound, existence and uniqueness for every L2 right-hand side, and the solution norm estimate.

Hotspots independently audited the complete source and found no defect. In particular, the two contrast square roots give exactly the contrast bound, support localization is pointwise, and actual source integrability precedes convolution identification.

Scope: these are spatial integral-operator and algebraic L2 solution statements. The module does not claim the solution satisfies the distributional Maxwell PDE or a radiation condition. Those identifications belong to the separate source/PDE track.
