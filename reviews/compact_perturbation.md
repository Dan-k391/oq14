# Compact perturbation kernel and range

Source: `lean/CompactPerturbation.lean`.

SHA256: `0912E8DF228128DA8012B85B7F3426E6387C00AE818C2469F4FD21C3A7C755BF`.

Pinned Lean 4.19 source compilation and direct olean emission passed on 2026-10-20. All six exported theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`. Independent full-source modal-agent review passed.

The fixed-point kernel of a genuine compact operator inherits compactness of its identity map; compactness of its unit ball proves finite dimension. A compact-subsequence contradiction gives an actual positive unit-sphere gap on any closed subspace without nonzero fixed points. Normalization gives a norm bound.

On a complex Hilbert space, the orthogonal complement of the kernel meets this hypothesis. Its bounded-below restricted defect has closed range. Orthogonal projection proves that this range is exactly the range of the full defect.

These results contain no assumed Fredholm alternative, finite-dimensionality premise, or closed-range premise. They do not yet prove injectivity implies surjectivity.
