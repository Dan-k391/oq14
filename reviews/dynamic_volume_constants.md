# Explicit small-volume constant

Frozen source: `lean/DynamicVolumeConstants.lean`.

SHA256: `E3110224F54321C43EA107C9E37DAE9B6DC08CAD007384C5F7E9F1ABD676F35C`.

The pinned Lean 4.19 compiler completed successfully on 2026-10-20. Both exported theorem reports use only `propext`, `Classical.choice`, and `Quot.sound`.

The actual Euclidean three-dimensional unit-ball volume is evaluated as `4*pi/3`. Substitution into the proved dynamic operator estimate gives exactly

`errorBound c k R = 252 * c.bound * k^2 * R^2`.

Thus the preceding volume inverse theorem applies whenever this concrete number is less than one. The factor is deliberately conservative, inherited from the nine-entry vector estimate; no optimality is claimed.

The pinned mathlib `VolumeOfBalls` dependency was built locally without changing any version pins. Hotspots checked the constant against the earlier entry-mass proof; root has been asked to review the two exported source statements.
