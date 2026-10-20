# Disjoint-ball exterior geometry

Source: `lean/DisjointBallGeometry.lean`.

SHA256: `1B7D3EE183975F56EF307786026A997D5F4F6D60FFA73CFA8EF48DB02F4202FE`.

The final Lean compiler completed with exit 0 and produced the importable object (465672 bytes). All 18 selected theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The strict exterior of any finite family of pairwise strictly separated nonnegative-radius balls is proved path connected, connected, and open. The proof uses actual paths avoiding the finite center set, actual finite positive inflation preserving endpoint distances and pair separation, and an explicit continuous radial push. The finite sum representing the push has at most one active correction. Its image lies in the original strict exterior and it fixes both endpoints. Connectivity is derived, with no connectivity premise.

An explicit axis point proves nonemptiness and existence outside any prescribed radius. Positive radii and actual interface bridges are supplied separately by `DisjointBallCells.lean`. Enclosing shells and cavities are outside this source's claim.

Status: root full-source audit and independent compiler PASS. Frozen at the hash above.
