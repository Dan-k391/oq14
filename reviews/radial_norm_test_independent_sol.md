# Independent Sol audit of actual annular norm tests

Source: `lean/RadialNormTest.lean`.

Audited SHA256: `B87C76A323DC610591086FB962E1694AAAB65FC088DF5A27A15AE45C2D918027`.

Independent full-source mathematical audit: PASS. Independent pinned Lean 4.19 compilation: exit 0, no warnings, eight dependency reports containing only `propext`, `Classical.choice`, and `Quot.sound`, on 2026-10-20. The frozen source was not edited.

The derivatives are actual real spatial coordinate derivatives of the literal composition eta of the Euclidean norm. At each nonzero point, the first derivative is eta prime times the corresponding radial unit coordinate; the second derivative includes both the eta double-prime radial term and the derivative of that unit coordinate. Summation using the actual coordinate-square identity gives eta double-prime plus twice eta prime divided by radius. Applying the actual Laplacian product identity to a homogeneous harmonic polynomial gives the correct coefficient twice the degree plus two, divided by radius.

Global smoothness at the origin is proved from eta vanishing on a neighborhood of zero and continuity of the norm. The actual topological support is contained in the inverse image of eta's support; a genuine bound on that support gives a Euclidean closed-ball bound and hence compactness. Exterior support containment follows directly from the radial support condition. No regularity, support, Laplacian, or field equation conclusion is assumed.
