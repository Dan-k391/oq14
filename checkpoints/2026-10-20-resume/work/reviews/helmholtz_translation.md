# HelmholtzTranslation verification

Source: `lean/HelmholtzTranslation.lean`.
SHA256: `1062E1CB14F09B0841DD1C496B90237548C7517D134BCCA3DF2D700C7B68E1F1`.

Pinned Lean 4.19 compilation and importable object export completed with exit 0,
without warnings. All 11 selected dependency reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

The translated function is literally v(y)=u(c+y). The pinned exact
Frechet derivative rule for invertible input translation proves equality
of actual first derivatives without extra regularity assumptions. Applying
that rule again to the exact derivative-function equality proves full
actual second Frechet derivative equality. Coordinate evaluation yields
actual first and second coordinate derivative identities, hence actual
Laplacian equality by summation.

Genuine smooth composition transfers local smoothness and smoothness on
a ball centered at c to the corresponding ball centered at zero. The
explicit ball-membership equivalence gives the actual constant-complex-
frequency Helmholtz equation transfer. A final equivalence translates
vanishing on the centered ball back to vanishing on the ball around c.
No continuation or PDE regularity conclusion is presumed.

Independent full-source review requested from root at this hash.

Root completed independent full-source and compiler audits at this hash. Final freeze PASS.
