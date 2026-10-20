# HarmonicPolynomial verification

Frozen source: `lean/HarmonicPolynomial.lean`.
SHA256: `4D6B0D247F70E0D46DD07D747AC5C1DBE5C1AE02787EE15996F5DB27CBDE80CC`.

Pinned Lean 4.19 compilation and importable object export completed with exit 0.
All 21 selected dependency reports use only `propext`, `Classical.choice`,
and `Quot.sound`. Root independent full-source mathematical audit PASS.

The formal Laplacian is the actual sum of three polynomial second partial
linear maps. Product differentiation plus the homogeneous Euler identity
gives Delta(radiusSq*p)=(4n+6)*p+radiusSq*Delta(p). Finite induction gives
the explicit positive radial-power Laplacian coefficient.

The module evaluates actual real multivariate polynomials on Euclidean
three-space and then includes values in the complex numbers. Structural
polynomial induction proves smoothness and that each actual Frechet
coordinate derivative agrees with the formal polynomial partial. Thus
the actual spatial Laplacian agrees with the formal Laplacian evaluation,
and homogeneous polynomials satisfy the actual complex Euler identity.
These results supply concrete smooth harmonic functions for subsequent
sphere approximation and exterior Green arguments.
