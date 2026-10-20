# FiniteRankSchur — actual typed Schur algebra and Woodbury inverse

Source: `lean/FiniteRankSchur.lean`

SHA256: `F9929A95165F1F3844D1A41C1FCF084BCD35731675429B1923BFAC4FDF5F622D`

Evidence: `lean/logs/finite-rank-schur-check.log`. All 11 selected exports
compiled cleanly with an importable object and only `propext`,
`Classical.choice`, and `Quot.sound`.

The algebra is formulated for continuous linear maps on arbitrary normed
spaces E and V over a nontrivially normed field. No completeness or finite
dimension hypothesis is needed by these identities. The intended use
specializes E to the Banach or Hilbert field space and V to the fixed
finite-dimensional approximation space.

For U:V→E and B:E→V, the proof constructs both actual inverse identities
between 1-UB and 1+U(1-BU) inverse B. Interchanging E and V proves that
1-UB is a unit exactly when 1-BU is a unit. All inverses use the existing
total `Ring.inverse`, with unit hypotheses supplying its cancellation laws.

For a unit A:E→E, I:V→E, and B:E→V, the Schur operator is
D = 1 - B A inverse I. The actual factorization
A-IB = A(1-A inverse I B) proves the invertibility equivalence with D.
The constructed inverse of A-IB is exactly
A inverse + A inverse I D inverse B A inverse, with typed continuous-linear
composition throughout. Both left and right inverse identities and equality
to the actual `Ring.inverse` are exported.

Self-review checked the rectangular map directions, order of every factor,
unit conditions used by total inversion, the two independent Jacobson
cancellation identities, factorization order, and the final inverse
uniqueness argument. The interface was coordinated with `HilbertFiniteRank`
and uses its preferred `Ring.inverse` convention.

Scope: no compact approximation, determinant, analytic continuation,
meromorphy, spectral multiplicity, or Fredholm theorem is assumed or claimed
by this algebra module. Those constructions can use its exact finite-space
reduction. Root independently read the complete final source at the
recorded hash and passed all 11 exports. The source is frozen.
