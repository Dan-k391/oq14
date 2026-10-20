# Actual finite-rank approximation of compact operators

Source: `lean/HilbertFiniteRank.lean`.

SHA256: `596CAC913957AED3B5F9F1701F857E774DA0A4DE59B87DB187C6A1840C1AB1BC`.

Pinned Lean 4.19 source compilation with direct olean emission passed on 2026-10-20 (compiler exit 0, no warnings). All three theorem exports have axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Root's full-source conceptual audit passed. The source is frozen at this hash.

A genuine compact operator maps the unit ball into a set with compact closure. A finite epsilon/2 net spans an actual finite-dimensional subspace. Orthogonal projection onto this span minimizes distance to each net point, so its composition with the original operator has unit-sphere error at most epsilon/2. Homogeneous normalization gives the operator norm bound, strictly below epsilon.

The approximation is exported both as a factorization through a finite-dimensional subspace and as an endomorphism with finite-dimensional range. No approximation-property hypothesis or finite-rank approximation conclusion is assumed. Ambient completeness is unnecessary because the finite-dimensional projection subspace is complete.
