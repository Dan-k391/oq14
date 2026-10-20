# Independent regional Maxwell continuation audit

Reviewer: continuation_review_sol. Date: 2026-10-20.

Source: `lean/RegionalMaxwellContinuation.lean`.
SHA256: `46CC168EEBDAEF62B187B342F67A96EFB0A253A82C01837EE3FA7D9DCA803127`.

Independent pinned Lean 4.19 execution of
`lake env lean RegionalMaxwellContinuation.lean` completed with exit 0.
All six dependency reports list only `propext`, `Classical.choice`, and
`Quot.sound`. The final hash was checked again after compilation and is
unchanged. The complete source and complete RegionalMaxwellLocalization
and RegionalMaxwellHelmholtz sources were read, as were the actual
MaterialMaxwell field-pair and TestMaxwell definitions. The actual scalar
continuation chain was independently audited in
`reviews/weak_helmholtz_continuation.md`.

The new theorem is a genuine electric-field continuation result. The global
Maxwell predicate consists of the actual compact-smooth-test curl pairings
and the actual dielectric-weighted electric-field integrals. Regional tests
embed in those global tests. When the weighted electric field agrees almost
everywhere with multiplication by a positive constant, localization therefore
gives actual constant-material regional Maxwell equations. Commuting test
derivatives proves divergence of curl is zero and curl-curl equals
gradient-divergence minus Laplacian. Local integrability of each electric
component justifies the integral sums, giving the literal weak scalar
Helmholtz equation at frequency `k * sqrt epsilon0`.

The frequency is proved nonzero from nonzero real k and positive epsilon0.
An actual electric almost-everywhere zero ball supplies a zero germ for
each component. The proved weak Helmholtz continuation theorem then gives
each component zero almost everywhere on an open preconnected weighted
region. A finite-component almost-everywhere conjunction recovers actual
vector equality with zero. No magnetic zero hypothesis is used, and no
electric continuation conclusion is supplied as a premise.

For interface continuation, the bridge B is open and preconnected and
covered almost everywhere by U union V. U and V are open, V is preconnected,
both bridge intersections are nonempty, and the dielectric is constant
epsilon0 almost everywhere in V. On the U portion of B, the supplied actual
electric zero makes both weighted products zero; on its V portion, material
constancy makes them equal. The common almost-everywhere exceptional sets
are combined explicitly. Thus the actual PDE has the constant V material
throughout B in the required weak sense.

A point of B intersect U has an actual electric zero germ, since U is open.
The weighted-region result proves electric zero almost everywhere in B.
A point of B intersect V then has an actual zero germ by openness of B,
and the same result propagates zero throughout V. The geometry assumptions
express only open-set connectedness, overlap, and almost-everywhere coverage;
they do not assume a PDE continuation property. No U connectedness or material
constancy is required, since U is already known electrically zero.

Scope: this proves continuation across each supplied bridge between suitable
constant-material cells, for globally componentwise locally integrable E and
the actual global weak Maxwell pairings with nonzero real frequency. It does
not construct bridge geometry, prove reachability or coverage for a material
partition, or alone prove global Maxwell/volume uniqueness or solvability.
In particular it does not justify continuation for arbitrary rough variable
dielectrics.

The source scan finds no standalone axiom/constant declarations or proof-hole
tokens. No proof source was edited. Mathematical and independent compiler
audit: PASS.
