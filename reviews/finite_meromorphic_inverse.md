# FiniteMeromorphicInverse — actual analytic adjugate and meromorphic inverse

Source: `lean/FiniteMeromorphicInverse.lean`

SHA256: `3A3CF8797F4A5FC5A7A827A8BD1409598D7BDC255FF987BBE940F3BB3309CD4E`

The module uses the actual determinant and coordinate-analyticity exports
of `FiniteDimensionalDeterminant`. Matrix adjugate entries are determinants
of actual row replacements, so each is analytic by the finite Leibniz
formula. A finite-basis algebra equivalence reconstructs the adjugate as an
actual continuous linear endomorphism. Its reconstruction map is bounded
and complex-linear, which gives analyticity in operator norm.

The actual total `Ring.inverse` is proved equal to determinant inverse
times the reconstructed adjugate, including at singular matrices. The
proof transports the true matrix inverse through the algebra equivalence;
singular total inverses are zero. Analyticity of the adjugate and scalar
meromorphy of the determinant inverse therefore prove unconditional
meromorphy of the actual finite-dimensional operator inverse.

At a unit the actual inverse is analytic. At any point the actual unit set
has the local alternative: no units in a neighborhood, or units throughout
a punctured neighborhood. On a connected analytic domain, one actual unit
basepoint excludes the first alternative everywhere by analytic uniqueness
of the scalar determinant. Thus nonunits are isolated.

At a nonunit with punctured invertibility the meromorphic inverse has
strictly negative order. Otherwise it would have a finite limit C, and the
two actual inverse identities would give A(z)C = CA(z) = 1 by continuity,
contradicting that A(z) is a nonunit. The final export supplies these
conditions directly from a unit basepoint on a connected domain.

Self-review checked row and column indices in the adjugate, the fixed
basis and inverse algebra equivalence, the elementwise matrix norm used
only for the finite-coordinate analytic proof, singular total-inverse
behavior, operator-norm reconstruction, connected-domain uniqueness, both
sides of the limiting inverse contradiction, and the distinction between
meromorphy and actual negative pole order.

Scope: these are finite-dimensional inverse theorems with analyticity as
input. No compact approximation, Banach-space Schur reduction, global
analytic Fredholm conclusion, or Maxwell spectral identification is
assumed or claimed by this module. They are supporting inputs to the
separate actual compact-pencil construction.

Evidence: `lean/logs/finite-meromorphic-inverse-check.log`. The final 14
selected exports compiled cleanly with an importable object and only
`propext`, `Classical.choice`, and `Quot.sound`. Root independently read
the complete final source at the recorded hash and passed all 14 exports.
The source is frozen.
