# ModalScaledPole — actual simple poles on the physical scaled shell

Source: `lean/ModalScaledPole.lean`

SHA256: `F511CF5AFBB3611FBC6DB646B58EBAB4C509E790C92349451B4884E0AE0C3818`

The fixed-shell response is the actual composition R_s(κ) = R(sκ).
The regularized family is G_s(κ) = G(sκ)/s. Its analyticity, nonzero
center, and exact punctured normal form establish meromorphy, order minus
one, and an operator-norm residue limit equal to the original residue
operator divided by s.

The physical shell is parametrized by y = sx, with x in the original
closed unit-to-two shell. The coordinate map is injective and has range
exactly the shell s ≤ norm(y) ≤ 2s. The parameter measure is s cubed times
the original shell measure. Its pushforward is proved equal to ordinary
three-dimensional volume restricted to the physical shell. The target L2
space therefore carries the actual physical volume rather than a
normalized probability or artificially unchanged shell measure.

The physical lift is a bounded injective complex-linear map between the
original shell L2 space and the physical shell L2 space in these coordinates.
It keeps field values unchanged in coordinates and has the exact L2 norm
factor given by the square root of s cubed. The implementation retains the
equivalent ENNReal power expression for that factor.

Postcomposition with this lift gives an actual physical response and an
actual physical residue. The physical response agrees almost everywhere
with the original outgoing fields evaluated at y/s. The physical residue
agrees almost everywhere with 1/s times the same globally constructed
dilated electric and magnetic weak mode. A nonzero original residue input
remains nonzero after this lift and frequency residue factor.

The physical response has its own analytic normal form, exact simple-pole
order, and actual operator-norm residue limit in the physical L2 space.
The final existence export chooses s = Re(k)/k0 for any prescribed k0 > 0,
retaining negative imaginary part and arbitrary quality threshold.

Self-review checked both inverse radius factors in the normal form, the
operator versus vector applications of the lift, the ordinary-volume
pushforward identity, positive-radius conditions, L2 measure scaling,
injectivity needed to preserve pole order, punctured residue limits, and
the almost-everywhere identification at the physical interface.

Scope: this is the two-data spherical matching shell response transported
to the physical shell. It is not an identification of the full Maxwell
resolvent. No reciprocal mode normalization, cross-degree pole separation,
or hotspot packing follows from these exports.

Evidence: `lean/logs/modal-scaled-pole-check.log`. All 30 selected exports
compiled cleanly with an importable object and only `propext`,
`Classical.choice`, and `Quot.sound`. Root independently read the complete
final source at the recorded hash and passed all 30 exports, including the
ordinary-volume shell map and exact residue factor. The source is frozen.
