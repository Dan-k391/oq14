# Actual scalar Euclidean Plancherel formalization

Status: PROVED in Lean 4.19.0 with pinned mathlib. The file is `lean/FourierL2.lean`.

The construction starts from mathlib's ordinary Fourier integral, with kernel exp(-2 pi i inner(x,xi)). It proves the conjugation/reflection identity and uses the bilinear Fourier integral interchange and Schwartz inversion to establish Parseval on actual Schwartz functions. No Plancherel operator is a premise.

The density proof is independent of Fourier theory: actual compact smooth functions satisfy all Schwartz derivative decay bounds; an L2 field orthogonal to the embedded Schwartz range is locally integrable and annihilates every compact smooth real scalar test. The existing fundamental distribution test theorem makes it zero almost everywhere. The orthogonal-complement criterion then proves the embedded Schwartz range dense in L2.

Fourier acts isometrically on this range with its L2 norm. The actual bounded extension along the dense isometric inclusion preserves norms by continuity. Its image contains the whole embedded Schwartz range by the inverse Schwartz transform; since the isometric image of complete L2 is closed, the extension is onto. The final `fourierEquiv` is therefore an actual complex linear isometric equivalence. Exports prove its agreement almost everywhere with the Fourier integral on Schwartz functions, inverse agreement, inner-product and norm preservation, and uniqueness among continuous linear extensions.

Validation: direct compilation completed successfully with no warnings or errors. All 23 theorem exports were checked using `#print axioms`; each has exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no custom axioms or proof placeholders.

Independent review: hotspots read the complete source, including conjugation and inverse signs, inner-product orientation, compact-smooth Schwartz construction, distribution annihilator density, actual L2 range norm, extension, closed-range surjectivity, and uniqueness. No defect found.

Scope: this file establishes scalar L2 Plancherel on Euclidean three-space. Vector lifting, the previously constructed frequency multiplier's physical-space conjugation, and identification with the static Newton kernel are separate subsequent work. No Maxwell boundary-value or scattering conclusion is claimed by this file.
