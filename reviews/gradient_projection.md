# Actual differential characterization of the Fourier projection

Source: `lean/GradientProjection.lean`. Status: PROVED for the precise statements exported, in Lean 4.19.0 and pinned mathlib.

Directional derivatives use `SchwartzMap.pderivCLM` evaluated along the existing `Maxwell.basis`. Their values are definitionally the existing Maxwell Frechet coordinate derivatives. The Fourier derivative identity is derived from `Real.fourierIntegral_fderiv` and evaluation of the continuous-linear-map-valued Fourier integral; the sign is +2 pi i for the exp(-2 pi i inner(x,xi)) convention.

The actual L2 gradient of a Schwartz scalar field has Fourier transform (2 pi i Ff) xi. The previously constructed physical longitudinal projection fixes it. The separately defined Schwartz divergence and curl agree with the existing Maxwell operators. Fourier differentiation proves that actual divergence-free Schwartz vector fields lie in the projection's kernel; the existing Maxwell divergence-of-curl identity then applies to every Schwartz curl.

For arbitrary actual vector L2 fields, the transverse residual is orthogonal to every Schwartz gradient, and the longitudinal part is orthogonal to every Schwartz curl. These are exact weak-test identities, not PDE assumptions.

Validation: source compiles cleanly without warnings or errors. All 15 theorem exports were checked using `#print axioms`, each reporting exactly `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms or proof placeholders.

Independent review: hotspots checked the Fourier derivative sign, coordinate conversion, exact Maxwell operator correspondence, projection identities, and their weak-test consequences. No defect found.

Scope: no equality with a closed gradient-span projection and no Newton-potential convolution formula is asserted by this module. Those require separate arguments. The definitions and conclusions here are actual spatial derivatives and L2 fields, rather than supplied formal symbols.
