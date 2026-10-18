# Weak-field Poynting formalization audit

Status: thirteen new modules compile without warnings or errors using the existing pinned Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Their 153 selected `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no admissions or custom axioms in these sources. Existing frozen sources, dependency pins, and repository Git state were not changed by this work.

## Actual analytic content

`lean/WeakPoynting.lean` proves genuine whole-space graph-norm smoothing of every distributional H(curl) field. It uses the existing coordinate L2 equivalence classes over actual Euclidean three-space, not an abstract space assumed to admit smooth approximation. The final theorem is `OQ14.WeakPoynting.smooth_graph_approximation`: for every graph element there is a sequence of graph elements converging in the actual field/curl product norm, each represented by a globally smooth field and its actual classical curl.

The sequence is explicit convolution with normalized smooth bumps of radii `1/(n+1)` and `2/(n+1)`. Differentiation under convolution is a pinned mathlib theorem. Weak-curl commutation is proved by applying the actual weak equation to translated/reflected compact C1 kernels and checking the derivative signs. Strong L2 convergence is proved through continuity of translation in L2 and convergence of Bochner averages. The crucial identification of the average with the pointwise smooth convolution is not assumed: `kernel_test_integrable` proves absolute product-space integrability using a genuine L2 Cauchy–Schwarz estimate, `averageL2_testPair` applies Fubini, and `averageL2_ae` uses the fundamental lemma against smooth compact tests. Thus the resulting sequence consists of actual smooth representatives, with no circular density or identification hypothesis.

`lean/WeakPoynting/Green.lean` constructs a continuous bilinear L2 product pairing and proves its Lebesgue integral formula. Compact C1 scalar test products with a smooth field yield the local identity for one arbitrary weak field and one smooth graph element. The proved approximation, followed through a bounded functional, removes smoothness from the second field. `OQ14.WeakGreen.weak_local_Green` is the actual integral law

\[
\int \chi\bigl(C\cdot F-E\cdot D\bigr)
 +\nabla\chi\cdot(E\times F)=0,
\qquad C=\operatorname{curl}E,\quad D=\operatorname{curl}F.
\]

The source states this first as an expanded sum of genuine Lebesgue integrals. All products are justified by L2 pairings with bounded compact multipliers. The signs were checked independently by the coordinator.

`lean/WeakPoynting/Poynting.lean` proves conjugation preserves the actual weak curl, using conjugated compact tests and the derivative/integral conjugation rules. `OQ14.WeakPower.weak_complex_Poynting` combines the Green identity with this result. It is stated as one genuine integral:

\[
\int \chi\bigl(C\cdot\overline H-E\cdot\overline K\bigr)
 +\nabla\chi\cdot(E\times\overline H)=0.
\]

`poyntingDensity_integrable` proves integrability of this density, so the result is not vacuous because Lean defines a default value for an undefined Bochner integral.

`lean/WeakPoynting/Local.lean` removes the whole-space L2 restriction. For every open set Ω and every compact C1 scalar test with support inside Ω, `exists_interior_cutoff` constructs a smooth cutoff supported inside Ω and equal to one on a neighborhood of the test support. It uses an actual compact neighborhood and the pinned smooth Urysohn theorem. `HCurlCutoff` supplies the previously proved product-rule weak curl and zero extension. New almost-everywhere representative formulas prove that the extended field and curl agree with the original regional field and curl on the relevant support. Both the test and its derivative vanish off that support. The integral is therefore transported to Ω.

The final local result is `OQ14.LocalPower.local_weak_complex_Poynting`, with independent integrability theorem `local_poyntingDensity_integrable`. It quantifies over actual regional H(curl) elements, imposes no zero boundary condition, and requires no global L2 behavior. It does not assume a general-domain density theorem.

`lean/WeakPoynting/Conservation.lean` uses real compact C1 tests and proves the derivative formula for their complex lifts. Its `WeakMaxwell` predicate consists precisely of the two actual regional weak-curl equations almost everywhere:

\[
C=i\omega\mu(x)H,\qquad K=-i\omega\varepsilon(x)E.
\]

The coefficients are real-valued functions; they may vary or jump. No differentiability is required. The reactive term is shown pointwise to be purely imaginary before any integration. The integrable complex Poynting density then gives both `weak_real_power_integrable` and `weak_real_power_conservation`:

\[
\int_\Omega\nabla\chi\cdot\frac12\operatorname{Re}(E\times\overline H)=0.
\]

The final theorem does not need an additional boundedness or measurability hypothesis on the coefficient functions: the actual regional field and curl classes and their almost-everywhere equations are already supplied, and no separate material-energy integral is formed. Bounded measurable positive dielectric coefficients are included as a special case. This does not establish that any such coefficient admits a scattering solution.

## Coverage boundaries

This work now closes the local distributional cross-product identity, diagonal real power conservation, actual L1 plane slicing and its weak axial derivative, the unique continuous representative, and its weighted endpoint/volume formula **for compact C1 transverse apertures and compact C1 axial cutoffs**. It does **not** formalize the entire written `ch:fluxlemma`: Hermitian off-diagonal polarization is now proved as detailed below; arbitrary W1-infinity aperture/cutoff regularity remains a separate extension. It also does not formalize the later trace/eigenvalue/channel arguments, scattering existence, radiation conditions, Runge approximation, singular-mode excitation, resonance continuation, or the final unrestricted OQ14 claim.

The regional theorem is suitable for fields that are locally H(curl), by applying it where the field/curl belong to regional L2. An independent bundled H(curl)-loc space, restriction functor between regions, boundary tangential traces, and a global general-domain density theorem were not added.

## Evidence and reproduction

Direct checks were run from `D:/oq14/lean` with the portable Lean 4.19.0 compiler. The frozen source hashes are:

| Source | SHA256 |
|---|---|
| `WeakPoynting.lean` | `74b49995d65c7e6ef3722481c706d321f27e2f73ea0c9da2628ba65bfe44e102` |
| `WeakPoynting/Green.lean` | `879d621016122fcb3cad5758f2670b60d61a5191ad2539ae87cc11e99b69e3e5` |
| `WeakPoynting/Poynting.lean` | `c419f2a94d9cb0d303ad7f5642b821047e06d596a765cc4df7955c6aa0bb6a78` |
| `WeakPoynting/Local.lean` | `b15e9b8de4108e3ce597c1e228690300d2396ac13dbbb50cb0a00e106b9806dc` |
| `WeakPoynting/Conservation.lean` | `e788c2c43bae08e130810338facad3a92cadb8bd7871e1dbab5318695ccea75f` |
| `WeakPoynting/Slices.lean` | `7452cd9ff12b0072f5f7cea53bb76f134c898a1d503d2354a924bfcce52953b5` |
| `WeakPoynting/Representative.lean` | `bade5cb79e3c7f085d9d73141d9fc1ed97d0dfc1f89805a48625b8857b9a237c` |
| `WeakPoynting/Weighted.lean` | `ddfeb07dbf433fbd38a1a6bb1918e8855d9e9381af9de33e7101aca1e82f7783` |
| `WeakPoynting/Polarization.lean` | `39d9449e74baeabaa657601913ccbbc2e17bcd5aa49e9e927bb90ea79ef63740` |
| `WeakPoynting/Lipschitz.lean` | `8b4f50968e94ffb9028822fe1fc04dbeea50dc9e11afc5e5f8e6d51bcdb7ea5c` |
| `WeakPoynting/Aperture.lean` | `0a9b2cb20e09f8c862cec4a3bdb60d82d41c9f7d37d97564003c016bb4ae1c8f` |
| `WeakPoynting/Axial.lean` | `fdb3c0607e14cf468ce7263baa2e7a5adca7b7d8d37b1e167adccb65f11602fa` |
| `WeakPoynting/LipschitzBoundary.lean` | `6e1ebd950ef56ea1741e2a9f8859dc734e55c4cb8a58b716fab319e57dafc377` |

The corresponding compiler stdout and dependency/source provenance are in `lean/WeakPoynting/verification.txt`, `provenance.json`, and the eight matching `green-`, `poynting-`, `local-`, `conservation-`, `slices-`, `representative-`, `weighted-`, and `polarization-` evidence pairs. These are source-hash-scoped direct compilation records. The coordinator separately registers frozen roots and runs the combined clean package build and qualified axiom audit. Dependency cache preparation uses only the existing lockfile; localization additionally imports `Mathlib.Geometry.Manifold.PartitionOfUnity`, and the primitive proof imports `Mathlib.MeasureTheory.Integral.IntegralEqImproper`, both already cached in this workspace.

## Actual plane slices, continuous representatives, and endpoint law

`Slices.lean` uses the genuine volume-preserving measurable coordinate equivalence between Euclidean three-space and an axial real coordinate times a two-dimensional real plane. No product-volume normalization is assumed. Actual Fubini gives the plane integrals. The zero extension of the regional Poynting vector is globally L1, proved from the actual zero extensions of regional L2 field classes and L2 product integrability. Its distributional divergence is required only for tests supported inside the original open region; no unjustified conservation across the region's boundary is asserted.

For a compact C1 aperture ψ and an open axial collar I with `I × tsupport ψ` inside Ω, `maxwell_flux_slices` proves actual L1 functions

\[
f(z)=\int_{\mathbb R^2}\psi P_z,\qquad
g(z)=\int_{\mathbb R^2}\nabla_\perp\psi\cdot P_\perp
\]

and the genuine weak identity `∫ θ' f + θ g = 0` for every compact C1 test supported in I. The sign and the transverse term both follow from the explicitly proved tensor derivative rule. These are a.e. slice functions, not arbitrary evaluations of regional L2 representatives at a specified plane.

`Representative.lean` does not assume the missing Sobolev representative theorem. It first proves that a locally integrable function with zero distributional derivative is a.e. constant: convolution with a normalized smooth bump has zero classical derivative; the classical mean-value theorem makes that convolution constant; actual a.e. differentiation convergence of shrinking bumps identifies the original function with a constant. An actual L1 primitive `∫(-∞,x] g` is continuous and has exact integral increments. Its compact-test integration by parts is derived using an absolutely integrable two-variable triangular kernel and Fubini. Subtracting this primitive leaves a zero-derivative distribution.

The whole-line theorem is localized using a constructed smooth cutoff equal to one near the chosen closed interval. The distributional scalar product rule is proved by a test product, including its derivative term. No desired increment law is encoded as a hypothesis. Two continuous representatives that agree a.e. on a nondegenerate closed interval agree on its interior by positivity of Lebesgue measure on open sets and then at its endpoints by continuity. `maxwell_continuous_flux` applies all this directly to the actual regional Maxwell slices. This proves the substantive local W1,1 representative and increment content; no bundled library Sobolev type is used.

`Weighted.lean` proves the distributional product rule for χf. The continuous representative theorem applied to χf, followed by uniqueness, identifies that representative with χF. Its increment law gives

\[
\int_a^b(\chi'f+\chi g)=\chi(b)F(b)-\chi(a)F(a).
\]

This avoids an assumed a.e. fundamental theorem or a nonexistent classical derivative of f at every point. Genuine finite-slab Fubini converts the integral into the volume integral of `volumeDensity`, whose equality to `∇(χψ)·P` and integrability are separately proved. `maxwell_weighted_flux` combines the continuous representative, exact increments, and left trace

\[
F(a)=-\int_{a<z\le b}\nabla(\chi\psi)\cdot P
\]

when χ(a)=1 and χ(b)=0. The distinction between half-open and open slab endpoints does not affect a volume integral, but the formal statement currently uses the actual half-open interval. The theorem proves a canonical weighted flux value, not a tangential field trace or equality of the raw plane integral at every exceptional plane.

The actual-function Lipschitz test extension is now proved below. A bundled W1-infinity representative theorem, followed by the remaining div-curl, compactness, and variational/scattering foundations required by the main Maxwell problem, remains separate. They must be analytic proofs rather than assumed physical structures.


## Hermitian cross-input extension

`Polarization.lean` proves the actual weak Maxwell equations are closed under complex combinations of regional H(curl) states. The almost-everywhere L2 representative formulas for both fields and curls are checked explicitly; no pointwise representative linearity is presumed. For two states a and b it defines the physical vector

\[
p(a,b)=\tfrac14(E_a\times\overline H_b+\overline E_b\times H_a).
\]

The source proves diagonal agreement with the real time-average power, conjugate symmetry, additivity and complex linearity in the first input, and conjugate linearity in the second. Its actual polarization formula has the checked **+i** sign:

\[
p(a,b)=\tfrac14[Q(a+b)-Q(a-b)]+\tfrac i4[Q(a+ib)-Q(a-ib)].
\]

The formula is transported to actual regional L2 classes almost everywhere. L1 integrability is proved before splitting any integral. Diagonal Maxwell conservation and actual complex linear closure yield conservation of both components and then the single genuine complex compact-test integral in `crossFlux_conservation`.

Complex plane slices are actual two-dimensional Lebesgue integrals of the cross product. Their decomposition into component plane integrals holds almost everywhere by genuine product-space integrability and Fubini, not at every exceptional plane by definition. `maxwell_cross_flux` constructs the complex continuous representative, proves its exact subinterval increments, and derives the complete complex weighted volume identity. `complexVolumeDensity_gradient` identifies the density with the actual gradient of the tensor cutoff dotted with the cross flux. `canonical_hermitian_symmetry` uses proved uniqueness of continuous representatives to establish conjugate symmetry at every canonical plane value, including endpoints.

Normalization is c0=1; the manuscript's fixed real physical factor multiplies every flux expression. The aperture and axial cutoff remain compact C1. No scattering input map, scattering existence, general boundary trace, or W1-infinity density is assumed or proved in this module.

The pin-preserving library audit found `LipschitzWith.integral_lineDeriv_mul_eq`, `locallyIntegrable_lineDeriv`, `memLp_lineDeriv`, and `ae_differentiableAt` in `Mathlib/Analysis/Calculus/Rademacher.lean`. The four subsequent frozen modules complete this actual analytic route: commute mollification with the actual weak directional derivative using integration by parts, preserve compact interior support, prove uniform derivative bounds and a.e. convergence, then use dominated convergence against the actual L1 flux. Rademacher differentiation alone is not treated as a weak-test density theorem.

## Actual Lipschitz aperture and axial cutoff extension

`Lipschitz.lean` has 16 selected exports and proves real and Hermitian Maxwell conservation against arbitrary compact Lipschitz scalar tests supported in the open region. `Aperture.lean` has 11 selected exports and derives the actual plane weak derivative and continuous regional Maxwell flux for compact Lipschitz apertures. `Axial.lean` has eight selected exports and proves the genuine one-dimensional Lipschitz weak-test extension, multiplier product rule, and weighted endpoint law. `LipschitzBoundary.lean` has 14 selected exports and combines them into the complete actual gradient-volume identity for diagonal and Hermitian complex flux, with Lipschitz cutoffs in both directions and Hermitian symmetry at every canonical value.

The strongest direct theorem is `OQ14.LipschitzBoundary.maxwell_cross_flux_gradient`. It concludes continuity, a.e. agreement with the actual plane integral, exact subinterval increments, actual gradient-pairing integrability, and the left-trace gradient-volume formula. It starts with actual regional weak Maxwell states and actual Lipschitz functions; no smooth-density, desired endpoint, or field-trace identity is assumed. Raw plane evaluations on exceptional planes remain distinct from canonical representative values. A bundled W1-infinity equivalence-class-to-Lipschitz representative theorem is still outside the formalization.

Detailed proof and scope audits are recorded in `reviews/lipschitz_formalization.md`, `reviews/aperture_formalization.md`, `reviews/axial_formalization.md`, and `reviews/lipschitz_boundary_formalization.md`. The four additional source-scoped evidence pairs use prefixes `lipschitz-`, `aperture-`, `axial-`, and `lipschitz-boundary-`. All sources are frozen; the coordinator independently reviews and integrates them into the combined build.
