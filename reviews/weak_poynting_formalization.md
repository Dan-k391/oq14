# Weak-field Poynting formalization audit

Status: five new modules compile without warnings or errors using the existing pinned Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Their 39 selected `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no admissions or custom axioms in these sources. Existing sources, dependency pins, and repository Git state were not changed by this work.

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

This work closes the local distributional cross-product identity and diagonal real power-conservation step used inside the written `ch:fluxlemma`. It does **not** formalize that entire lemma: Hermitian off-diagonal polarization, W1,1 dependence of plane-integrated flux on the axial coordinate, the continuous representative, evaluation at a specified plane, and its weighted volume identity are still separate steps. It also does not formalize the later trace/eigenvalue/channel arguments, scattering existence, radiation conditions, Runge approximation, singular-mode excitation, resonance continuation, or the final unrestricted OQ14 claim.

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

The corresponding compiler stdout and dependency/source provenance are in `lean/WeakPoynting/verification.txt`, `provenance.json`, and the four matching `green-`, `poynting-`, `local-`, and `conservation-` evidence pairs. These are source-hash-scoped direct compilation records. The coordinator separately registers all five roots and runs the combined clean package build and qualified axiom audit. Dependency cache preparation uses only the existing lockfile; localization additionally imports `Mathlib.Geometry.Manifold.PartitionOfUnity`, already cached in this workspace.

The next substantive continuum steps are a genuine axial slicing/W1,1 theorem for an L1 distributionally divergence-free flux, followed by its canonical continuous representative and weighted volume evaluation; then the actual trace and variational/scattering foundations required by the main Maxwell problem. These should be proved as analytic statements, not packaged into an assumed physical structure.
