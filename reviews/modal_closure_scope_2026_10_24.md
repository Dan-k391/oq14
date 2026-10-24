# Modal closure scope, October 24, 2026

Author: modal Sol agent. Scoping only, from a read of the sources named below. Statements are copied from the Lean files (long ones are truncated with an ellipsis; the file name gives the rest). Nothing here is a new theorem except the one file named in the last section.

The three remaining items from the handoff are (1) actual reciprocal-residue normalization, (2) infinite-degree pole isolation, (3) simultaneous genuine three-dimensional maxima in the prescribed plane. Targets: arbitrarily high Q, fixed real pole frequency, common bounds, N-dependent insertion contrast.

## CLAIMS.md rows

- `ms:sphere-simple`: "Simple separated electric sphere poles at algebraic index, arbitrary high Q and nonzero core field. Exact Hankel polynomials, Wronskians, Lindemann--Weierstrass, Rouche. PROVED in axisymmetric electric sector" (written proof).
- `ms:normalization`, `ms:rounding`: "Genuine nonzero reciprocal residue norm and one-sided convergence of normalized rounded modes. PROVED" (written proof).
- `ms:modal-packing`, `ms:modal-volume`: "Arbitrary finite 3D peak packing in one normalized finite-device high-Q QNM ... PROVED written modal theorem; not yet Lean-formalized".
- `hs:modal-angular-branch`, `hs:modal-coefficient-continuation`: "PROVED local modal bridge" (written).

The Lean status below comes from the sources, not from these rows.

## What the Lean code already proves

All modules in this section report only standard axioms (author reviews `reviews/modal_*.md`).

### Sphere matching level (degree l, interface n, frequency z; `Amplitudes` is the interior/exterior amplitude pair)

- `ModalWronskian.hankel_wronskian (l) (z) (hz : z ≠ 0) : xi l z * xiMinusD l z - xiMinus l z * xiD l z = -2 * I`; `plus_ne_zero_at_pole (l n z) (hn) (hz) (hd : tmDet l n z = 0) : cPlus l n z ≠ 0`.
- `ModalMatching.solve_residue_limit (l n z₀) (hn : n ≠ 0) (hz : z₀ ≠ 0) (hd : tmDet l n z₀ = 0) (hs : deriv (tmDet l n) z₀ ≠ 0) (f) : Tendsto (fun z => (z - z₀) • solve l n z f) (𝓝[≠] z₀) (𝓝 (residue l n z₀ f))`; `residue_rank_one_factor`.
- `ModalMatchingNorm.residue_normalized (l n z) (hn) (hz) (hd) (f) : residue l n z f = (leftCovector l z f / leftCovector l z (matchingDerivative l n z (rightVector l n z))) • rightVector l n z`; `derivative_pairing : leftCovector l z (matchingDerivative l n z (rightVector l n z)) = deriv (tmDet l n) z`; `derivative_pairing_nonzero`; `exists_unit_derivative_pairing`; `exists_high_quality_normalized_matching_residue (l) (n : ℝ) (hn : 1 < n) (L Q) (hQ : 0 ≤ Q) : ∃ z, z ≠ 0 ∧ tmDet l (n : ℂ) z = 0 ∧ L < z.re ∧ z.im < 0 ∧ Q < z.re / (-2*z.im) ∧ ∃ a, a ≠ 0 ∧ ...`. This is the actual reciprocal normalization at the sphere-interface (matching) level: the derivative pairing equals the determinant derivative.
- `ModalAsymptotics.tm_simple_zero_strip (l) (n : ℝ) (hn : 1 < n) (ε) (hε : 0 < ε) (L) : ∃ z, z ≠ 0 ∧ tmDet l (n : ℂ) z = 0 ∧ deriv (tmDet l (n : ℂ)) z ≠ 0 ∧ L < z.re ∧ |z.im + Real.log ((n + 1) / (n - 1)) / (2 * n)| < ε`; `tm_high_quality_zeros (l) (n : ℝ) (hn : 1 < n) (L Q) (hQ : 0 ≤ Q) : ∃ z, z ≠ 0 ∧ tmDet l (n : ℂ) z = 0 ∧ deriv (tmDet l (n : ℂ)) z ≠ 0 ∧ L < z.re ∧ z.im < 0 ∧ Q < z.re / (-2 * z.im)`. These give simple high-Q zeros with no algebraicity or isolation information.
- `ModalExistence.simple_tm_zero_avoiding_finite (l) (n : ℂ) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) (S : Set ℂ) (hS : S.Finite) (L) : ∃ z, z ≠ 0 ∧ tmDet l n z = 0 ∧ deriv (tmDet l n) z ≠ 0 ∧ z ∉ S ∧ L < ‖z‖`.

### Field level (shell response; degree 1 only)

- `ModalFieldPole.response_order_minus_one (n) (k₀ : Frequency) (hn) (hd : tmDet 1 n k₀.1 = 0) (hs : deriv (tmDet 1 n) k₀.1 ≠ 0) : (response_meromorphic n k₀.1 hn k₀.property).order = (-1 : ℤ)`; `regularized_analytic`, `regularized_nonzero`; `exists_high_quality_simple_field_poles`.
- `ModalFieldResidue.responseOperator_residue_limit`, `residueOperator_nonzero`, `residueOperator_range_line (n) (k₀) : ∀ f, ∃ c, residueOperator n k₀ f = c • unitL2 k₀`; `exists_high_quality_field_residue`.
- `ModalShellAnalytic.fieldL2_analytic`, `fieldL2_ne_zero`, `fieldL2_actual`.
- `ModalPoleMode.residue_weak_maxwell`: the residue field pair (`electricMode`, `magneticMode`) satisfies the weak curl equations on all of space against compactly supported C2 test functions; also `residue_local_L2`, `residue_exterior`, `residue_shell_actual`, `residue_regional_graphs`, `exists_high_quality_residue_modes`.
- `ModalPoleRadiation.mode_electric_far_limit`, `nonzero_residue_far_field`, `exists_high_quality_radiating_residue_modes`: the same residue mode radiates.
- `ModalScaledPole.exists_prescribed_physical_shell_poles (n : ℝ) (hn : 1 < n) (k0 : ℝ) (hk0 : 0 < k0) (Q : ℝ) (hQ : 0 ≤ Q) : ∃ k : Frequency, ∃ s : ℝ, 0 < s ∧ (k.1/(s : ℂ)).re = k0 ∧ (k.1/(s : ℂ)).im < 0 ∧ Q < (k.1/(s : ℂ)).re / (-2*(k.1/(s : ℂ)).im) ∧ tmDet 1 (n : ℂ) k.1 = 0 ∧ deriv (tmDet 1 (n : ℂ)) k.1 ≠ 0 ∧ ...`, with an order-minus-one meromorphic physical response and nonzero physical residue. This is the fixed-real-pole-frequency, arbitrarily-high-Q statement at the shell-response level.

### Algebraic exceptions

- `ModalRational.finite_multiple_zeros`, `finite_common_zeros (l j n) (hlj : l ≠ j) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) : Set.Finite {z | z ≠ 0 ∧ tmDet l n z = 0 ∧ tmDet j n z = 0}`.
- `ModalAlgebraicity.common_zero_exponential_obstruction (l j n z) (hlj : l ≠ j) (hna : IsAlgebraic ℚ n) (hn) (hp) (hm) (hz) (hl : tmDet l n z = 0) (hj : tmDet j n z = 0) : IsAlgebraic ℚ (2 * I * n * z) ∧ 2 * I * n * z ≠ 0 ∧ IsAlgebraic ℚ (exp (2 * I * n * z))` and `multiple_zero_exponential_obstruction`. These give a contradiction only with the full Hermite-Lindemann theorem, which the pinned mathlib does not have (only `NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`); see `reviews/modal_algebraicity.md`.

### Volume operator level (complex frequency, compactly supported bounded coefficient c with support in the closed ball of radius R)

- `ComplexConvolutionAnalytic.volumeBlock_analyticAt`, `pencil_analyticAt`, `compactPart_compact`, `volumeBlock_factor : volumeBlock c k R = StaticNewton.volumeBlock c * pencil c k R`, `pencil_zero_isUnit`.
- `VolumeAnalyticAlternative.inverse_meromorphicOn (c R hR hc) : MeromorphicOn (fun z => Ring.inverse (volumeBlock c z R)) Set.univ`; `exceptional_discrete`; `finite_exceptional_in_bounded`; `inverse_order_negative`.
- `VolumeLaurent.finite_rank_laurent (c R hR hc z₀) : ∃ n G p, AnalyticAt ℂ G z₀ ∧ (∀ j, FiniteDimensional ℂ (LinearMap.range (p.coeff j))) ∧ ∀ᶠ z in 𝓝[≠] z₀, HasSum (fun j => ((z-z₀)^n)⁻¹ • ((z-z₀)^j • p.coeff j)) (Ring.inverse (volumeBlock c z R) - G z)`; also `CompactLaurent.finite_rank_laurent`, `AnalyticCompactInverse.inverse_meromorphicOn`, `FiniteMeromorphicInverse.inverse_order_negative`.
- `ComplexVolumeReciprocity.volumeBlock_reciprocity (c R hR k F G) : vectorPair (volumeBlock c k R F) G = vectorPair F (volumeBlock c k R G)` and `volumeBlock_deriv_reciprocity` (same for the k-derivative): the bilinear, non-conjugated pairing symmetry needed for a left functional.
- `RadialMaxwellUniqueness.volumeBlock_isUnit`, `homogeneous_fields_zero`: real k, radial layered coefficients, invertibility (a different regime from the complex-frequency pole).

### Hotspots (driven, not modal)

- `ConicalVolumePeaks.eventually_positive_physical_peaks`, `ConicalRoundedPeaks.explicit_rounded_peaks`, `ConicalFiniteIlluminationPeaks.positive_frequency_rounded_finite_peaks`: for small positive real k, rounded finite inclusions have superlevel sets of positive measure. No maxima, no common plane, no modal normalization.

Not in Lean: `hs:modal-coefficient-continuation` (analytic singular coefficient through zero contrast), the modal rounding convergence, and any statement about an actual maximum.

## Item 1: actual reciprocal-residue normalization

Done: the normalization at the matching level (`residue_normalized`, `derivative_pairing`), the actual shell residue, weak Maxwell, radiation, nonzero residue; the symmetric pairing of the volume operator and its k-derivative; meromorphy and finite-rank Laurent structure of the volume inverse.

Missing: the transfer from the sphere mode to the volume operator. Smallest missing theorem (not attempted; it needs the complex-frequency outgoing representation formula for a weak radiating solution, which is not in the code). For c equal to n^2 - 1 on the unit ball and 0 outside, n real greater than 1, `tmDet 1 (n : ℂ) k₀.1 = 0`, and R at least 1, the weighted residue mode lies in the kernel of the volume block:

`theorem weighted_mode_in_volume_kernel ... : ComplexConvolutionAnalytic.volumeBlock c k₀.1 R (weightedMode c n k₀ f) = 0`

where `weightedMode` is the L2 class of `x ↦ (Real.sqrt (c.value x) : ℂ) • ModalPoleMode.electricMode n k₀.1 f x`. After it, three more pieces are needed: kernel simplicity (kernel equals the span of the weighted mode, which needs the angular/sector decomposition of the volume operator), the identity that `vectorPair (deriv (fun z => volumeBlock c z R) k₀ u) u` equals a nonzero constant times `deriv (tmDet 1 n) k₀`, and the simple-pole residue limit. The abstract residue-form step is now supplied by `SimplePoleResidueForm.residue_form` (below).

## Item 2: infinite-degree pole isolation

Done: abstractly, the volume inverse is meromorphic on the whole plane and the exceptional set is discrete and finite on bounded sets (`VolumeAnalyticAlternative`), so every pole is isolated in the frequency plane regardless of angular degree. Per fixed degree, simple high-Q zeros exist; per fixed pair of degrees only finitely many coincidences; for algebraic n an exceptional zero would force a nonzero algebraic a with exp a algebraic.

Missing (smallest): Hermite-Lindemann, `theorem transcendental_exp_of_algebraic (a : ℂ) (ha : IsAlgebraic ℚ a) (h0 : a ≠ 0) : Transcendental ℚ (Complex.exp a)`. The pinned mathlib has only the analytic half. With it and a rational n greater than 1, the existing obstructions would give: every zero z of `tmDet 1 n` has `deriv (tmDet 1 n) z ≠ 0` and `tmDet j n z ≠ 0` for every j different from 1 (all degrees at once, since `common_zero_exponential_obstruction` is stated for arbitrary l different from j). This is not feasible in a few hours (a multi-day arithmetic proof). A genericity route avoiding transcendence (vary n, use analytic dependence of simple zeros and a countability argument) is larger. The operator-level kernel statement (all sectors, all degrees) also shares the sector-decomposition gap of item 1.

## Item 3: simultaneous 3D maxima in the prescribed plane

Done: only driven positive-measure superlevel sets (see above).

Missing: (a) the local modal coefficient continuation, (b) one-sided uniform convergence of the normalized rounded modes away from the tips (`ms:rounding`), (c) the finite assembly giving, in N disjoint small balls, strict positivity of the mode's local peak coefficient after a finite intersection of nonvanishing contrast intervals, and (d) the axisymmetric rotation step. The smallest missing statement is purely geometric and should be provable in a few hours (not attempted, ready): for an intensity F on R^3 that depends on x only through (x0^2 + x1^2, x2), a point p with p1 = 0, and eps positive, if x maximizes F over the closed ball of radius eps about p, then the point (sigma sqrt(x0^2 + x1^2), 0, x2), with sigma the sign of p0, is also a maximizer in that ball and lies in the plane x1 = 0 (the reverse triangle inequality on the planar radii shows its distance to p is not larger). Items (a) to (c) are large and not feasible in this session.

## Attempted lemma

`lean/SimplePoleResidueForm.lean` (namespace `OQ14.SimplePoleResidueForm`) proves the abstract residue-form step used by item 1, with no Maxwell content:

`theorem residue_form (A : ℂ → H →L[ℂ] H) (A1 : H →L[ℂ] H) (z0 : ℂ) (hA : HasDerivAt A A1 z0) (u : H) (φ : H →L[ℂ] ℂ) (hker : ∀ v, A z0 v=0 → ∃ a : ℂ,v=a • u) (hφ : ∀ v, φ (A z0 v)=0) (hd : φ (A1 u)≠0) (hinv : ∀ᶠ z in 𝓝[≠] z0, IsUnit (A z)) (R : H →L[ℂ] H) (hR : Tendsto (fun z => (z-z0) • Ring.inverse (A z)) (𝓝[≠] z0) (𝓝 R)) : ∀ x, R x=(φ x/φ (A1 u)) • u`

plus `residue_kills_kernel : A z0 * R=0`. The existence of the residue limit is a hypothesis; the lemma does not prove simplicity. Combined with `volumeBlock_reciprocity` (phi as the pairing against u) it will give the form minus E tensor E over the derivative pairing once the three missing pieces of item 1 are available.
