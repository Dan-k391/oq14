# Removing the unit-frequency caveat of the channel branch: design note (root, October 24, 2026)

Purpose: say exactly which objects of the final counting theorem
`OQ14.RestrictedTEActualDevice.actual_counted_subspaces_device` carry the frequency, which of them need a
scaling lemma, which are invariant, and what the k-frequency theorem asserts and does not assert. Nothing here
is a claim of full OQ14 closure (the modal branch stays blocked by Hermite-Lindemann; no rate in n or r is proved).

## 1. The scaling

Maxwell's equations are scale invariant. For k > 0 and a pair (E, H) solving the k = 1 system with dielectric
eps(y), the pair E_k(x) = k E(k x), H_k(x) = k H(k x) solves the frequency-k system with dielectric
eps_k(x) = eps(k x). The amplitude factor k is a normalization choice: without it the sphere flux (power), the
plane flux through any set, and the squared far amplitude all scale by the same factor k^-2 and the
counted-subspace ratios are unchanged; with it, every one of these quantities is literally invariant, the far
amplitude e^{-ikr} r E_k(r d) -> A is the k = 1 amplitude, and the plane flux of the scaled fields through the
square of half-side L equals the k = 1 plane flux through the square of half-side k L. The k = 1 theorem is
therefore applied at half-side k * L and the fields are read back through the dilation x -> k x (direction
checked: D_L in x-coordinates is D_{kL} in y = k x).

Vocabulary already in the tree: `PuncturedMaxwellScaling.fieldAtFrequency k F x = F (k • x)`,
`ModalScaling.dilate s F x = F (s⁻¹ • x)`, `ModalScaling.dcoord_comp_smul` (chain rule for the dilation),
`ModalScaling.integral_dilate_product` (change of variables on Space), `Measure.integral_comp_smul`,
`Measure.setIntegral_comp_smul`, `Measure.quasiMeasurePreserving_smul` (Mathlib). The new modules define
`scaleField k F x := (k : ℂ) • F (k • x)` (space fields), `scaleCoeff k c` (coefficient with value
`fun ξ => c.value (k • ξ)`, same bound), and `scaleMap k E` (plane field maps, `(k : ℂ) • E x (k • ξ)`).

## 2. Where the frequency enters the frozen definitions

- `MaterialField.total c 1 u inc`, `MaterialField.scattered`, `MaterialField.solution c 1 X f`,
  `DynamicVolume.volumeBlock c 1 X`, `DynamicVolume.source c u` (no k), `StaticCoefficient.Coefficient`
  (no k: value, bound, measurability), `MaterialMaxwell.dielectric c x = 1 + c.value (coordinateMap x)` (no k),
  `MaterialMaxwell.totalMagnetic c 1 u incH`, `RestrictedTEPlaneLocal.electric A = teElectric (potential 1 A)`
  and `.magnetic`, `RestrictedTEActualCore.coreSol` (the combined L2 solution at k = 1), the shell data
  `SourcePairedInclusion.data q hq n r` (radii R, X), the device coefficient `deviceCoeff` (sphere radii
  ρ a_n, heights h a_n), the radiated mode series and the TE background: all are k = 1 objects with the literal
  argument `1`. None of them is re-instantiated at frequency k. The k-frequency fields are DEFINED as the
  amplitude-normalized dilations of the k = 1 fields.
- `MaterialMaxwell.TestMaxwell k ε E H`: the weak system with the frequency as a genuine parameter
  (tests: `DynamicSource.Test`, Schwartz functions with compact support; `fieldPair E i f = ∫ E x i * f x`;
  `curlPair A i f = A (next i) (testPartial (previous i) f) - A (previous i) (testPartial (next i) f)`). This is
  the one frozen predicate in which frequency k is meaningful, and it is the physical content of the k-frequency
  theorem.
- `RestrictedTEActualFields.fieldFlux E H x ξ = crossProduct (E x ξ) (conjugate (H x ξ)) 2` (no k),
  `RestrictedTEPassageTransfer.passage μ D F = (∫ q in D, F q ∂μ).re`, `bypass μ D F = ∫ q in Dᶜ, ‖F q‖ ∂μ`
  (no k), `RestrictedTEActualSquare.Dsq L = {|q 0| < L ∧ |q 1| < L}` (no k),
  `RestrictedTEActualCounting.IsCounted W T Pass Byp τ η δ` (compares Pass, Byp with `physicalPower` and
  `‖T a‖²`; no k).
- `RestrictedTEIncoming.physicalPower A` (limit of the inward sphere flux of the finite incoming TE field at
  k = 1, `actual_power_limit`), `RestrictedTEInput.input` (the L2 sphere amplitude), `actualScatter` /
  `ChannelScatteringMap.scatterMap` (the far amplitude `MaxwellFarField.electricAmplitude 1 (source c u)` of the
  scattered field plus the outgoing Hankel amplitude of the incident, normalized like `input`): amplitude
  objects, frequency-free as data; their physical meaning at frequency k is supplied by the power and far-field
  lemmas below.

## 3. What needs a scaling lemma (the five modules)

(FrequencyScalingMaxwell) Weak Maxwell at frequency k. `dilateTest k f : Test` with value `f (k⁻¹ • x)`
(Schwartz: `SchwartzMap.compCLM` or `compCLMOfContinuousLinearEquiv`; compact support:
`HasCompactSupport.comp_homeomorph`), `testPartial j (dilateTest k f)` has value `k⁻¹ * (testPartial j f) (k⁻¹ • x)`
(chain rule `dcoord_comp_smul`), `fieldPair (fieldAtFrequency k E) i f = k^-3 * fieldPair E i (dilateTest k f)`
(`Measure.integral_comp_smul`, finrank 3), hence
`curlPair (fieldPair (fieldAtFrequency k E)) i f = k^-2 * curlPair (fieldPair E) i (dilateTest k f)`, and
`testMaxwell_scale : 0 < k → TestMaxwell 1 ε E H → TestMaxwell k (fun x => ε (k • x)) (fieldAtFrequency k E) (fieldAtFrequency k H)`
(k^-2 * I * k^3 = I * k). With `testMaxwell_smul` (both fields multiplied by the same complex constant) the
amplitude-normalized form `TestMaxwell k (fun x => ε (k • x)) (scaleField k E) (scaleField k H)` follows.
Coefficient: `scaleCoeff k c` and `dielectric (scaleCoeff k c) x = dielectric c (k • x)`, bounds unchanged.

(FrequencyScalingFlux) Plane flux and section. `fieldFlux (scaleMap k E) (scaleMap k H) x ξ = k² * fieldFlux E H x (k • ξ)`
(conjugate of a real multiple, bilinearity of `crossProduct`), `k • Dsq L = Dsq (k * L)` and
`k • (Dsq L)ᶜ = (Dsq (k * L))ᶜ`, `passage volume (Dsq L) (fun ξ => k² * F (k • ξ)) = passage volume (Dsq (k * L)) F`
and the same for `bypass` (`Measure.setIntegral_comp_smul` on the plane, finrank 2, the factor k^-2 cancels
k²), and `isCounted_scale`: `IsCounted W T (passage through Dsq (k L) of fieldFlux E H) (bypass …) τ η δ →
IsCounted W T (passage through Dsq L of fieldFlux (scaleMap k E) (scaleMap k H)) (bypass …) τ η δ` (pointwise
rewriting; T and physicalPower untouched).

(FrequencyScalingPower) Inputs, power and far field. `radialPower n (k • e) (k • h) = k² * radialPower n e h`
for real k; the inward sphere flux of the scaled incoming TE pair at radius r equals the k = 1 flux at radius
k r, so it tends to `physicalPower A` (reindexing `actual_power_limit` along r -> k r): `physicalPower A` is
the limiting inward power of the k-frequency incident. The scaled finite TE incident pair is a vacuum weak
Maxwell pair at frequency k (`RestrictedTEMaterial.testMaxwell A` plus `testMaxwell_scale`). Far field:
if `factor 1 r • F (r • d) → A` then `factor k r • scaleField k F (r • d) → A`
(`MaxwellFarField.factor k r = r * exp(-I k r)`; `factor k r * k = factor 1 (k r)` and reindexing), so the
k-frequency far amplitude of a scaled field is the k = 1 far amplitude; instantiated with
`MaxwellFarField.electric_far_vector_limit` for the dyadic scattered field: the scaled scattered field has far
amplitude `electricAmplitude 1 ρ n` at frequency k. This is why `actualScatter` is the k-frequency scattering
map as well.

(FrequencyScalingDevice) The device. (a) `device_testMaxwell`: for the concrete doubled device, eventually in
n (the limiting effective block is a unit, `partner_limitEffective_isUnit`) and then eventually in r
(`SourcePairedReduction.eventually_combined_isUnit`, `eventually_inner_radius`), for every finite TE input x,
`TestMaxwell 1 (dielectric (pairedCoeff …)) (physE …) (physH …)` where `physE = MaterialField.total (add shell ci) 1 (coreSol x) (electric x)`,
`physH = totalMagnetic (add shell ci) 1 (coreSol x) (magnetic x)` (`PhysicalFieldIdentification.physE/physH`):
`volume_solution_testMaxwell` with support `add_support_X`, datum `isDatum_add` of the two `datum_actual`,
solution equation `Ring.mul_inverse_cancel` of the combined block, smooth incident, `RestrictedTEMaterial.testMaxwell`.
This k = 1 statement was never written down for the combined device (only for the shell alone,
`RestrictedTEBackgroundOutside.shell_testMaxwell`, and inline for abstract data in
`ChannelMaterialThroughput.material_unit_throughput`). (b) Its scaled form
`TestMaxwell k (dielectric (scaleCoeff k (pairedCoeff …))) (scaleField k physE) (scaleField k physH)`.
(c) Transport of `PhysicallyIdentified` along the dilation: pointwise clauses by substitution, almost-everywhere
clauses by `Measure.quasiMeasurePreserving_smul` and `Measure.restrict_map` (the predicate
`PhysicallyIdentifiedAt k` has the radii R_r / k, X_r / k and the region `(k • ·) ⁻¹' physRegion`).
(d) The scaled piecewise plane fields are the plane values of the scaled space fields off the circle of radius
`radius r / k` (`PhysicalDeviceFields.device_fields_physical` at the point `k • ξ`, `planePoint (k • ξ) = k • planePoint ξ`).

(RestrictedTEFrequencyScaling) The final theorem `counted_subspaces_at_frequency k hk εp hεp N η δ hη hηδ τ hτ L hL`:
the statement of `actual_counted_subspaces_device` with the device of half-side `k * L`, the coefficient
replaced by `scaleCoeff k (pairedCoeff …)` (values in [1, εp] at every point), the square `Dsq L`, the plane
fields `scaleMap k (deviceFieldsE …)`, `scaleMap k (deviceFieldsH …)`, the same orthonormal family, finrank N,
the same scattering map, the same τ η δ; conjoined with the physical clauses: eventually in n, for every x,
eventually in r, the scaled physical fields are a weak Maxwell pair at frequency k with the scaled dielectric,
they are identified with the scaled space fields (transported `PhysicallyIdentified`), and the counted plane
fields are the plane values of the scaled space fields off the circle. Proof: `actual_counted_subspaces_device`
at `k * L`, then `isCounted_scale`, `dielectric_scaleCoeff`, and the device module. Standard axioms only.

## 4. What is invariant (no lemma needed)

The dielectric bounds `q² ≤ εp`, `1 + χ ≤ εp`; the orthonormality of `input ∘ A` and the span dimension N;
the scattering map `actualScatter` and unit throughput; the thresholds τ, η, δ; the gain and shell indices and
the eventual quantifiers; the device parameters q, χ, ρ, h, R, the family A.

## 5. What is NOT asserted, and why

- The k-frequency theorem does not say that the scaled fields equal `MaterialField.total (scaleCoeff k c) k u_k inc_k`
  for some dilated L2 datum `u_k`, nor that `coreSol` dilates to the solution of the frequency-k volume block.
  That identification would need the dilation of `VectorL2`, of the square-root multiplier, of
  `DynamicVolume.volumeBlock c k X` and of `DynamicVolume.source`, plus uniqueness of the volume solution at
  frequency k; none of this is in the tree. The physical content delivered instead is the frozen weak system
  `TestMaxwell k` for the dilated fields and dilated coefficient (the same predicate the k = 1 development uses
  for its own physical fields), the vacuum system at k for the dilated incident, the invariance of the limiting
  inward power, and the invariance of the far amplitude.
- The exterior representation "scaled total = scaled incident + frequency-k dyadic integral of the scaled
  source" (which needs the kernel identity `dyadic 1 (k • z) = k^-3 • dyadic k z`) is not part of the
  deliverable; outgoingness of the scaled scattered field is recorded through the far-field limit lemma.
- The k-frequency device is the k = 1 device of half-side k L dilated by 1/k: shells of radii R_r / k,
  X_r / k, spheres of radius ρ a_n / k at height h a_n / k above the points (-L, y_l) of the square of
  half-side L (`hpoint (-(k L)) (ysq N (k L)) l = k • hpoint (-L) (ysq N L) l`); the support radius still grows
  with r. This geometric reading is stated in words, not as a Lean lemma, except through the value formula of
  `scaleCoeff`.
- All other caveats of the k = 1 statement remain: finite even-degree TE inputs, the open square up to
  parametrization, eventual statements without rates in n or r, identification in space plus continuous plane
  representatives.
