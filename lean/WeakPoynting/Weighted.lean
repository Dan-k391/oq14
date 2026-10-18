import WeakPoynting.Representative

/-!
# Weighted endpoint identities for actual weak plane flux

The integration-by-parts identity follows from the proved continuous
representative theorem and the actual distributional product rule. No
pointwise derivative of the original L1 slice is required or assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.WeightedFlux

open MeasureTheory OQ14.Maxwell OQ14.FluxSlices OQ14.FluxRepresentative Filter
open scoped Topology

/-- The product rule is derived by testing against a compact product. -/
theorem product_weak_derivative {I : Set ℝ} (χ : LineTest Set.univ) (f g : ℝ → ℝ)
    (hw : HasWeakDerivativeOn I f g) :
    HasWeakDerivativeOn I (fun x => χ.function x * f x)
      (fun x => χ.function x * g x + deriv χ.function x * f x) := by
  intro θ
  have h := hw (lineProductTest θ χ)
  convert h using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [lineProductTest_deriv]
    simp only [lineProductTest]
    ring)

/-- Exact weighted endpoint identity for a continuous representative of an L1
function whose weak derivative is the actual L1 function g. -/
theorem weak_endpoint_identity {I : Set ℝ} (hI : IsOpen I)
    (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : HasWeakDerivativeOn I f g) {a b : ℝ} (hab : a < b)
    (hsub : Set.Icc a b ⊆ I) (χ : LineTest Set.univ)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hae : f =ᵐ[volume.restrict (Set.Icc a b)] F) :
    (∫ x in a..b, deriv χ.function x * f x + χ.function x * g x) =
      χ.function b * F b - χ.function a * F a := by
  obtain ⟨hi, hj⟩ := cutoff_integrable χ f g hf hg
  obtain ⟨J, hJ, hJae, hJinc⟩ := local_continuous_representative hI _ _ hi hj
    (product_weak_derivative χ f g hw) hsub
  have heq : J =ᵐ[volume.restrict (Set.Icc a b)] (fun x => χ.function x * F x) := by
    filter_upwards [hae, hJae] with x hx hjx
    rw [← hjx, hx]
  have he := representative_unique hab hJ (χ.regular.continuous.mul hF) heq
  have hinc := hJinc a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
  rw [he ⟨hab.le, le_rfl⟩, he ⟨le_rfl, hab.le⟩] at hinc
  simpa only [add_comm] using hinc.symm

/-- The unit/zero endpoint cutoff extracts the left trace, with its sign fixed. -/
theorem left_trace_identity {I : Set ℝ} (hI : IsOpen I)
    (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : HasWeakDerivativeOn I f g) {a b : ℝ} (hab : a < b)
    (hsub : Set.Icc a b ⊆ I) (χ : LineTest Set.univ)
    (ha : χ.function a = 1) (hb : χ.function b = 0)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hae : f =ᵐ[volume.restrict (Set.Icc a b)] F) :
    F a = -(∫ x in a..b, deriv χ.function x * f x + χ.function x * g x) := by
  have h := weak_endpoint_identity hI f g hf hg hw hab hsub χ F hF hae
  rw [ha, hb, zero_mul, one_mul, zero_sub] at h
  linarith

/-- Genuine three-dimensional Fubini restricted to a finite axial slab. -/
theorem slab_coordinate_Fubini (f : Space → ℝ) (hf : Integrable f)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in axis ⁻¹' Set.Ioc a b, f x) =
      ∫ z in a..b, ∫ q : Plane, f (split.symm (z, q)) := by
  have hm : MeasurableSet (axis ⁻¹' Set.Ioc a b) :=
    measurableSet_Ioc.preimage axis.continuous.measurable
  rw [← integral_indicator hm, coordinate_Fubini _ (hf.indicator hm),
    intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    by_cases hz : z ∈ Set.Ioc a b
    · simp [Set.indicator, axis_join, hz]
    · simp [Set.indicator, axis_join, hz])

def volumeDensity (χ : LineTest Set.univ) (ψ : PlaneTest) (P : RealFlux) (x : Space) : ℝ :=
  deriv χ.function (axis x) * verticalDensity ψ P x +
    χ.function (axis x) * transverseDensity ψ P x

theorem volumeDensity_gradient (χ : LineTest Set.univ) (ψ : PlaneTest)
    (P : RealFlux) (x : Space) :
    volumeDensity χ ψ P x =
      fderiv ℝ (tensorFunction ψ χ) x (basis 0) * P x 0 +
      fderiv ℝ (tensorFunction ψ χ) x (basis 1) * P x 1 +
      fderiv ℝ (tensorFunction ψ χ) x (basis 2) * P x 2 := by
  rw [tensor_partial_zero, tensor_partial_one, tensor_partial_two]
  simp only [volumeDensity, verticalDensity, transverseDensity]
  ring

theorem volumeDensity_integrable (χ : LineTest Set.univ) (ψ : PlaneTest)
    (P : RealFlux) (hP : ∀ j, Integrable (fun x => P x j)) :
    Integrable (volumeDensity χ ψ P) :=
  (axis_weight_integrable _ (verticalDensity_integrable ψ P hP)
    _ (χ.regular.continuous_deriv le_rfl) χ.compact.deriv).add
    (axis_weight_integrable _ (transverseDensity_integrable ψ P hP)
      _ χ.regular.continuous χ.compact)

/-- Both axial and transverse-gradient terms are retained in the slab identity. -/
theorem weighted_slab_Fubini (χ : LineTest Set.univ) (ψ : PlaneTest)
    (P : RealFlux) (hP : ∀ j, Integrable (fun x => P x j))
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in axis ⁻¹' Set.Ioc a b, volumeDensity χ ψ P x) =
      ∫ z in a..b, deriv χ.function z * fluxSlice ψ P z +
        χ.function z * derivativeSlice ψ P z := by
  have hv := verticalDensity_integrable ψ P hP
  have ht := transverseDensity_integrable ψ P hP
  have hi := axis_weight_integrable _ hv _ (χ.regular.continuous_deriv le_rfl) χ.compact.deriv
  have hj := axis_weight_integrable _ ht _ χ.regular.continuous χ.compact
  have hif : Integrable (fun z => deriv χ.function z * fluxSlice ψ P z) :=
    (fluxSlice_integrable ψ P hP).bdd_mul (χ.regular.continuous_deriv le_rfl).aestronglyMeasurable
      ((χ.regular.continuous_deriv le_rfl).bounded_above_of_compact_support χ.compact.deriv)
  have hjf : Integrable (fun z => χ.function z * derivativeSlice ψ P z) :=
    (derivativeSlice_integrable ψ P hP).bdd_mul χ.regular.continuous.aestronglyMeasurable
      (χ.regular.continuous.bounded_above_of_compact_support χ.compact)
  change (∫ x in axis ⁻¹' Set.Ioc a b,
    deriv χ.function (axis x) * verticalDensity ψ P x +
      χ.function (axis x) * transverseDensity ψ P x) = _
  rw [integral_add hi.integrableOn hj.integrableOn,
    slab_coordinate_Fubini _ hi hab, slab_coordinate_Fubini _ hj hab]
  simp_rw [axis_join, integral_const_mul]
  exact (intervalIntegral.integral_add hif.intervalIntegrable hjf.intervalIntegrable).symm

/-- Canonical real diagonal plane flux, with the complete weighted volume formula,
derived directly from the actual regional weak Maxwell curl equations. -/
theorem maxwell_weighted_flux {Ω : Set Space} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (ψ : PlaneTest)
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : OQ14.DomainCurl.HCurl Ω)
    (hM : OQ14.WeakConservation.WeakMaxwell ω μ ε E H)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ I)
    (χ : LineTest Set.univ) (ha : χ.function a = 1) (hb : χ.function b = 0) :
    ∃ F : ℝ → ℝ, Continuous F ∧
      fluxSlice ψ (zeroExtendedPower Ω E H) =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      (∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, derivativeSlice ψ (zeroExtendedPower Ω E H) z) ∧
      F a = -(∫ x in axis ⁻¹' Set.Ioc a b,
        volumeDensity χ ψ (zeroExtendedPower Ω E H) x) := by
  obtain ⟨hf, hg, hw⟩ := maxwell_flux_slices hΩ ψ hbox ω μ ε E H hM
  obtain ⟨F, hF, hae, hinc⟩ := local_continuous_representative hI _ _ hf hg hw hsub
  refine ⟨F, hF, hae, hinc, ?_⟩
  rw [weighted_slab_Fubini χ ψ _ (zeroExtendedPower_integrable hΩ.measurableSet E H) hab.le]
  exact left_trace_identity hI _ _ hf hg hw hab hsub χ ha hb F hF hae

end OQ14.WeightedFlux

#print axioms OQ14.WeightedFlux.product_weak_derivative
#print axioms OQ14.WeightedFlux.weak_endpoint_identity
#print axioms OQ14.WeightedFlux.left_trace_identity
#print axioms OQ14.WeightedFlux.slab_coordinate_Fubini
#print axioms OQ14.WeightedFlux.volumeDensity_gradient
#print axioms OQ14.WeightedFlux.volumeDensity_integrable
#print axioms OQ14.WeightedFlux.weighted_slab_Fubini
#print axioms OQ14.WeightedFlux.maxwell_weighted_flux
