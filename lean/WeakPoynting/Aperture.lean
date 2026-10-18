import WeakPoynting.Lipschitz

/-! # Actual plane flux through compact Lipschitz apertures -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.LipschitzAperture

open MeasureTheory OQ14.Maxwell OQ14.FluxSlices OQ14.LipschitzFlux
  OQ14.FluxRepresentative Filter
open scoped Topology NNReal

structure Aperture where
  function : Plane → ℝ
  constant : ℝ≥0
  lipschitz : LipschitzWith constant function
  compact : HasCompactSupport function

def aperturePartial (ψ : Aperture) (j : Fin 2) (q : Plane) : ℝ :=
  fderiv ℝ ψ.function q (Pi.single j 1)

theorem partial_measurable (ψ : Aperture) (j : Fin 2) : Measurable (aperturePartial ψ j) :=
  measurable_fderiv_apply_const ℝ ψ.function _

theorem partial_bound (ψ : Aperture) (j : Fin 2) (q : Plane) :
    ‖aperturePartial ψ j q‖ ≤ ψ.constant * ‖(Pi.single j 1 : Plane)‖ := by
  exact ((fderiv ℝ ψ.function q).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ ψ.lipschitz) (norm_nonneg _))

theorem bounded_lipschitz_mul {X : Type*} [PseudoMetricSpace X]
    {A B M N : ℝ≥0} (f g : X → ℝ) (hf : LipschitzWith A f) (hg : LipschitzWith B g)
    (hM : ∀ x, ‖f x‖ ≤ M) (hN : ∀ x, ‖g x‖ ≤ N) :
    LipschitzWith (M * B + N * A) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  calc
    _ = ‖f x * (g x - g y) + g y * (f x - f y)‖ := by congr 1; ring
    _ ≤ ‖f x * (g x - g y)‖ + ‖g y * (f x - f y)‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ := by rw [norm_mul, norm_mul]
    _ ≤ M * (B * dist x y) + N * (A * dist x y) := by
      gcongr
      · exact hM x
      · simpa only [dist_eq_norm] using hg.dist_le_mul x y
      · exact hN y
      · simpa only [dist_eq_norm] using hf.dist_le_mul x y
    _ = _ := by push_cast; ring

def tensor {I : Set ℝ} (ψ : Aperture) (θ : LineTest I) (x : Space) : ℝ :=
  θ.function (axis x) * ψ.function (transverse x)

theorem tensor_lipschitz {I : Set ℝ} (ψ : Aperture) (θ : LineTest I) :
    ∃ C, LipschitzWith C (tensor ψ θ) := by
  obtain ⟨A, hA⟩ := θ.regular.continuous.bounded_above_of_compact_support θ.compact
  obtain ⟨B, hB⟩ := ψ.lipschitz.continuous.bounded_above_of_compact_support ψ.compact
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport θ.compact θ.regular le_rfl
  have hA' (x : Space) : ‖θ.function (axis x)‖ ≤ Real.toNNReal A :=
    (hA _).trans (Real.le_coe_toNNReal _)
  have hB' (x : Space) : ‖ψ.function (transverse x)‖ ≤ Real.toNNReal B :=
    (hB _).trans (Real.le_coe_toNNReal _)
  exact ⟨_, bounded_lipschitz_mul _ _ (hD.comp axis.lipschitz)
    (ψ.lipschitz.comp transverse.lipschitz) hA' hB'⟩

theorem tensor_compact {I : Set ℝ} (ψ : Aperture) (θ : LineTest I) :
    HasCompactSupport (tensor ψ θ) := by
  have hc : HasCompactSupport (fun p : ℝ × Plane => θ.function p.1 * ψ.function p.2) := by
    apply HasCompactSupport.of_support_subset_isCompact (θ.compact.prod ψ.compact)
    intro p hp
    have hh := mul_ne_zero_iff.mp hp
    exact ⟨subset_tsupport _ hh.1, subset_tsupport _ hh.2⟩
  exact hc.comp_homeomorph splitHomeomorph

theorem tensor_inside {I : Set ℝ} {Ω : Set Space} (ψ : Aperture) (θ : LineTest I)
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω) : tsupport (tensor ψ θ) ⊆ Ω := by
  have ha : tsupport (tensor ψ θ) ⊆ axis ⁻¹' tsupport θ.function := by
    apply closure_minimal _ (isClosed_closure.preimage axis.continuous)
    intro x hx
    exact subset_tsupport _ (mul_ne_zero_iff.mp hx).1
  have hb : tsupport (tensor ψ θ) ⊆ transverse ⁻¹' tsupport ψ.function := by
    apply closure_minimal _ (isClosed_closure.preimage transverse.continuous)
    intro x hx
    exact subset_tsupport _ (mul_ne_zero_iff.mp hx).2
  exact fun x hx => hbox ⟨θ.inside (ha hx), hb hx⟩

theorem transverse_differentiable_ae (ψ : Aperture) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ ψ.function (transverse x) := by
  have ht : Measure.QuasiMeasurePreserving transverse volume volume :=
    Measure.quasiMeasurePreserving_snd.comp split_measurePreserving.quasiMeasurePreserving
  exact ht.tendsto_ae.eventually (ψ.lipschitz.ae_differentiableAt (μ := volume))

theorem tensor_partial {I : Set ℝ} (ψ : Aperture) (θ : LineTest I) (x : Space)
    (hx : DifferentiableAt ℝ ψ.function (transverse x)) (j : Fin 3) :
    fderiv ℝ (tensor ψ θ) x (basis j) =
      deriv θ.function (axis x) * axis (basis j) * ψ.function (transverse x) +
      θ.function (axis x) * fderiv ℝ ψ.function (transverse x) (transverse (basis j)) := by
  have hθ := (θ.regular.differentiable le_rfl (axis x)).hasDerivAt.comp_hasFDerivAt x axis.hasFDerivAt
  have hψ := hx.hasFDerivAt.comp x transverse.hasFDerivAt
  have h := congrArg (fun L : Space →L[ℝ] ℝ => L (basis j)) (hθ.mul hψ).fderiv
  simpa [tensor, Function.comp_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
    add_comm] using h

def vertical (ψ : Aperture) (P : RealFlux) (x : Space) : ℝ :=
  ψ.function (transverse x) * P x 2

def lateral (ψ : Aperture) (P : RealFlux) (x : Space) : ℝ :=
  aperturePartial ψ 0 (transverse x) * P x 0 + aperturePartial ψ 1 (transverse x) * P x 1

def flux (ψ : Aperture) (P : RealFlux) (z : ℝ) : ℝ := ∫ q : Plane, vertical ψ P (split.symm (z,q))
def lateralFlux (ψ : Aperture) (P : RealFlux) (z : ℝ) : ℝ := ∫ q : Plane, lateral ψ P (split.symm (z,q))

theorem densities_integrable (ψ : Aperture) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (vertical ψ P) ∧ Integrable (lateral ψ P) := by
  have hp (j : Fin 2) (k : Fin 3) : Integrable (fun x => aperturePartial ψ j (transverse x) * P x k) :=
    (hP k).bdd_mul ((partial_measurable ψ j).comp transverse.continuous.measurable).aestronglyMeasurable
      ⟨ψ.constant * ‖(Pi.single j 1 : Plane)‖, fun x => partial_bound ψ j (transverse x)⟩
  exact ⟨transverse_weight_integrable _ (hP 2) ψ.function ψ.lipschitz.continuous ψ.compact,
    (hp 0 0).add (hp 1 1)⟩

theorem tensor_flux_ae {I : Set ℝ} (ψ : Aperture) (θ : LineTest I) (P : RealFlux) :
    gradientFlux (tensor ψ θ) P =ᵐ[volume]
      (fun x => deriv θ.function (axis x) * vertical ψ P x + θ.function (axis x) * lateral ψ P x) := by
  filter_upwards [transverse_differentiable_ae ψ] with x hx
  simp only [gradientFlux, tensor_partial ψ θ x hx, transverse_basis_zero,
    transverse_basis_one, transverse_basis_two, map_zero]
  simp [axis, basis, EuclideanSpace.single_apply, vertical, lateral, aperturePartial]
  ring

/-- Actual weak plane derivative for a compact Lipschitz aperture. -/
theorem aperture_weak_derivative {Ω : Set Space} {I : Set ℝ} (hΩ : IsOpen Ω)
    (ψ : Aperture) (P : RealFlux) (hP : ∀ j, Integrable (fun x => P x j))
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (hdiv : HasZeroDistributionalDivergence Ω P) :
    Integrable (flux ψ P) ∧ Integrable (lateralFlux ψ P) ∧
      HasWeakDerivativeOn I (flux ψ P) (lateralFlux ψ P) := by
  obtain ⟨hv, ht⟩ := densities_integrable ψ P hP
  refine ⟨slice_integrable _ hv, slice_integrable _ ht, ?_⟩
  intro θ
  obtain ⟨C, hC⟩ := tensor_lipschitz ψ θ
  have hz := (lipschitz_weak_gradient_divergence hΩ _ hC (tensor_compact ψ θ)
    (tensor_inside ψ θ hbox) P hP hdiv).2
  rw [integral_congr_ae (tensor_flux_ae ψ θ P),
    integral_add (axis_weight_integrable _ hv _ (θ.regular.continuous_deriv le_rfl) θ.compact.deriv)
      (axis_weight_integrable _ ht _ θ.regular.continuous θ.compact),
    weighted_coordinate_Fubini _ hv _ (θ.regular.continuous_deriv le_rfl) θ.compact.deriv,
    weighted_coordinate_Fubini _ ht _ θ.regular.continuous θ.compact] at hz
  have hi : Integrable (fun z => deriv θ.function z * flux ψ P z) :=
    (slice_integrable _ hv).bdd_mul (θ.regular.continuous_deriv le_rfl).aestronglyMeasurable
      ((θ.regular.continuous_deriv le_rfl).bounded_above_of_compact_support θ.compact.deriv)
  have hj : Integrable (fun z => θ.function z * lateralFlux ψ P z) :=
    (slice_integrable _ ht).bdd_mul θ.regular.continuous.aestronglyMeasurable
      (θ.regular.continuous.bounded_above_of_compact_support θ.compact)
  rw [integral_add hi hj]
  exact hz

theorem maxwell_aperture_continuous_flux {Ω : Set Space} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (ψ : Aperture)
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : OQ14.DomainCurl.HCurl Ω)
    (hM : OQ14.WeakConservation.WeakMaxwell ω μ ε E H)
    {a b : ℝ} (hsub : Set.Icc a b ⊆ I) :
    ∃ F : ℝ → ℝ, Continuous F ∧
      flux ψ (zeroExtendedPower Ω E H) =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      ∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, lateralFlux ψ (zeroExtendedPower Ω E H) z := by
  obtain ⟨hf, hg, hw⟩ := aperture_weak_derivative hΩ ψ _
    (zeroExtendedPower_integrable hΩ.measurableSet E H) hbox
    (maxwell_zeroExtendedPower_divergence hΩ ω μ ε E H hM)
  exact local_continuous_representative hI _ _ hf hg hw hsub

end OQ14.LipschitzAperture

#print axioms OQ14.LipschitzAperture.partial_measurable
#print axioms OQ14.LipschitzAperture.partial_bound
#print axioms OQ14.LipschitzAperture.tensor_lipschitz
#print axioms OQ14.LipschitzAperture.tensor_compact
#print axioms OQ14.LipschitzAperture.tensor_inside
#print axioms OQ14.LipschitzAperture.transverse_differentiable_ae
#print axioms OQ14.LipschitzAperture.tensor_partial
#print axioms OQ14.LipschitzAperture.densities_integrable
#print axioms OQ14.LipschitzAperture.tensor_flux_ae
#print axioms OQ14.LipschitzAperture.aperture_weak_derivative
#print axioms OQ14.LipschitzAperture.maxwell_aperture_continuous_flux
