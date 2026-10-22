import FiniteSphereScale

/-! # Derived finite-sphere source errors for the actual parity-kernel inverse -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.FiniteSphereSmallError

open MeasureTheory Metric Set StaticBallNewton FiniteSphereStatic FiniteSphereResidualBound
  StaticSphereScale ParityReactionVolume
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def errorConstant (χ ρ δ k R b A M : ℝ) : ℝ :=
  2*(3*Real.sqrt χ*M*ρ*Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ) +
    3*Real.sqrt χ*FiniteSphereScale.interactionConstant (ι := ι) χ ρ δ A*
      Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ) +
    linearBound χ (FiniteSphereScale.totalVolume (ι := ι) ρ) k R b*
      FiniteSphereScale.trialConstant (ι := ι) χ ρ A)

theorem weighted_error_scaled (p : ι → Space) (ρ a χ δ R k b A M : ℝ)
    (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1) (hχ : 0 ≤ χ) (hδ : 0 < δ)
    (hb : b ≠ 0) (hA : 0 ≤ A) (hM : 0 ≤ M) (hrad : ρ*a ≤ δ/4)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (p i) (p j))
    (hinside : ∀ j, ‖p j‖+ρ*a ≤ R)
    (d : BoundedMaterialKernel.SupportData (coefficient p (fun _ => ρ*a) χ hχ))
    (hdR : d.radius = R) (hdK : d.carrier = ⋃ j, ball (p j) (ρ*a))
    (hsmall : linearBound χ (FiniteSphereScale.totalVolume (ι := ι) ρ) k R b*a ≤ 1/2)
    (f : VectorL2) (incident : Maxwell.Field) (E : ι → Vector)
    (hE : ∀ j m, E j m = incident (p j) m) (hcenter : ∀ j m, ‖E j m‖ ≤ A/a)
    (hincident : ∀ m : Fin 3, (fun x => f (VectorFourier.coordinateMap x) m) =ᵐ[volume]
      fun x => (Real.sqrt ((coefficient p (fun _ => ρ*a) χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
        incident x m)
    (hdiff : ∀ j m, ∀ x ∈ ball (p j) (ρ*a), DifferentiableAt ℝ (fun y => incident y m) x)
    (hder : ∀ j m, ∀ x ∈ ball (p j) (ρ*a), ‖fderiv ℝ (fun y => incident y m) x‖ ≤ M/a) :
    ‖ParityMaterialField.solution d k (b/a) f-trial p (fun _ => ρ*a) χ E‖ ≤
      errorConstant (ι := ι) χ ρ δ k R b A M*a*Real.sqrt a := by
  let V := FiniteSphereScale.totalVolume (ι := ι) ρ
  let S := Real.sqrt V
  let K := linearBound χ V k R b
  let T := FiniteSphereScale.trialConstant (ι := ι) χ ρ A
  let D := FiniteSphereScale.interactionConstant (ι := ι) χ ρ δ A
  have hV : 0 ≤ V := FiniteSphereScale.totalVolume_nonnegative ρ hρ.le
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hK : 0 ≤ K := linearBound_nonnegative χ V k R b hχ hV
  have hD : 0 ≤ D := by unfold D FiniteSphereScale.interactionConstant; positivity
  have hvol : Real.sqrt (volume.real (⋃ j, ball (p j) (ρ*a))) ≤ S*a*Real.sqrt a :=
    FiniteSphereScale.sqrt_union_volume_bound p ρ a hρ.le ha.le
  have hv : volume.real d.carrier ≤ V*a^3 := by
    rw [hdK]
    exact FiniteSphereScale.union_volume_bound p ρ a hρ.le ha.le
  have hQ : perturbationBound d k (b/a) ≤ K*a := by
    have hh := perturbation_linear d χ V k b a hχ hV ha ha1 hb le_rfl hv
    simpa only [hdR, K] using hh
  have hQsmall : perturbationBound d k (b/a) ≤ 1/2 := hQ.trans hsmall
  have hdis : ∀ i j, i ≠ j → (ρ*a)+(ρ*a) ≤ dist (p i) (p j) := by
    intro i j hij
    linarith [hsep i j hij]
  have hvar : ∀ j, ∀ x ∈ ball (p j) (ρ*a), ∀ m : Fin 3, ‖incident x m-E j m‖ ≤ M*ρ := by
    intro j x hx m
    have hh := StaticSphereForcing.incident_variation_of_derivative (p j) (ρ*a) (mul_pos hρ ha)
      incident (M/a) (div_nonneg hM ha.le) (hdiff j) (hder j) x hx m
    rw [← hE j m] at hh
    apply hh.trans_eq
    field_simp
    ring
  have hF : ‖f-forcing p (fun _ => ρ*a) χ E‖ ≤ (3*Real.sqrt χ*M*ρ*S)*a*Real.sqrt a := by
    apply (FiniteSphereComparison.forcing_error_bound p (fun _ => ρ*a) χ hχ E R hinside hdis
      f incident (M*ρ) hincident hvar).trans
    apply (mul_le_mul_of_nonneg_left hvol (by positivity : 0 ≤ 3*Real.sqrt χ*(M*ρ))).trans_eq
    ring
  have hT : ‖trial p (fun _ => ρ*a) χ E‖ ≤ T*Real.sqrt a :=
    FiniteSphereScale.trial_scaled p ρ a χ A hρ.le ha hχ E hcenter
  have hI : interactionBound (fun _ : ι => ρ*a)
      (fun j => StaticSpherePolarization.polarization χ (E j)) δ ≤ D*a^2 :=
    FiniteSphereScale.interaction_scaled ρ a χ δ A hρ.le ha hχ hδ E hcenter
  have hR : (3*Real.sqrt χ*interactionBound (fun _ : ι => ρ*a)
      (fun j => StaticSpherePolarization.polarization χ (E j)) δ)*
        Real.sqrt (volume.real (⋃ j, ball (p j) (ρ*a))) ≤ (3*Real.sqrt χ*D*S)*a*Real.sqrt a := by
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ 3*Real.sqrt χ))
      hvol (Real.sqrt_nonneg _) (by positivity : 0 ≤ 3*Real.sqrt χ*(D*a^2))).trans
    have ha3 : a^3 ≤ a := by
      have hh := mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
      have hh' := mul_le_mul_of_nonneg_left ha1 ha.le
      nlinarith
    calc
      _ = (3*Real.sqrt χ*D*S)*a^3*Real.sqrt a := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha3 (by positivity : 0 ≤ 3*Real.sqrt χ*D*S)) (Real.sqrt_nonneg _)
  apply (FiniteSphereComparison.parity_comparison p (fun _ => ρ*a) χ hχ E δ hδ
    (fun _ => mul_pos hρ ha) (fun _ => hrad) hsep R hinside d k (b/a) hQsmall f).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hF hR)
    (mul_le_mul hQ hT (norm_nonneg _) (mul_nonneg hK ha.le))) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  change _ = 2*(3*Real.sqrt χ*M*ρ*S+3*Real.sqrt χ*D*S+K*T)*a*Real.sqrt a
  ring

theorem trial_source_ae (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : ι → Vector) (m : Fin 3) :
    DynamicVolume.source (coefficient p r χ hχ) (trial p r χ E) m =ᵐ[volume]
      fun x => ∑ j : ι, (ball (p j) (r j)).indicator
        (fun _ => StaticSpherePolarization.polarization χ (E j) m) x := by
  have hp := StaticNewton.material_source_ae (coefficient p r χ hχ) (trial p r χ E) m
  rw [physical_trial p r χ hχ E] at hp
  exact hp.symm.trans ((NewtonL2.physicalCoordinate_ae _ m).trans
    (sumSource_ae p r (fun j => StaticSpherePolarization.polarization χ (E j)) m))

theorem physical_errors_of_weighted (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : ι → Vector) (d : BoundedMaterialKernel.SupportData (coefficient p r χ hχ))
    (u : VectorL2) (e : ℝ) (he : ‖u-trial p r χ E‖ ≤ e) :
    ‖StaticCoefficient.sqrtMultiplier (coefficient p r χ hχ) u-
      sumSource p r (fun j => StaticSpherePolarization.polarization χ (E j))‖ ≤ Real.sqrt χ*e ∧
    ∀ m : Fin 3, (∫ x, ‖DynamicVolume.source (coefficient p r χ hχ) u m x-
      ∑ j : ι, (ball (p j) (r j)).indicator (fun _ => StaticSpherePolarization.polarization χ (E j) m) x‖) ≤
        (Real.sqrt χ*e)*Real.sqrt (volume.real d.carrier) := by
  refine ⟨?_, ?_⟩
  · rw [← physical_trial p r χ hχ E, ← map_sub]
    exact (StaticCoefficient.applySqrt_norm _ _).trans (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _))
  · intro m
    let v := trial p r χ E
    have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_sub u v)
    have ht : (∫ x, ‖DynamicVolume.source (coefficient p r χ hχ) u m x-
        ∑ j : ι, (ball (p j) (r j)).indicator (fun _ => StaticSpherePolarization.polarization χ (E j) m) x‖) =
        ∫ x, ‖DynamicConvolution.component m (StaticCoefficient.sqrtMultiplier (coefficient p r χ hχ) (u-v)) x‖ := by
      apply integral_congr_ae
      filter_upwards [hs, trial_source_ae p r χ hχ E m,
        StaticNewton.material_source_ae (coefficient p r χ hχ) (u-v) m] with x hs hv hp
      rw [DynamicConvolution.component_apply, hp, ← hv]
      unfold DynamicVolume.source
      rw [hs]
      simp only [Pi.sub_apply, PiLp.sub_apply (p := (2 : ENNReal)), mul_sub]
      rfl
    rw [ht]
    exact (BoundedMaterialKernel.source_mass d (u-v) m).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

end OQ14.FiniteSphereSmallError

#print axioms OQ14.FiniteSphereSmallError.weighted_error_scaled
#print axioms OQ14.FiniteSphereSmallError.trial_source_ae
#print axioms OQ14.FiniteSphereSmallError.physical_errors_of_weighted
