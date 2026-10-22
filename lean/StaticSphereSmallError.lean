import StaticSphereScale

/-! # Derived small-radius source errors for the literal parity-kernel sphere

The incident assumptions are actual local Frechet derivative and center
amplitude bounds. No source-response convergence estimate is a premise.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.StaticSphereSmallError

open MeasureTheory Metric Set StaticBallNewton StaticSphereMaterial StaticSphereScale
  StaticSphereResidual ParityReactionVolume
open scoped Topology BigOperators

def errorConstant (χ ρ k R b A M : ℝ) : ℝ :=
  6*Real.sqrt χ*Real.sqrt (volumeConstant ρ)*
    (M*ρ+linearBound χ (volumeConstant ρ) k R b*A)

theorem errorBound_scaled (p : Space) (ρ a χ R k b A M : ℝ)
    (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1) (hχ : 0 ≤ χ) (hb : b ≠ 0)
    (hM : 0 ≤ M)
    (d : SupportData (coefficient p (ρ*a) χ hχ))
    (hdR : d.radius = R) (hdK : d.carrier = ball p (ρ*a))
    (f : VectorL2) (incident : Maxwell.Field) (E : Vector)
    (hE : ∀ i, E i = incident p i) (hcenter : ∀ i : Fin 3, ‖E i‖ ≤ A/a)
    (hincident : ∀ i : Fin 3, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((coefficient p (ρ*a) χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
        incident x i)
    (hdiff : ∀ i : Fin 3, ∀ x ∈ ball p (ρ*a), DifferentiableAt ℝ (fun y => incident y i) x)
    (hder : ∀ i : Fin 3, ∀ x ∈ ball p (ρ*a), ‖fderiv ℝ (fun y => incident y i) x‖ ≤ M/a) :
    errorBound d k (b/a) f E ≤ errorConstant χ ρ k R b A M*a*Real.sqrt a := by
  let V := volumeConstant ρ
  let S := Real.sqrt V
  let K := linearBound χ V k R b
  have hV : 0 ≤ V := volumeConstant_nonnegative ρ hρ.le
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hK : 0 ≤ K := linearBound_nonnegative χ V k R b hχ hV
  have hv : volume.real d.carrier ≤ V*a^3 := by
    rw [hdK, scaled_ball_volume p ρ a hρ.le ha.le]
  have hQ : perturbationBound d k (b/a) ≤ K*a := by
    have hh := perturbation_linear d χ V k b a hχ hV ha ha1 hb le_rfl hv
    simpa only [hdR, K] using hh
  have hvar : ∀ x ∈ ball p (ρ*a), ∀ i : Fin 3, ‖incident x i-E i‖ ≤ M*ρ := by
    intro x hx i
    have hh := StaticSphereForcing.incident_variation_of_derivative p (ρ*a) (mul_pos hρ ha)
      incident (M/a) (div_nonneg hM ha.le) hdiff hder x hx i
    rw [← hE i] at hh
    apply hh.trans_eq
    field_simp
    ring
  have hF : ‖f-forcing p (ρ*a) χ E‖ ≤ (3*Real.sqrt χ*M*ρ*S)*a*Real.sqrt a := by
    have hh := StaticSphereForcing.forcing_error_bound p (ρ*a) χ hχ f incident E (M*ρ)
      hincident hvar
    rw [sqrt_scaled_ball_volume (0 : Space) ρ a hρ.le ha.le] at hh
    apply hh.trans_eq
    ring
  have hsum : (∑ i : Fin 3, ‖E i‖) ≤ 3*A/a := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hcenter i)
    exact hh.trans_eq (by simp only [Fin.sum_univ_three]; ring)
  have hT : ‖trial p (ρ*a) χ E‖ ≤ (3*Real.sqrt χ*A*S)*Real.sqrt a := by
    apply (trial_norm_bound p (ρ*a) χ hχ E).trans
    rw [sqrt_scaled_ball_volume (0 : Space) ρ a hρ.le ha.le]
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)) (by positivity)).trans_eq
    dsimp only [S]
    field_simp
    ring
  have he : errorBound d k (b/a) f E ≤
      2*((3*Real.sqrt χ*M*ρ*S)*a*Real.sqrt a + K*a*((3*Real.sqrt χ*A*S)*Real.sqrt a)) := by
    unfold errorBound
    apply mul_le_mul_of_nonneg_left (add_le_add hF _) (by norm_num : (0 : ℝ) ≤ 2)
    exact mul_le_mul hQ hT (norm_nonneg _) (mul_nonneg hK ha.le)
  apply he.trans_eq
  change _ = 6*Real.sqrt χ*S*(M*ρ+K*A)*a*Real.sqrt a
  ring

theorem source_errors_scaled (p : Space) (ρ a χ R k b A M : ℝ)
    (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1) (hχ : 0 ≤ χ) (hb : b ≠ 0)
    (hM : 0 ≤ M)
    (d : SupportData (coefficient p (ρ*a) χ hχ))
    (hdR : d.radius = R) (hdK : d.carrier = ball p (ρ*a))
    (hsmall : linearBound χ (volumeConstant ρ) k R b*a ≤ 1/2)
    (f : VectorL2) (incident : Maxwell.Field) (E : Vector)
    (hE : ∀ i, E i = incident p i) (hcenter : ∀ i : Fin 3, ‖E i‖ ≤ A/a)
    (hincident : ∀ i : Fin 3, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((coefficient p (ρ*a) χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
        incident x i)
    (hdiff : ∀ i : Fin 3, ∀ x ∈ ball p (ρ*a), DifferentiableAt ℝ (fun y => incident y i) x)
    (hder : ∀ i : Fin 3, ∀ x ∈ ball p (ρ*a), ‖fderiv ℝ (fun y => incident y i) x‖ ≤ M/a) :
    ‖ParityMaterialField.solution d k (b/a) f-trial p (ρ*a) χ E‖ ≤
        errorConstant χ ρ k R b A M*a*Real.sqrt a ∧
    ‖StaticCoefficient.sqrtMultiplier (coefficient p (ρ*a) χ hχ)
      (ParityMaterialField.solution d k (b/a) f)-
      StaticBallCentered.source p (ρ*a) (StaticSpherePolarization.polarization χ E)‖ ≤
        Real.sqrt χ*errorConstant χ ρ k R b A M*a*Real.sqrt a ∧
    ∀ i : Fin 3, (∫ x, ‖DynamicVolume.source (coefficient p (ρ*a) χ hχ)
      (ParityMaterialField.solution d k (b/a) f) i x -
      (ball p (ρ*a)).indicator (fun _ => StaticSpherePolarization.polarization χ E i) x‖) ≤
        (Real.sqrt χ*errorConstant χ ρ k R b A M*Real.sqrt (volumeConstant ρ))*a^3 := by
  have hv : volume.real d.carrier ≤ volumeConstant ρ*a^3 := by
    rw [hdK, scaled_ball_volume p ρ a hρ.le ha.le]
  have hQ : perturbationBound d k (b/a) ≤ 1/2 := by
    apply (perturbation_linear d χ (volumeConstant ρ) k b a hχ
      (volumeConstant_nonnegative ρ hρ.le) ha ha1 hb le_rfl hv).trans
    simpa only [hdR] using hsmall
  have he := errorBound_scaled p ρ a χ R k b A M hρ ha ha1 hχ hb hM d hdR hdK
    f incident E hE hcenter hincident hdiff hder
  refine ⟨(sphere_comparison p (ρ*a) (mul_pos hρ ha) χ hχ d k (b/a) hQ f E).trans he, ?_, ?_⟩
  · exact (physical_L2_error p (ρ*a) (mul_pos hρ ha) χ hχ d k (b/a) hQ f E).trans
      ((mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)).trans_eq (by ring))
  · intro i
    apply (physical_L1_error p (ρ*a) (mul_pos hρ ha) χ hχ d k (b/a) hQ f E i).trans
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).trans_eq
    rw [hdK, sqrt_scaled_ball_volume p ρ a hρ.le ha.le]
    have hs := Real.sq_sqrt ha.le
    linear_combination (Real.sqrt χ*errorConstant χ ρ k R b A M*
      Real.sqrt (volumeConstant ρ)*a^2)*hs

end OQ14.StaticSphereSmallError

#print axioms OQ14.StaticSphereSmallError.errorBound_scaled
#print axioms OQ14.StaticSphereSmallError.source_errors_scaled
