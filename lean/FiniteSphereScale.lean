import FiniteSphereComparison

/-! # Actual volume and interaction powers for finite shrinking sphere trials -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.FiniteSphereScale

open MeasureTheory Metric Set StaticBallNewton FiniteSphereStatic FiniteSphereResidualBound
  StaticSphereScale
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι]

def totalVolume (ρ : ℝ) : ℝ := (Fintype.card ι : ℝ)*volumeConstant ρ

def trialConstant (χ ρ A : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)*(3*Real.sqrt χ*A*Real.sqrt (volumeConstant ρ))

def interactionConstant (χ ρ δ A : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)*((4/3 : ℝ)*(ρ^3/(δ/2)^3))*(3*χ*A)

theorem totalVolume_nonnegative (ρ : ℝ) (hρ : 0 ≤ ρ) : 0 ≤ totalVolume (ι := ι) ρ := by
  unfold totalVolume
  exact mul_nonneg (Nat.cast_nonneg _) (volumeConstant_nonnegative ρ hρ)

theorem union_volume_bound (p : ι → Space) (ρ a : ℝ) (hρ : 0 ≤ ρ) (ha : 0 ≤ a) :
    volume.real (⋃ j : ι, ball (p j) (ρ*a)) ≤ totalVolume (ι := ι) ρ*a^3 := by
  apply (DynamicSupportVolume.finite_ball_volume p (fun _ => ρ*a)
    (fun _ => mul_nonneg hρ ha)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, totalVolume, volumeConstant]
  ring

theorem sqrt_union_volume_bound (p : ι → Space) (ρ a : ℝ) (hρ : 0 ≤ ρ) (ha : 0 ≤ a) :
    Real.sqrt (volume.real (⋃ j : ι, ball (p j) (ρ*a))) ≤
      Real.sqrt (totalVolume (ι := ι) ρ)*a*Real.sqrt a := by
  apply (Real.sqrt_le_sqrt (union_volume_bound p ρ a hρ ha)).trans_eq
  rw [Real.sqrt_mul (totalVolume_nonnegative ρ hρ), show a^3=a^2*a by ring,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  ring

theorem polarization_component_bound (χ : ℝ) (hχ : 0 ≤ χ) (E : Vector) (m : Fin 3) :
    ‖StaticSpherePolarization.polarization χ E m‖ ≤ χ*‖E m‖ := by
  have hc : 0 ≤ 3*χ/(χ+3) := by positivity
  change ‖((3*χ/(χ+3) : ℝ) : ℂ)*E m‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ (by linarith : 0 < χ+3)).mpr
  nlinarith [sq_nonneg χ]

theorem trial_scaled (p : ι → Space) (ρ a χ A : ℝ) (hρ : 0 ≤ ρ) (ha : 0 < a)
    (hχ : 0 ≤ χ) (E : ι → Vector) (hE : ∀ j m, ‖E j m‖ ≤ A/a) :
    ‖trial p (fun _ => ρ*a) χ E‖ ≤ trialConstant (ι := ι) χ ρ A*Real.sqrt a := by
  apply (FiniteSphereComparison.trial_norm_bound p (fun _ => ρ*a) χ hχ E).trans
  have hs : ∀ j : ι, (∑ m : Fin 3, ‖E j m‖) ≤ 3*A/a := by
    intro j
    exact (Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin 3))) => hE j m)).trans_eq
      (by simp only [Fin.sum_univ_three]; ring)
  apply (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs j) (Real.sqrt_nonneg χ))
      (Real.sqrt_nonneg (volume.real (ball (0 : Space) (ρ*a)))))).trans_eq
  rw [sqrt_scaled_ball_volume (0 : Space) ρ a hρ ha.le]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, trialConstant]
  field_simp
  ring

theorem interaction_scaled (ρ a χ δ A : ℝ) (hρ : 0 ≤ ρ) (ha : 0 < a)
    (hχ : 0 ≤ χ) (hδ : 0 < δ) (E : ι → Vector) (hE : ∀ j m, ‖E j m‖ ≤ A/a) :
    interactionBound (fun _ : ι => ρ*a) (fun j => StaticSpherePolarization.polarization χ (E j)) δ ≤
      interactionConstant (ι := ι) χ ρ δ A*a^2 := by
  have hs : ∀ j : ι, (∑ m : Fin 3, ‖StaticSpherePolarization.polarization χ (E j) m‖) ≤ 3*χ*A/a := by
    intro j
    have hh : ∀ m : Fin 3, ‖StaticSpherePolarization.polarization χ (E j) m‖ ≤ χ*(A/a) :=
      fun m => (polarization_component_bound χ hχ (E j) m).trans
        (mul_le_mul_of_nonneg_left (hE j m) hχ)
    exact (Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin 3))) => hh m)).trans_eq
      (by simp only [Fin.sum_univ_three]; ring)
  unfold interactionBound
  apply (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (hs j) (by positivity : 0 ≤ (4/3 : ℝ)*((ρ*a)^3/(δ/2)^3)))).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, interactionConstant]
  field_simp
  ring

end OQ14.FiniteSphereScale

#print axioms OQ14.FiniteSphereScale.totalVolume_nonnegative
#print axioms OQ14.FiniteSphereScale.union_volume_bound
#print axioms OQ14.FiniteSphereScale.sqrt_union_volume_bound
#print axioms OQ14.FiniteSphereScale.polarization_component_bound
#print axioms OQ14.FiniteSphereScale.trial_scaled
#print axioms OQ14.FiniteSphereScale.interaction_scaled
