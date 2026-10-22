import FiniteSpherePlaneSources

/-! Actual finite-ball trial and inverse source L1 masses scale as a squared. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereSourceMass
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open FiniteSpherePlaneSources (trialSource)
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def trialConstant (χ ρ A : ℝ) : ℝ := 3*FiniteSphereScale.totalVolume (ι := ι) ρ*χ*A

private theorem indicator_mass (p : Space) (r : ℝ) (z : ℂ) :
    (∫ x : Space, ‖(ball p r).indicator (fun _ => z) x‖)=volume.real (ball p r)*‖z‖ := by
  have he : (fun x : Space => ‖(ball p r).indicator (fun _ => z) x‖)=
      (ball p r).indicator (fun _ => ‖z‖) := by ext x; by_cases hx : x ∈ ball p r <;> simp [hx]
  rw [he,integral_indicator_const _ measurableSet_ball]
  rfl

omit [DecidableEq ι] in
theorem trial_mass (p : ι → Space) (ρ a χ A : ℝ) (hρ : 0 ≤ ρ) (ha : 0 < a) (hχ : 0 ≤ χ)
    (E : ι → Vector) (hE : ∀ l j, ‖E l j‖ ≤ A/a) :
    sourceMass (trialSource p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l))) ≤
      trialConstant (ι := ι) χ ρ A*a^2 := by
  have hc (j : Fin 3) :
      (∫ x : Space, ‖trialSource p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l)) j x‖) ≤
      (FiniteSphereScale.totalVolume (ι := ι) ρ*χ*A)*a^2 := by
    have hi (l : ι) := StaticBallDipole.indicator_integrable (p l) (ρ*a) (StaticSpherePolarization.polarization χ (E l) j)
    calc
      _ ≤ ∫ x : Space, ∑ l : ι, ‖(ball (p l) (ρ*a)).indicator (fun _ => StaticSpherePolarization.polarization χ (E l) j) x‖ :=
        integral_mono_ae (integrable_finset_sum Finset.univ (fun l _ => hi l)).norm
          (integrable_finset_sum Finset.univ (fun l _ => (hi l).norm)) (Filter.Eventually.of_forall (fun x => norm_sum_le _ _))
      _ = ∑ l : ι, volume.real (ball (p l) (ρ*a))*‖StaticSpherePolarization.polarization χ (E l) j‖ := by
        rw [integral_finset_sum _ (fun l _ => (hi l).norm)]
        exact Finset.sum_congr rfl (fun l _ => indicator_mass _ _ _)
      _ ≤ ∑ l : ι, volume.real (ball (p l) (ρ*a))*(χ*(A/a)) :=
        Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left
          ((FiniteSphereScale.polarization_component_bound χ hχ (E l) j).trans
            (mul_le_mul_of_nonneg_left (hE l j) hχ)) measureReal_nonneg)
      _ = _ := by
        simp only [StaticSphereScale.scaled_ball_volume _ ρ a hρ ha.le,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        unfold FiniteSphereScale.totalVolume
        field_simp
        ring
  apply (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hc j)).trans_eq
  rw [Fin.sum_univ_three]
  unfold trialConstant
  ring

theorem inverse_mass (p : ι → Space) (ρ a χ δ R k b A M : ℝ) (hρ : 0 ≤ ρ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorFourier.VectorL2) (E : ι → Vector) (hE : ∀ l j, ‖E l j‖ ≤ A/a)
    (he : FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b A M hχ d f E) :
    sourceMass (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
      (ParityMaterialField.solution d k (b/a) f)) ≤
      (trialConstant (ι := ι) χ ρ A+|FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M|)*a^2 := by
  let u := ParityMaterialField.solution d k (b/a) f
  let S := trialSource p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l))
  have hs (j : Fin 3) : Integrable (S j) :=
    (FiniteSphereReaction.source_integrable p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l)) j).congr
      (FiniteSphereStatic.sumSource_ae p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l)) j)
  have hi := DynamicVolume.source_integrable _ u d.radius d.ballZero
  have hm := FiniteSpherePlaneSources.inverse_source_mass p ρ a χ δ R k b A M hχ d f E he
  calc
    _ ≤ sourceMass (DynamicVolume.source _ u-S)+sourceMass S := sourceMass_le_sub_add _ S hi hs
    _ ≤ FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M*a^3+
      trialConstant (ι := ι) χ ρ A*a^2 := add_le_add hm (trial_mass p ρ a χ A hρ ha hχ E hE)
    _ ≤ |FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M| *a^3+
      trialConstant (ι := ι) χ ρ A*a^2 := add_le_add_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) _
    _ ≤ |FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M| *a^2+
      trialConstant (ι := ι) χ ρ A*a^2 := add_le_add_right
        (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg a] : a^3 ≤ a^2) (abs_nonneg _)) _
    _ = _ := by ring

end OQ14.FiniteSphereSourceMass
#print axioms OQ14.FiniteSphereSourceMass.trial_mass
#print axioms OQ14.FiniteSphereSourceMass.inverse_mass
