import SphereWaveCalculus

/-! Genuine Frechet and coordinate derivatives through density integrals under actual uniform differential bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.DensityDerivatives
open MeasureTheory Metric Set
open scoped Topology
abbrev Space := FourierL2.Space

theorem differential_integrable (K : Space → Space → ℂ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (x : Space) (hc : Continuous (fun y => fderiv ℝ (fun z => K z y) x))
    (D : ℝ) (hb : ∀ y, ‖fderiv ℝ (fun z => K z y) x‖ ≤ D) :
    Integrable (fun y => ρ y • fderiv ℝ (fun z => K z y) x) := by
  apply (hρ.norm.mul_const D).mono' (hρ.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  filter_upwards with y
  exact ((fderiv ℝ (fun z => K z y) x).opNorm_smul_le (ρ y)).trans
    (mul_le_mul_of_nonneg_left (hb y) (norm_nonneg _))

theorem hasFDerivAt (K : Space → Space → ℂ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hd : ∀ x y, DifferentiableAt ℝ (fun z => K z y) x)
    (hc : ∀ x, Continuous (fun y => fderiv ℝ (fun z => K z y) x))
    (D : ℝ) (hb : ∀ x y, ‖fderiv ℝ (fun z => K z y) x‖ ≤ D)
    (hi : ∀ x, Integrable (fun y => K x y*ρ y)) (x : Space) :
    HasFDerivAt (fun z => ∫ y, K z y*ρ y)
      (∫ y, ρ y • fderiv ℝ (fun z => K z y) x) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y => K z y*ρ y) (F' := fun z y => ρ y • fderiv ℝ (fun z => K z y) z)
    (ε := 1) (bound := fun y => ‖ρ y‖*D) (by norm_num)
  · filter_upwards with z
    exact (hi z).aestronglyMeasurable
  · exact hi x
  · exact hρ.aestronglyMeasurable.smul (hc x).aestronglyMeasurable
  · filter_upwards with y z _
    exact ((fderiv ℝ (fun u => K u y) z).opNorm_smul_le (ρ y)).trans
      (mul_le_mul_of_nonneg_left (hb z y) (norm_nonneg _))
  · exact hρ.norm.mul_const D
  · filter_upwards with y z _
    simpa only [mul_comm] using (hd z y).hasFDerivAt.const_mul (ρ y)

theorem partial_integrable (K : Space → Space → ℂ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (x : Space) (hc : Continuous (fun y => fderiv ℝ (fun z => K z y) x))
    (D : ℝ) (hb : ∀ y, ‖fderiv ℝ (fun z => K z y) x‖ ≤ D) (a : Fin 3) :
    Integrable (fun y => ρ y*Maxwell.dcoord (fun z => K z y) x a) := by
  have hi := (ContinuousLinearMap.apply ℝ ℂ (Maxwell.basis a)).integrable_comp
    (differential_integrable K ρ hρ x hc D hb)
  simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul,Maxwell.dcoord] using hi

theorem coordinate_derivative (K : Space → Space → ℂ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hd : ∀ x y, DifferentiableAt ℝ (fun z => K z y) x)
    (hc : ∀ x, Continuous (fun y => fderiv ℝ (fun z => K z y) x))
    (D : ℝ) (hb : ∀ x y, ‖fderiv ℝ (fun z => K z y) x‖ ≤ D)
    (hi : ∀ x, Integrable (fun y => K x y*ρ y)) (x : Space) (a : Fin 3) :
    Maxwell.dcoord (fun z => ∫ y, K z y*ρ y) x a=
      ∫ y, ρ y*Maxwell.dcoord (fun z => K z y) x a := by
  rw [Maxwell.dcoord,(hasFDerivAt K ρ hρ hd hc D hb hi x).fderiv,
    ContinuousLinearMap.integral_apply (differential_integrable K ρ hρ x (hc x) D (hb x))]
  apply integral_congr_ae
  filter_upwards with y
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,Maxwell.dcoord]

end OQ14.DensityDerivatives
#print axioms OQ14.DensityDerivatives.differential_integrable
#print axioms OQ14.DensityDerivatives.hasFDerivAt
#print axioms OQ14.DensityDerivatives.partial_integrable
#print axioms OQ14.DensityDerivatives.coordinate_derivative
