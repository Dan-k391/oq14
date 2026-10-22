import PlaneInverseCube
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Genuine plane annulus integration for inverse-distance and inverse-square kernels. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.PlaneInverseAnnulus

open MeasureTheory Metric Set PlaneInverseCube
open scoped Topology

def profile (p : ℕ) (d M t : ℝ) : ℝ := (Ioc d M).indicator (fun r => r⁻¹^p) t

theorem weighted_one (d M : ℝ) (hd : 0 < d) :
    (fun t => t*profile 1 d M t)=(Ioc d M).indicator (fun _ => (1 : ℝ)) := by
  funext t
  by_cases ht : t ∈ Ioc d M
  · have ht0 : t ≠ 0 := (hd.trans ht.1).ne'
    simp only [profile, indicator_of_mem ht, pow_one]
    exact mul_inv_cancel₀ ht0
  · simp [profile, indicator_of_not_mem ht]

theorem weighted_two (d M : ℝ) (hd : 0 < d) :
    (fun t => t*profile 2 d M t)=(Ioc d M).indicator (fun r => r⁻¹) := by
  funext t
  by_cases ht : t ∈ Ioc d M
  · have ht0 : t ≠ 0 := (hd.trans ht.1).ne'
    simp only [profile, indicator_of_mem ht]
    field_simp
    ring
  · simp [profile, indicator_of_not_mem ht]

theorem inverse_integrableOn (d M : ℝ) (hd : 0 < d) :
    IntegrableOn (fun r : ℝ => r⁻¹) (Ioc d M) := by
  have hc : ContinuousOn (fun r : ℝ => r⁻¹) (Icc d M) := by
    intro r hr
    exact (continuousAt_inv₀ (hd.trans_le hr.1).ne').continuousWithinAt
  exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

theorem profile_one_integrable (d M : ℝ) (hd : 0 < d) :
    Integrable (fun q : Plane => profile 1 d M ‖q‖) := by
  apply integrable_norm_of_radial
  rw [weighted_one d M hd]
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr
    (integrableOn_const.mpr (Or.inr measure_Ioc_lt_top))).integrableOn

theorem profile_two_integrable (d M : ℝ) (hd : 0 < d) :
    Integrable (fun q : Plane => profile 2 d M ‖q‖) := by
  apply integrable_norm_of_radial
  rw [weighted_two d M hd]
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr (inverse_integrableOn d M hd)).integrableOn

private theorem radial_formula (p : ℕ) (d M : ℝ) (hd : 0 < d) :
    (∫ q : Plane, profile p d M ‖q‖)=diskConstant*(∫ t : ℝ, t*profile p d M t) := by
  have he := integral_fun_norm_addHaar (μ := (volume : Measure Plane)) (profile p d M)
  have hdim : Module.finrank ℝ Plane=2 := by simp [Plane]
  rw [hdim] at he
  simp only [Nat.reduceSub, pow_one, nsmul_eq_mul, smul_eq_mul] at he
  have hr : (∫ t : ℝ in Ioi 0, t*profile p d M t)=(∫ t : ℝ, t*profile p d M t) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hn : t ∉ Ioc d M := by
      intro hm
      have ht0 : 0 < t := hd.trans hm.1
      exact ht ht0
    simp [profile, indicator_of_not_mem hn]
  rw [hr] at he
  exact he.trans (by unfold diskConstant; ring)

theorem profile_one_integral (d M : ℝ) (hd : 0 < d) (hdM : d ≤ M) :
    (∫ q : Plane, profile 1 d M ‖q‖)=diskConstant*(M-d) := by
  rw [radial_formula 1 d M hd, weighted_one d M hd, integral_indicator measurableSet_Ioc]
  have hi := integral_one (a := d) (b := M)
  rw [intervalIntegral.integral_of_le hdM] at hi
  rw [hi]

theorem profile_two_integral (d M : ℝ) (hd : 0 < d) (hdM : d ≤ M) :
    (∫ q : Plane, profile 2 d M ‖q‖)=diskConstant*Real.log (M/d) := by
  rw [radial_formula 2 d M hd, weighted_two d M hd, integral_indicator measurableSet_Ioc]
  have hi := integral_inv_of_pos hd (hd.trans_le hdM)
  rw [intervalIntegral.integral_of_le hdM] at hi
  rw [hi]

end OQ14.PlaneInverseAnnulus

#print axioms OQ14.PlaneInverseAnnulus.weighted_one
#print axioms OQ14.PlaneInverseAnnulus.weighted_two
#print axioms OQ14.PlaneInverseAnnulus.inverse_integrableOn
#print axioms OQ14.PlaneInverseAnnulus.profile_one_integrable
#print axioms OQ14.PlaneInverseAnnulus.profile_two_integrable
#print axioms OQ14.PlaneInverseAnnulus.profile_one_integral
#print axioms OQ14.PlaneInverseAnnulus.profile_two_integral
