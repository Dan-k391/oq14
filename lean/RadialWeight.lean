import RadialPowerTest
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
The actual nonnegative compact radial weight from the smooth primitive test,
its strictly positive half-line integral, and exact Lebesgue radius scaling.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OQ14.RadialWeight
open MeasureTheory Metric Set OQ14.RadialPowerTest

def weight (r : ℝ) : ℝ := 2*r*beta (r^2)

theorem weight_continuous : Continuous weight :=
  (continuous_const.mul continuous_id).mul (beta_regular.continuous.comp (continuous_id.pow 2))

theorem weight_nonnegative (r : ℝ) (hr : 0 < r) : 0 ≤ weight r :=
  mul_nonneg (by positivity) (beta_nonnegative _)

theorem weight_zero_left (r : ℝ) (hr : 0 ≤ r) (h1 : r ≤ 1) : weight r = 0 := by
  have hq : r^2 ≤ 1 := by nlinarith
  simp only [weight, beta_zero_left _ hq, mul_zero]

theorem weight_zero_right (r : ℝ) (hr : 2 ≤ r) : weight r = 0 := by
  have hq : 3 ≤ r^2 := by nlinarith
  simp only [weight, beta_zero_right _ hq, mul_zero]

theorem weight_supported_Ioi (r : ℝ) (hr : 0 < r) (hn : r ∉ Icc (1 : ℝ) 2) :
    weight r = 0 := by
  by_cases h1 : r ≤ 1
  · exact weight_zero_left r hr.le h1
  · have h2 : 2 ≤ r := by
      by_contra h
      exact hn ⟨(lt_of_not_ge h1).le, (lt_of_not_ge h).le⟩
    exact weight_zero_right r h2

theorem weight_compact : HasCompactSupport weight := by
  apply (isCompact_closedBall (0 : ℝ) 2).of_isClosed_subset (isClosed_tsupport weight)
  apply closure_minimal _ isClosed_closedBall
  intro r hr
  by_contra hn
  have hab : 2 < |r| := by simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    not_le] using hn
  have hq : 3 ≤ r^2 := by nlinarith [sq_abs r]
  exact hr (by simp only [weight, beta_zero_right _ hq, mul_zero])

theorem weight_integrable : Integrable weight :=
  weight_continuous.integrable_of_hasCompactSupport weight_compact

theorem weight_integrableOn : IntegrableOn weight (Ioi (0 : ℝ)) :=
  weight_integrable.integrableOn

theorem beta_integral_Ioi : (∫ q in Ioi (0 : ℝ), beta q) = primitive 1 := by
  have he : (∫ q in Ioi (0 : ℝ), beta q) = ∫ q in Ioc (0 : ℝ) 4, beta q := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      (fun q hq => hq.1)
    intro q hq
    have h4 : 4 < q := by
      by_contra h
      exact hq.2 ⟨hq.1, le_of_not_gt h⟩
    exact beta_zero_right q (by linarith)
  rw [he, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)]
  exact primitive_constant_left 0 (by norm_num)

theorem weight_integral_eq : (∫ r in Ioi (0 : ℝ), weight r) = primitive 1 := by
  have hs := integral_comp_rpow_Ioi_of_pos (g := beta) (p := (2 : ℝ)) (by norm_num)
  have he : (∫ r in Ioi (0 : ℝ), weight r) = ∫ q in Ioi (0 : ℝ), beta q := by
    simpa only [weight, show (2 : ℝ)-1=1 by norm_num, Real.rpow_one,
      Real.rpow_two, smul_eq_mul] using hs
  exact he.trans beta_integral_Ioi

theorem weight_integral_positive : 0 < ∫ r in Ioi (0 : ℝ), weight r := by
  rw [weight_integral_eq]
  exact primitive_one_positive

theorem scaled_weight_substitution (a : ℝ) (ha : 0 < a) (F : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), (-2/a^2)*r*beta (r^2/a^2)*F r) =
      -(∫ u in Ioi (0 : ℝ), weight u * F (a*u)) := by
  let g : ℝ → ℝ := fun r => (-2/a^2)*r*beta (r^2/a^2)*F r
  have hs := integral_comp_mul_left_Ioi g 0 ha
  simp only [mul_zero, smul_eq_mul] at hs
  have hi : (∫ r in Ioi (0 : ℝ), g r) = a * ∫ u in Ioi (0 : ℝ), g (a*u) := by
    rw [hs, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  change (∫ r in Ioi (0 : ℝ), g r) = _
  rw [hi, ← integral_const_mul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with u
  have hq : (a*u)^2/a^2 = u^2 := by field_simp; ring
  simp only [g, weight, hq]
  field_simp
  ring

def scaledWeight (a r : ℝ) : ℝ := (2/a^2)*r*beta (r^2/a^2)

theorem scaledWeight_nonnegative (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 0 < r) :
    0 ≤ scaledWeight a r :=
  mul_nonneg (by positivity) (beta_nonnegative _)

theorem scaledWeight_zero_inner (a : ℝ) (ha : 0 < a) (r : ℝ)
    (hr : 0 ≤ r) (hra : r ≤ a) : scaledWeight a r = 0 := by
  have hq : r^2/a^2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos ha)).mpr ((sq_le_sq₀ hr ha.le).mpr hra)
  simp only [scaledWeight, beta_zero_left _ hq, mul_zero]

theorem scaledWeight_eq (a r : ℝ) :
    scaledWeight a r = a⁻¹ * weight (a⁻¹*r) := by
  have hq : (a⁻¹*r)^2 = r^2/a^2 := by
    simp only [mul_pow, inv_pow, div_eq_mul_inv]
    ring
  simp only [scaledWeight, weight, hq, div_eq_mul_inv, inv_pow]
  ring

theorem scaledWeight_integrable (a : ℝ) (ha : 0 < a) : Integrable (scaledWeight a) := by
  have hi := (weight_integrable.comp_mul_left' (inv_ne_zero ha.ne')).const_mul a⁻¹
  apply hi.congr
  filter_upwards with r
  exact (scaledWeight_eq a r).symm

theorem scaledWeight_integrableOn (a : ℝ) (ha : 0 < a) :
    IntegrableOn (scaledWeight a) (Ioi (0 : ℝ)) :=
  (scaledWeight_integrable a ha).integrableOn

theorem scaledWeight_integral_eq (a : ℝ) (ha : 0 < a) :
    (∫ r in Ioi (0 : ℝ), scaledWeight a r) = primitive 1 := by
  have hs := scaled_weight_substitution a ha (fun _ => 1)
  simp only [mul_one] at hs
  have hn : (fun r => (-2/a^2)*r*beta (r^2/a^2)) = fun r => -scaledWeight a r := by
    funext r
    unfold scaledWeight
    ring
  rw [hn, integral_neg] at hs
  exact (neg_injective hs).trans weight_integral_eq

theorem scaledWeight_integral_positive (a : ℝ) (ha : 0 < a) :
    0 < ∫ r in Ioi (0 : ℝ), scaledWeight a r := by
  rw [scaledWeight_integral_eq a ha]
  exact primitive_one_positive

end OQ14.RadialWeight



#print axioms OQ14.RadialWeight.weight_continuous
#print axioms OQ14.RadialWeight.weight_nonnegative
#print axioms OQ14.RadialWeight.weight_zero_left
#print axioms OQ14.RadialWeight.weight_zero_right
#print axioms OQ14.RadialWeight.weight_supported_Ioi
#print axioms OQ14.RadialWeight.weight_compact
#print axioms OQ14.RadialWeight.weight_integrable
#print axioms OQ14.RadialWeight.weight_integrableOn
#print axioms OQ14.RadialWeight.beta_integral_Ioi
#print axioms OQ14.RadialWeight.weight_integral_eq
#print axioms OQ14.RadialWeight.weight_integral_positive
#print axioms OQ14.RadialWeight.scaled_weight_substitution
#print axioms OQ14.RadialWeight.scaledWeight_nonnegative
#print axioms OQ14.RadialWeight.scaledWeight_zero_inner
#print axioms OQ14.RadialWeight.scaledWeight_eq
#print axioms OQ14.RadialWeight.scaledWeight_integrable
#print axioms OQ14.RadialWeight.scaledWeight_integrableOn
#print axioms OQ14.RadialWeight.scaledWeight_integral_eq
#print axioms OQ14.RadialWeight.scaledWeight_integral_positive
