import Packet06ConeConstantCorrection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeHolderParticular
open MeasureTheory Set OQ14.ConePowerPrimitive OQ14.ConicalRadialParticular

theorem primitive_holder_bound (β α : ℝ) (hβ : -1 < β) (hα : 0 < α)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Ici 0)) (r M : ℝ) (hr : 0 ≤ r)
    (_hM : 0 ≤ M) (hb : ∀ s ∈ Ioo (0 : ℝ) r, ‖f s‖ ≤ M*s^α) :
    ‖primitive β f r‖ ≤ M*r^(β+α+1)/(β+α+1) := by
  have hβα : -1 < β+α := by linarith
  have hi := integrand_intervalIntegrable β hβ f hf r hr
  have hiPow := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) hβα
  have hb' : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) r), ‖((s^β : ℝ) : ℂ)*f s‖ ≤ M*s^(β+α) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hs.1.le _)]
    calc
      _ ≤ s^β*(M*s^α) := mul_le_mul_of_nonneg_left (hb s hs) (Real.rpow_nonneg hs.1.le _)
      _ = M*s^(β+α) := by rw [Real.rpow_add hs.1]; ring
  calc
    ‖primitive β f r‖ ≤ ∫ s in (0 : ℝ)..r, ‖((s^β : ℝ) : ℂ)*f s‖ := intervalIntegral.norm_integral_le_integral_norm hr
    _ ≤ ∫ s in (0 : ℝ)..r, M*s^(β+α) := by
      rw [intervalIntegral.integral_of_le hr,intervalIntegral.integral_of_le hr]
      exact integral_mono_ae hi.1.norm (hiPow.const_mul M).1 hb'
    _ = M*r^(β+α+1)/(β+α+1) := by
      rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl hβα),
        Real.zero_rpow (by linarith : β+α+1 ≠ 0),sub_zero]
      ring
theorem particular_holder_bound (ν α : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (hα : 0 < α)
    (A B : ℝ → ℂ) (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ s ∈ Ioo (0 : ℝ) r, ‖A s‖ ≤ M*s^α ∧ ‖B s‖ ≤ M*s^α) :
    ‖particular ν A B r‖ ≤ (3/α+1)*M*r^(1+α) := by
  have hL : ∀ s ∈ Ioo (0 : ℝ) r, ‖minusForcing ν A B s‖ ≤ (3*M)*s^α := by
    intro s hs
    have hm : 0 ≤ M*s^α := mul_nonneg hM (Real.rpow_nonneg hs.1.le _)
    calc
      _ ≤ ‖B s‖ + ‖((ν+1 : ℝ) : ℂ)*A s‖ := norm_sub_le _ _
      _ = ‖B s‖+(ν+1)*‖A s‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [hν.1] : 0 < ν+1)]
      _ ≤ M*s^α+(ν+1)*(M*s^α) := add_le_add (hb s hs).2
        (mul_le_mul_of_nonneg_left (hb s hs).1 (by linarith [hν.1]))
      _ ≤ (3*M)*s^α := by nlinarith [hν.2]
  have hR : ∀ s ∈ Ioo (0 : ℝ) r, ‖plusForcing ν A B s‖ ≤ (2*M)*s^α := by
    intro s hs
    have hm : 0 ≤ M*s^α := mul_nonneg hM (Real.rpow_nonneg hs.1.le _)
    calc
      _ ≤ ‖B s‖+‖(ν : ℂ)*A s‖ := norm_add_le _ _
      _ = ‖B s‖+ν*‖A s‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hν.1]
      _ ≤ M*s^α+ν*(M*s^α) := add_le_add (hb s hs).2 (mul_le_mul_of_nonneg_left (hb s hs).1 hν.1.le)
      _ ≤ (2*M)*s^α := by nlinarith [hν.2]
  have hl := primitive_holder_bound (-ν) α (by linarith [hν.2]) hα (minusForcing ν A B)
    (hB.sub (continuousOn_const.mul hA)) r (3*M) hr.le (by positivity) hL
  have hr' := primitive_holder_bound (ν+1) α (by linarith [hν.1]) hα (plusForcing ν A B)
    (hB.add (continuousOn_const.mul hA)) r (2*M) hr.le (by positivity) hR
  have hp1 : r^ν*r^(-ν+α+1)=r^(1+α) := by rw [← Real.rpow_add hr]; congr 1; ring
  have hp2 : r^(-ν-1)*r^(ν+1+α+1)=r^(1+α) := by rw [← Real.rpow_add hr]; congr 1; ring
  have hleft : ‖leftPrimitive ν A B r‖ ≤ (3/α)*M*r^(-ν+α+1) := by
    dsimp only [leftPrimitive]
    apply hl.trans
    have hd : α ≤ -ν+α+1 := by linarith [hν.2]
    have hk : 0 ≤ (3*M)*r^(-ν+α+1) := mul_nonneg (by positivity) (Real.rpow_nonneg hr.le _)
    have hh := div_le_div_of_nonneg_left hk hα hd
    convert hh using 1
    ring
  have hright : ‖rightPrimitive ν A B r‖ ≤ M*r^(ν+1+α+1) := by
    dsimp only [rightPrimitive]
    apply hr'.trans
    have hd : (2 : ℝ) ≤ ν+1+α+1 := by linarith [hν.1]
    have hk : 0 ≤ M*r^(ν+1+α+1) := mul_nonneg hM (Real.rpow_nonneg hr.le _)
    apply (div_le_iff₀ (by linarith [hν.1] : 0 < ν+1+α+1)).mpr
    nlinarith
  have hd : 1 ≤ 2*ν+1 := by linarith [hν.1]
  have hdiv (w : ℂ) : ‖w/((2*ν+1 : ℝ) : ℂ)‖ ≤ ‖w‖ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 2*ν+1)]
    exact div_le_self (norm_nonneg w) hd
  calc
    _ ≤ ‖power ν r*leftPrimitive ν A B r-power (-ν-1) r*rightPrimitive ν A B r‖ := hdiv _
    _ ≤ ‖power ν r*leftPrimitive ν A B r‖+‖power (-ν-1) r*rightPrimitive ν A B r‖ := norm_sub_le _ _
    _ = r^ν*‖leftPrimitive ν A B r‖+r^(-ν-1)*‖rightPrimitive ν A B r‖ := by
      simp only [norm_mul,power,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.le _)]
    _ ≤ r^ν*((3/α)*M*r^(-ν+α+1))+r^(-ν-1)*(M*r^(ν+1+α+1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hleft (Real.rpow_nonneg hr.le _))
        (mul_le_mul_of_nonneg_left hright (Real.rpow_nonneg hr.le _))
    _ = (3/α+1)*M*r^(1+α) := by
      linear_combination ((3/α)*M)*hp1+M*hp2

#print axioms OQ14.Packet06ConeHolderParticular.primitive_holder_bound
#print axioms OQ14.Packet06ConeHolderParticular.particular_holder_bound
end OQ14.Packet06ConeHolderParticular
