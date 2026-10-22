import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Genuine endpoint-integrable power primitives for the inhomogeneous cone equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.ConePowerPrimitive
open MeasureTheory Set Filter
open scoped Topology

def primitive (β : ℝ) (f : ℝ → ℂ) (r : ℝ) : ℂ := ∫ s in (0 : ℝ)..r, ((s^β : ℝ) : ℂ)*f s

theorem integrand_continuousAt (β : ℝ) (f : ℝ → ℂ) (hf : ContinuousOn f (Ici 0))
    (r : ℝ) (hr : 0 < r) : ContinuousAt (fun s : ℝ => ((s^β : ℝ) : ℂ)*f s) r := by
  exact (Complex.continuous_ofReal.continuousAt.comp
    ((Real.hasDerivAt_rpow_const (p := β) (Or.inl hr.ne')).continuousAt)).mul
      ((hf r hr.le).continuousAt (Ici_mem_nhds hr))

theorem integrand_intervalIntegrable (β : ℝ) (hβ : -1 < β) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ici 0)) (r : ℝ) (hr : 0 ≤ r) :
    IntervalIntegrable (fun s : ℝ => ((s^β : ℝ) : ℂ)*f s) volume 0 r := by
  have hi := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) hβ
  have hic : IntervalIntegrable (fun s : ℝ => ((s^β : ℝ) : ℂ)) volume 0 r := ⟨hi.1.ofReal,hi.2.ofReal⟩
  apply hic.mul_continuousOn
  rw [uIcc_of_le hr]
  exact hf.mono Icc_subset_Ici_self

theorem primitive_hasDerivAt (β : ℝ) (hβ : -1 < β) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ici 0)) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (primitive β f) (((r^β : ℝ) : ℂ)*f r) r := by
  apply intervalIntegral.integral_hasDerivAt_right
    (integrand_intervalIntegrable β hβ f hf r hr.le)
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun x hx => integrand_continuousAt β f hf x hx) r hr
  · exact integrand_continuousAt β f hf r hr

theorem primitive_norm_le (β : ℝ) (hβ : -1 < β) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ici 0)) (r M : ℝ) (hr : 0 ≤ r)
    (hb : ∀ s ∈ Ioo (0 : ℝ) r, ‖f s‖ ≤ M) :
    ‖primitive β f r‖ ≤ M*r^(β+1)/(β+1) := by
  have hi := integrand_intervalIntegrable β hβ f hf r hr
  have hiPow := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) hβ
  have hb' : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) r), ‖((s^β : ℝ) : ℂ)*f s‖ ≤ M*s^β := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hs.1.le _)]
    exact (mul_le_mul_of_nonneg_left (hb s hs)
      (Real.rpow_nonneg hs.1.le _)).trans_eq (mul_comm _ _)
  calc
    ‖primitive β f r‖ ≤ ∫ s in (0 : ℝ)..r, ‖((s^β : ℝ) : ℂ)*f s‖ := intervalIntegral.norm_integral_le_integral_norm hr
    _ ≤ ∫ s in (0 : ℝ)..r, M*s^β := by
      rw [intervalIntegral.integral_of_le hr,intervalIntegral.integral_of_le hr]
      exact integral_mono_ae hi.1.norm (hiPow.const_mul M).1 hb'
    _ = M*r^(β+1)/(β+1) := by
      rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl hβ),
        Real.zero_rpow (by linarith : β+1 ≠ 0),sub_zero]
      ring

end OQ14.ConePowerPrimitive

#print axioms OQ14.ConePowerPrimitive.integrand_continuousAt
#print axioms OQ14.ConePowerPrimitive.integrand_intervalIntegrable
#print axioms OQ14.ConePowerPrimitive.primitive_hasDerivAt
#print axioms OQ14.ConePowerPrimitive.primitive_norm_le
