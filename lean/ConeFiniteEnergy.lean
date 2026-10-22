import ConicalRadialParticular
import Mathlib.MeasureTheory.Function.L2Space

/-! Finite one-dimensional angular energy excludes the negative conical mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConeFiniteEnergy
open MeasureTheory Set OQ14.ConicalRadialParticular
open scoped ENNReal

theorem negative_power_not_memLp (ν R : ℝ) (hν : 0 < ν) (hR : 0 < R) :
    ¬MemLp (power (-ν-1)) 2 (volume.restrict (Ioo (0 : ℝ) R)) := by
  intro hm
  have hi := hm.norm.integrable_sq
  have hi' : IntegrableOn (fun r : ℝ => r^(-2*ν-2)) (Ioo (0 : ℝ) R) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [power,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.1.le _),
      ← Real.rpow_mul_natCast hr.1.le]
    congr 1
    ring
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mp hi'
  linarith

theorem negative_coefficient_zero (ν R : ℝ) (hν : 0 < ν) (hR : 0 < R)
    (U V : ℝ → ℂ) (b : ℂ)
    (hU : MemLp U 2 (volume.restrict (Ioo (0 : ℝ) R)))
    (hV : MemLp V 2 (volume.restrict (Ioo (0 : ℝ) R)))
    (heq : U =ᵐ[volume.restrict (Ioo (0 : ℝ) R)] fun r => V r+b*power (-ν-1) r) : b = 0 := by
  by_contra hb
  apply negative_power_not_memLp ν R hν hR
  apply MemLp.ae_eq _ ((hU.sub hV).const_mul b⁻¹)
  filter_upwards [heq] with r hr
  simp only [Pi.sub_apply]
  rw [hr]
  field_simp [hb]

end OQ14.ConeFiniteEnergy

#print axioms OQ14.ConeFiniteEnergy.negative_power_not_memLp
#print axioms OQ14.ConeFiniteEnergy.negative_coefficient_zero
