import SourceHerglotzTail
import NewtonStripMaxwell

/-! Actual static Hessian source fields have inverse-cube tails. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.StaticSourceTail
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open scoped Topology
abbrev Space := FourierL2.Space

theorem kernel_bound (R : ℝ) (hR : 0 ≤ R) (x y : Space) (hx : 2*R < ‖x‖)
    (hy : y ∈ closedBall 0 R) (i j : Fin 3) :
    ‖GreenKernel.phiHessian 0 (x-y) i j‖ ≤ (8/Real.pi)/‖x‖^3 := by
  obtain ⟨hn,hxy,hd⟩ := ScalarRadiation.distance_lower_bound R hR x y hx hy
  have hp : 0 < ‖x‖/2 := by have := norm_pos_iff.mpr hn; positivity
  have hb := StaticPlaneKernel.static_hessian_bound (x-y) hxy i j
  calc
    _ ≤ (1/Real.pi)*‖x-y‖⁻¹^3 := hb
    _ ≤ (1/Real.pi)*(‖x‖/2)⁻¹^3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
        (inv_le_inv₀ (hp.trans_le hd) hp |>.mpr hd) 3) (by positivity)
    _ = _ := by field_simp; ring

theorem field_bound (R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (S : Source) (hS : Admissible R d S)
    (q : Plane) (hq : 2*R < ‖q‖) (i : Fin 3) :
    ‖NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q) i‖ ≤
      ((8/Real.pi)/‖q‖^3)*sourceMass S := by
  have hs : MaxwellPlaneTail.planePoint q ∈ NewtonSeparatedResponse.strip d := by
    simp [NewtonSeparatedResponse.strip,MaxwellPlaneTail.planePoint,hd]
  have hi (j : Fin 3) := NewtonSeparatedResponse.scalar_integrand_integrable (S j) (hS.integrable j)
    d hd (hS.gap j) _ hs i j
  unfold NewtonSeparatedResponse.response KernelConvolution.response
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 3, ∫ y, ‖S j y*GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-y) i j‖ :=
      Finset.sum_le_sum (fun j _ => norm_integral_le_integral_norm _)
    _ ≤ ∑ j : Fin 3, ((8/Real.pi)/‖q‖^3)*(∫ y, ‖S j y‖) := Finset.sum_le_sum (fun j _ => by
      rw [← integral_const_mul]
      apply integral_mono_ae (hi j).norm ((hS.integrable j).norm.const_mul _)
      filter_upwards with y
      by_cases hy : S j y=0
      · simp [hy]
      rw [norm_mul]
      have hym : y ∈ closedBall 0 R := by
        by_contra hn
        exact hy (hS.support j y hn)
      have hb := kernel_bound R hR (MaxwellPlaneTail.planePoint q) y
        (by simpa only [MaxwellPlaneTail.planePoint_norm] using hq) hym i j
      simpa only [MaxwellPlaneTail.planePoint_norm,mul_comm] using
        mul_le_mul_of_nonneg_left hb (norm_nonneg (S j y)))
    _ = _ := by unfold sourceMass; rw [Finset.mul_sum]

end OQ14.StaticSourceTail
#print axioms OQ14.StaticSourceTail.kernel_bound
#print axioms OQ14.StaticSourceTail.field_bound
