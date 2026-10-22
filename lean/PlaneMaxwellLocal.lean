import PlaneDynamicLocal

/-! Derived actual Maxwell kernel constants for bounded-disk plane source errors. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.PlaneMaxwellLocal

open MeasureTheory Metric Set StaticPlaneKernel PlaneInverseCube PlaneDynamicLocal
open scoped Topology

def remainderCoefficient (k R T : ℝ) : ℝ := (14*k^2/(4*Real.pi))*(T+R)^2
def electricCoefficient (k R T : ℝ) : ℝ := (1/Real.pi)+remainderCoefficient k R T
def gradientCoefficient (k R T : ℝ) : ℝ := (4*Real.pi)⁻¹*(|k| * (T+R)^2+(T+R))

theorem inverse_one_to_three (r M : ℝ) (hr : 0 < r) (hrM : r ≤ M) :
    r⁻¹ ≤ M^2*r⁻¹^3 := by
  calc
    r⁻¹ = r^2*r⁻¹^3 := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hrM 2) (by positivity)

theorem inverse_two_to_three (r M : ℝ) (hr : 0 < r) (hrM : r ≤ M) :
    r⁻¹^2 ≤ M*r⁻¹^3 := by
  have he : r⁻¹^2=r*r⁻¹^3 := by field_simp; ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hrM (by positivity)

theorem remainder_kernel_bound (k R T : ℝ) (z : Space) (hz : z ≠ 0)
    (hM : ‖z‖ ≤ T+R) (i j : Fin 3) :
    ‖DyadicKernel.remainder k z i j‖ ≤ remainderCoefficient k R T*‖z‖⁻¹^3 := by
  exact (RealKernelBounds.remainder_bound_all k z i j).trans
    ((mul_le_mul_of_nonneg_left (inverse_one_to_three ‖z‖ (T+R) (norm_pos_iff.mpr hz) hM)
      (by positivity)).trans_eq (by unfold remainderCoefficient; ring))

theorem electric_kernel_bound (k R T : ℝ) (z : Space) (hz : z ≠ 0)
    (hM : ‖z‖ ≤ T+R) (i j : Fin 3) :
    ‖DyadicKernel.dyadic k z i j‖ ≤ electricCoefficient k R T*‖z‖⁻¹^3 := by
  have he : DyadicKernel.dyadic k z i j=
      GreenKernel.phiHessian 0 z i j+DyadicKernel.remainder k z i j := by
    unfold DyadicKernel.remainder
    ring
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add (static_hessian_bound z hz i j)
    (remainder_kernel_bound k R T z hz hM i j))).trans_eq (by unfold electricCoefficient; ring)

theorem gradient_kernel_bound (k R T : ℝ) (z : Space) (hz : z ≠ 0)
    (hM : ‖z‖ ≤ T+R) (i : Fin 3) :
    ‖GreenKernel.phiGradient k z i‖ ≤ gradientCoefficient k R T*‖z‖⁻¹^3 := by
  apply (KernelGradient.gradient_bound k z i).trans
  exact (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (inverse_one_to_three ‖z‖ (T+R) (norm_pos_iff.mpr hz) hM)
      (abs_nonneg k)) (inverse_two_to_three ‖z‖ (T+R) (norm_pos_iff.mpr hz) hM))
    (by positivity)).trans_eq (by unfold gradientCoefficient; ring)

theorem remainder_mass (k R T d : ℝ) (hd : 0 < d) (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, f y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2|) (i j : Fin 3) :
    IntegrableOn (fun q : Plane => KernelConvolution.response
      (fun z => DyadicKernel.remainder k z i j) f (MaxwellPlaneTail.planePoint q)) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖KernelConvolution.response
      (fun z => DyadicKernel.remainder k z i j) f (MaxwellPlaneTail.planePoint q)‖) ≤
      (remainderCoefficient k R T*((Real.pi+diskConstant)/d))*(∫ y, ‖f y‖) := by
  have hC : 0 ≤ remainderCoefficient k R T := by unfold remainderCoefficient; positivity
  exact ⟨response_integrableOn _ f (DynamicIntegrability.remainder_measurable k i j) hf
      R T d _ hd hC (fun z hz hm => remainder_kernel_bound k R T z hz hm i j) hs,
    response_mass _ f (DynamicIntegrability.remainder_measurable k i j) hf
      R T d _ hd hC (fun z hz hm => remainder_kernel_bound k R T z hz hm i j) hs⟩

theorem electric_entry_mass (k R T d : ℝ) (hd : 0 < d) (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, f y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2|) (i j : Fin 3) :
    IntegrableOn (fun q : Plane => KernelConvolution.response
      (fun z => DyadicKernel.dyadic k z i j) f (MaxwellPlaneTail.planePoint q)) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖KernelConvolution.response
      (fun z => DyadicKernel.dyadic k z i j) f (MaxwellPlaneTail.planePoint q)‖) ≤
      (electricCoefficient k R T*((Real.pi+diskConstant)/d))*(∫ y, ‖f y‖) := by
  have hC : 0 ≤ electricCoefficient k R T := by unfold electricCoefficient remainderCoefficient; positivity
  exact ⟨response_integrableOn _ f (PlaneSourceKernel.dyadic_measurable k i j) hf
      R T d _ hd hC (fun z hz hm => electric_kernel_bound k R T z hz hm i j) hs,
    response_mass _ f (PlaneSourceKernel.dyadic_measurable k i j) hf
      R T d _ hd hC (fun z hz hm => electric_kernel_bound k R T z hz hm i j) hs⟩

theorem gradient_mass (k R T d : ℝ) (hd : 0 < d) (hM : 0 ≤ T+R)
    (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, f y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2|) (i : Fin 3) :
    IntegrableOn (fun q : Plane => KernelConvolution.response
      (fun z => GreenKernel.phiGradient k z i) f (MaxwellPlaneTail.planePoint q)) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖KernelConvolution.response
      (fun z => GreenKernel.phiGradient k z i) f (MaxwellPlaneTail.planePoint q)‖) ≤
      (gradientCoefficient k R T*((Real.pi+diskConstant)/d))*(∫ y, ‖f y‖) := by
  have hC : 0 ≤ gradientCoefficient k R T := by unfold gradientCoefficient; positivity
  exact ⟨response_integrableOn _ f (KernelGradient.gradient_measurable k i) hf
      R T d _ hd hC (fun z hz hm => gradient_kernel_bound k R T z hz hm i) hs,
    response_mass _ f (KernelGradient.gradient_measurable k i) hf
      R T d _ hd hC (fun z hz hm => gradient_kernel_bound k R T z hz hm i) hs⟩

end OQ14.PlaneMaxwellLocal

#print axioms OQ14.PlaneMaxwellLocal.inverse_one_to_three
#print axioms OQ14.PlaneMaxwellLocal.inverse_two_to_three
#print axioms OQ14.PlaneMaxwellLocal.remainder_kernel_bound
#print axioms OQ14.PlaneMaxwellLocal.electric_kernel_bound
#print axioms OQ14.PlaneMaxwellLocal.gradient_kernel_bound
#print axioms OQ14.PlaneMaxwellLocal.remainder_mass
#print axioms OQ14.PlaneMaxwellLocal.electric_entry_mass
#print axioms OQ14.PlaneMaxwellLocal.gradient_mass
