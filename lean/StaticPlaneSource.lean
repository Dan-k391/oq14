import StaticPlaneKernel

/-! Genuine whole-plane L1 static fields of sources separated from the plane. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.StaticPlaneSource

open MeasureTheory Metric StaticPlaneKernel PlaneInverseCube
open scoped Topology

def integrand (f : Space → ℂ) (i j : Fin 3) (p : Space × Plane) : ℂ :=
  GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint p.2-p.1) i j*f p.1

def field (f : Space → ℂ) (i j : Fin 3) (q : Plane) : ℂ :=
  ∫ y, GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-y) i j*f y

theorem integrand_measurable (f : Space → ℂ) (hf : Integrable f) (i j : Fin 3) :
    AEStronglyMeasurable (integrand f i j) (volume.prod volume) := by
  exact ((hessian_measurable i j).comp
    ((MaxwellPlaneTail.planePoint_continuous.comp continuous_snd).sub
      continuous_fst).measurable).aestronglyMeasurable.mul hf.aestronglyMeasurable.fst

theorem fiber_mass (d : ℝ) (hd : 0 < d) (f : Space → ℂ) (i j : Fin 3)
    (y : Space) (hy : f y ≠ 0 → d ≤ |y 2|) :
    (∫ q : Plane, ‖integrand f i j (y,q)‖) ≤ (3/d)*‖f y‖ := by
  by_cases hz : f y=0
  · simp [integrand, hz]
  · simp only [integrand, norm_mul, integral_mul_const]
    exact mul_le_mul_of_nonneg_right (plane_kernel_mass d hd y (hy hz) i j) (norm_nonneg _)

theorem integrand_integrable (d : ℝ) (hd : 0 < d) (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, f y ≠ 0 → d ≤ |y 2|) (i j : Fin 3) :
    Integrable (integrand f i j) (volume.prod volume) := by
  have hm := integrand_measurable f hf i j
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hs] with y hy
    by_cases hz : f y=0
    · simpa only [integrand, hz, mul_zero] using integrable_zero Plane ℂ volume
    · exact (plane_kernel_integrable d hd y (hy hz) i j).mul_const (f y)
  · apply (hf.norm.const_mul (3/d)).mono' hm.norm.integral_prod_right'
    filter_upwards [hs] with y hy
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact fiber_mass d hd f i j y hy

theorem field_integrable (d : ℝ) (hd : 0 < d) (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, f y ≠ 0 → d ≤ |y 2|) (i j : Fin 3) :
    Integrable (field f i j) :=
  (integrand_integrable d hd f hf hs i j).integral_prod_right

theorem field_mass (d : ℝ) (hd : 0 < d) (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, f y ≠ 0 → d ≤ |y 2|) (i j : Fin 3) :
    (∫ q : Plane, ‖field f i j q‖) ≤ (3/d)*(∫ y, ‖f y‖) := by
  have hi := integrand_integrable d hd f hf hs i j
  calc
    _ ≤ ∫ q : Plane, ∫ y : Space, ‖integrand f i j (y,q)‖ := by
      exact integral_mono_ae (field_integrable d hd f hf hs i j).norm
        hi.norm.integral_prod_right
        (Filter.Eventually.of_forall (fun q => norm_integral_le_integral_norm _))
    _ = ∫ y : Space, ∫ q : Plane, ‖integrand f i j (y,q)‖ :=
      (integral_integral_swap hi.norm).symm
    _ ≤ ∫ y : Space, (3/d)*‖f y‖ := by
      apply integral_mono_ae hi.integral_norm_prod_left (hf.norm.const_mul (3/d))
      filter_upwards [hs] with y hy
      exact fiber_mass d hd f i j y hy
    _ = _ := integral_const_mul _ _

end OQ14.StaticPlaneSource

#print axioms OQ14.StaticPlaneSource.integrand_measurable
#print axioms OQ14.StaticPlaneSource.fiber_mass
#print axioms OQ14.StaticPlaneSource.integrand_integrable
#print axioms OQ14.StaticPlaneSource.field_integrable
#print axioms OQ14.StaticPlaneSource.field_mass
