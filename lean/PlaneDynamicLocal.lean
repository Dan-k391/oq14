import NewtonStripMaxwell

/-! Genuine bounded-disk plane integrals with explicit inverse-gap constants. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.PlaneDynamicLocal

open MeasureTheory Metric Set StaticPlaneKernel PlaneInverseCube
open scoped Topology

def integrand (K f : Space → ℂ) (p : Space × Plane) : ℂ :=
  f p.1*K (MaxwellPlaneTail.planePoint p.2-p.1)

theorem disk_distance (R T : ℝ) (y : Space) (hy : ‖y‖ ≤ R)
    (q : Plane) (hq : q ∈ closedBall 0 T) :
    ‖MaxwellPlaneTail.planePoint q-y‖ ≤ T+R := by
  have ht : ‖q‖ ≤ T := by simpa only [mem_closedBall, dist_zero_right] using hq
  exact (norm_sub_le _ _).trans (add_le_add (by rw [MaxwellPlaneTail.planePoint_norm]; exact ht) hy)

theorem fiber_integrable (K : Space → ℂ) (hKm : Measurable K) (R T d C : ℝ)
    (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ z, z ≠ 0 → ‖z‖ ≤ T+R → ‖K z‖ ≤ C*‖z‖⁻¹^3)
    (y : Space) (hy : ‖y‖ ≤ R) (hgap : d ≤ |y 2|) :
    IntegrableOn (fun q : Plane => K (MaxwellPlaneTail.planePoint q-y)) (closedBall 0 T) := by
  apply ((translated_envelope_integrable d hd (horizontal y)).const_mul C).integrableOn.mono'
    ((hKm.comp (MaxwellPlaneTail.planePoint_continuous.sub continuous_const).measurable).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with q hq
  have hs := PlaneSourceKernel.gap_distance d q y hgap
  have hn : MaxwellPlaneTail.planePoint q-y ≠ 0 := norm_pos_iff.mp (hd.trans_le hs)
  exact (hb _ hn (disk_distance R T y hy q hq)).trans
    (mul_le_mul_of_nonneg_left (inverse_cube_le_envelope d hd (q-horizontal y) _ hs
      (horizontal_distance q y)) hC)

theorem fiber_mass (K : Space → ℂ) (hKm : Measurable K) (R T d C : ℝ)
    (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ z, z ≠ 0 → ‖z‖ ≤ T+R → ‖K z‖ ≤ C*‖z‖⁻¹^3)
    (y : Space) (hy : ‖y‖ ≤ R) (hgap : d ≤ |y 2|) :
    (∫ q : Plane in closedBall 0 T, ‖K (MaxwellPlaneTail.planePoint q-y)‖) ≤
      C*((Real.pi+diskConstant)/d) := by
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, C*envelope d (q-horizontal y) := by
      apply integral_mono_ae (fiber_integrable K hKm R T d C hd hC hb y hy hgap).norm
        (((translated_envelope_integrable d hd (horizontal y)).const_mul C).integrableOn)
      filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with q hq
      have hs := PlaneSourceKernel.gap_distance d q y hgap
      have hn : MaxwellPlaneTail.planePoint q-y ≠ 0 := norm_pos_iff.mp (hd.trans_le hs)
      exact (hb _ hn (disk_distance R T y hy q hq)).trans
        (mul_le_mul_of_nonneg_left (inverse_cube_le_envelope d hd (q-horizontal y) _ hs
          (horizontal_distance q y)) hC)
    _ ≤ ∫ q : Plane, C*envelope d (q-horizontal y) :=
      setIntegral_le_integral ((translated_envelope_integrable d hd (horizontal y)).const_mul C)
        (Filter.Eventually.of_forall (fun q => mul_nonneg hC (envelope_nonnegative d hd.le _)))
    _ = _ := by rw [integral_const_mul, translated_envelope_integral d hd]

theorem source_integrand_integrable (K f : Space → ℂ) (hKm : Measurable K) (hf : Integrable f)
    (R T d C : ℝ) (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ z, z ≠ 0 → ‖z‖ ≤ T+R → ‖K z‖ ≤ C*‖z‖⁻¹^3)
    (hs : ∀ᵐ y, f y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2|) :
    Integrable (integrand K f)
      ((volume : Measure Space).prod ((volume : Measure Plane).restrict (closedBall 0 T))) := by
  have hm : AEStronglyMeasurable (integrand K f)
      ((volume : Measure Space).prod ((volume : Measure Plane).restrict (closedBall 0 T))) :=
    hf.aestronglyMeasurable.fst.mul ((hKm.comp
      ((MaxwellPlaneTail.planePoint_continuous.comp continuous_snd).sub continuous_fst).measurable).aestronglyMeasurable)
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hs] with y hy
    by_cases hz : f y=0
    · simpa only [integrand, hz, zero_mul] using
        integrable_zero Plane ℂ ((volume : Measure Plane).restrict (closedBall 0 T))
    · exact (fiber_integrable K hKm R T d C hd hC hb y (hy hz).1 (hy hz).2).const_mul (f y)
  · apply (hf.norm.mul_const (C*((Real.pi+diskConstant)/d))).mono' hm.norm.integral_prod_right'
    filter_upwards [hs] with y hy
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    by_cases hz : f y=0
    · simp [integrand, hz]
    · simp only [integrand, norm_mul, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (fiber_mass K hKm R T d C hd hC hb y (hy hz).1 (hy hz).2)
        (norm_nonneg (f y))

theorem response_integrableOn (K f : Space → ℂ) (hKm : Measurable K) (hf : Integrable f)
    (R T d C : ℝ) (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ z, z ≠ 0 → ‖z‖ ≤ T+R → ‖K z‖ ≤ C*‖z‖⁻¹^3)
    (hs : ∀ᵐ y, f y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2|) :
    IntegrableOn (fun q : Plane => KernelConvolution.response K f (MaxwellPlaneTail.planePoint q))
      (closedBall 0 T) :=
  (source_integrand_integrable K f hKm hf R T d C hd hC hb hs).integral_prod_right

theorem response_mass (K f : Space → ℂ) (hKm : Measurable K) (hf : Integrable f)
    (R T d C : ℝ) (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ z, z ≠ 0 → ‖z‖ ≤ T+R → ‖K z‖ ≤ C*‖z‖⁻¹^3)
    (hs : ∀ᵐ y, f y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2|) :
    (∫ q : Plane in closedBall 0 T, ‖KernelConvolution.response K f (MaxwellPlaneTail.planePoint q)‖) ≤
      (C*((Real.pi+diskConstant)/d))*(∫ y, ‖f y‖) := by
  have hi := source_integrand_integrable K f hKm hf R T d C hd hC hb hs
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, ∫ y : Space, ‖integrand K f (y,q)‖ :=
      integral_mono_ae (response_integrableOn K f hKm hf R T d C hd hC hb hs).norm
        hi.norm.integral_prod_right
        (Filter.Eventually.of_forall (fun _ => norm_integral_le_integral_norm _))
    _ = ∫ y : Space, ∫ q : Plane in closedBall 0 T, ‖integrand K f (y,q)‖ :=
      (integral_integral_swap hi.norm).symm
    _ ≤ ∫ y : Space, ‖f y‖*(C*((Real.pi+diskConstant)/d)) := by
      apply integral_mono_ae hi.integral_norm_prod_left (hf.norm.mul_const _)
      filter_upwards [hs] with y hy
      by_cases hz : f y=0
      · simp [integrand, hz]
      · simp only [integrand, norm_mul, integral_const_mul]
        exact mul_le_mul_of_nonneg_left (fiber_mass K hKm R T d C hd hC hb y (hy hz).1 (hy hz).2)
          (norm_nonneg (f y))
    _ = _ := by rw [integral_mul_const]; ring

end OQ14.PlaneDynamicLocal

#print axioms OQ14.PlaneDynamicLocal.disk_distance
#print axioms OQ14.PlaneDynamicLocal.fiber_integrable
#print axioms OQ14.PlaneDynamicLocal.fiber_mass
#print axioms OQ14.PlaneDynamicLocal.source_integrand_integrable
#print axioms OQ14.PlaneDynamicLocal.response_integrableOn
#print axioms OQ14.PlaneDynamicLocal.response_mass
