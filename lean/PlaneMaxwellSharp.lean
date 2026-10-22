import PlaneMaxwellLocal
import PlaneInverseLocal

/-! Genuine local electric remainder and magnetic gradient plane bounds with sharp gap growth. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.PlaneMaxwellSharp

open MeasureTheory Metric Set StaticPlaneKernel PlaneInverseCube
open scoped Topology

def remainderMass (k R T : ℝ) : ℝ := (14*k^2/(4*Real.pi))*(2*Real.pi*(T+R))
def gradientMass (k R T d : ℝ) : ℝ :=
  (4*Real.pi)⁻¹*(|k| * (2*Real.pi*(T+R))+Real.pi+diskConstant*Real.log ((T+R)/d))

private theorem translated_integrable (f : Plane → ℝ) (hf : Integrable f) (p : Plane) :
    Integrable (fun q => f (q-p)) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure Plane) (-p)).integrable_comp
      hf.aestronglyMeasurable |>.mpr hf

private theorem translated_integral (f : Plane → ℝ) (p : Plane) :
    (∫ q : Plane, f (q-p))=∫ q : Plane, f q := by
  simpa only [sub_eq_add_neg] using integral_add_right_eq_self f (-p)

private theorem inverse_envelope (p : ℕ) (R T d : ℝ) (hd : 0 < d)
    (y : Space) (hy : ‖y‖ ≤ R) (hgap : d ≤ |y 2|)
    (q : Plane) (hq : q ∈ closedBall 0 T) :
    ‖MaxwellPlaneTail.planePoint q-y‖⁻¹^p ≤
      PlaneInverseLocal.envelope p d (T+R) (q-horizontal y) := by
  have hs := PlaneSourceKernel.gap_distance d q y hgap
  have hu := PlaneDynamicLocal.disk_distance R T y hy q hq
  exact PlaneInverseLocal.inverse_pow_le_envelope p d (T+R) hd _ _ hs
    (horizontal_distance q y) ((horizontal_distance q y).trans hu)

theorem remainder_fiber_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R)
    (y : Space) (hy : ‖y‖ ≤ R) (hgap : d ≤ |y 2|) (i j : Fin 3) :
    (∫ q : Plane in closedBall 0 T,
      ‖DyadicKernel.remainder k (MaxwellPlaneTail.planePoint q-y) i j‖) ≤ remainderMass k R T := by
  let A := 14*k^2/(4*Real.pi)
  let E := fun q => A*PlaneInverseLocal.envelope 1 d (T+R) (q-horizontal y)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : Integrable E :=
    (translated_integrable _ (PlaneInverseLocal.envelope_one_integrable d (T+R) hd) (horizontal y)).const_mul A
  have hC : 0 ≤ PlaneMaxwellLocal.remainderCoefficient k R T := by
    unfold PlaneMaxwellLocal.remainderCoefficient
    positivity
  have hK := PlaneDynamicLocal.fiber_integrable _ (DynamicIntegrability.remainder_measurable k i j)
    R T d _ hd hC (fun z hz hm => PlaneMaxwellLocal.remainder_kernel_bound k R T z hz hm i j) y hy hgap
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, E q := by
      apply integral_mono_ae hK.norm hE.integrableOn
      filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with q hq
      apply (RealKernelBounds.remainder_bound_all k _ i j).trans
      exact mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using inverse_envelope 1 R T d hd y hy hgap q hq) hA
    _ ≤ ∫ q : Plane, E q := setIntegral_le_integral hE
      (Filter.Eventually.of_forall (fun q => mul_nonneg hA (PlaneInverseLocal.envelope_nonnegative 1 d (T+R) hd.le _)))
    _ ≤ remainderMass k R T := by
      rw [show (∫ q : Plane, E q)=A*(∫ q : Plane, PlaneInverseLocal.envelope 1 d (T+R) q) by
        rw [integral_const_mul, translated_integral]]
      exact mul_le_mul_of_nonneg_left (PlaneInverseLocal.envelope_one_mass d (T+R) hd hdM) hA

theorem gradient_fiber_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R)
    (y : Space) (hy : ‖y‖ ≤ R) (hgap : d ≤ |y 2|) (i : Fin 3) :
    (∫ q : Plane in closedBall 0 T,
      ‖GreenKernel.phiGradient k (MaxwellPlaneTail.planePoint q-y) i‖) ≤ gradientMass k R T d := by
  let e₁ := fun q => PlaneInverseLocal.envelope 1 d (T+R) (q-horizontal y)
  let e₂ := fun q => PlaneInverseLocal.envelope 2 d (T+R) (q-horizontal y)
  let A := (4*Real.pi)⁻¹
  let E := fun q => A*(|k| * e₁ q+e₂ q)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hi₁ : Integrable e₁ := translated_integrable _ (PlaneInverseLocal.envelope_one_integrable d (T+R) hd) _
  have hi₂ : Integrable e₂ := translated_integrable _ (PlaneInverseLocal.envelope_two_integrable d (T+R) hd) _
  have hE : Integrable E := ((hi₁.const_mul |k|).add hi₂).const_mul A
  have hM0 : 0 ≤ T+R := (hd.trans_le hdM).le
  have hC : 0 ≤ PlaneMaxwellLocal.gradientCoefficient k R T := by
    unfold PlaneMaxwellLocal.gradientCoefficient
    positivity
  have hK := PlaneDynamicLocal.fiber_integrable _ (KernelGradient.gradient_measurable k i)
    R T d _ hd hC (fun z hz hm => PlaneMaxwellLocal.gradient_kernel_bound k R T z hz hm i) y hy hgap
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, E q := by
      apply integral_mono_ae hK.norm hE.integrableOn
      filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with q hq
      apply (KernelGradient.gradient_bound k _ i).trans
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [pow_one] using inverse_envelope 1 R T d hd y hy hgap q hq)
          (abs_nonneg k)) (inverse_envelope 2 R T d hd y hy hgap q hq)) hA
    _ ≤ ∫ q : Plane, E q := setIntegral_le_integral hE (Filter.Eventually.of_forall (fun q =>
      mul_nonneg hA (add_nonneg (mul_nonneg (abs_nonneg k)
        (PlaneInverseLocal.envelope_nonnegative 1 d (T+R) hd.le _))
        (PlaneInverseLocal.envelope_nonnegative 2 d (T+R) hd.le _))))
    _ ≤ gradientMass k R T d := by
      have he : (∫ q : Plane, E q)=A*(|k| * (∫ q : Plane, PlaneInverseLocal.envelope 1 d (T+R) q)+
          ∫ q : Plane, PlaneInverseLocal.envelope 2 d (T+R) q) := by
        rw [integral_const_mul, integral_add (hi₁.const_mul |k|) hi₂, integral_const_mul]
        rw [translated_integral, translated_integral]
      rw [he, PlaneInverseLocal.envelope_two_integral d (T+R) hd hdM]
      exact (mul_le_mul_of_nonneg_left (add_le_add_right
        (mul_le_mul_of_nonneg_left (PlaneInverseLocal.envelope_one_mass d (T+R) hd hdM) (abs_nonneg k)) _) hA).trans_eq
          (by unfold gradientMass; dsimp [A]; ring)

private theorem mass_from_fibers (K f : Space → ℂ) (hf : Integrable f) (T L : ℝ)
    (hi : Integrable (PlaneDynamicLocal.integrand K f)
      ((volume : Measure Space).prod ((volume : Measure Plane).restrict (closedBall 0 T))))
    (hL : ∀ᵐ y, (∫ q : Plane in closedBall 0 T,
      ‖PlaneDynamicLocal.integrand K f (y,q)‖) ≤ ‖f y‖*L) :
    IntegrableOn (fun q : Plane => KernelConvolution.response K f (MaxwellPlaneTail.planePoint q)) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖KernelConvolution.response K f (MaxwellPlaneTail.planePoint q)‖) ≤
      L*(∫ y, ‖f y‖) := by
  refine ⟨hi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, ∫ y : Space, ‖PlaneDynamicLocal.integrand K f (y,q)‖ :=
      integral_mono_ae hi.integral_prod_right.norm hi.norm.integral_prod_right
        (Filter.Eventually.of_forall (fun _ => norm_integral_le_integral_norm _))
    _ = ∫ y : Space, ∫ q : Plane in closedBall 0 T, ‖PlaneDynamicLocal.integrand K f (y,q)‖ :=
      (integral_integral_swap hi.norm).symm
    _ ≤ ∫ y : Space, ‖f y‖*L := integral_mono_ae hi.integral_norm_prod_left (hf.norm.mul_const L) hL
    _ = _ := by rw [integral_mul_const]; ring

theorem remainder_response_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R)
    (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, f y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2|) (i j : Fin 3) :
    IntegrableOn (fun q : Plane => KernelConvolution.response (fun z => DyadicKernel.remainder k z i j) f
      (MaxwellPlaneTail.planePoint q)) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖KernelConvolution.response (fun z => DyadicKernel.remainder k z i j) f
      (MaxwellPlaneTail.planePoint q)‖) ≤ remainderMass k R T*(∫ y, ‖f y‖) := by
  have hC : 0 ≤ PlaneMaxwellLocal.remainderCoefficient k R T := by
    unfold PlaneMaxwellLocal.remainderCoefficient
    positivity
  have hi := PlaneDynamicLocal.source_integrand_integrable _ f
    (DynamicIntegrability.remainder_measurable k i j) hf R T d _ hd hC
    (fun z hz hm => PlaneMaxwellLocal.remainder_kernel_bound k R T z hz hm i j) hs
  apply mass_from_fibers _ f hf T _ hi
  filter_upwards [hs] with y hy
  by_cases hz : f y=0
  · simp [PlaneDynamicLocal.integrand, hz]
  · simp only [PlaneDynamicLocal.integrand, norm_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (remainder_fiber_mass k R T d hd hdM y (hy hz).1 (hy hz).2 i j)
      (norm_nonneg (f y))

theorem gradient_response_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R)
    (f : Space → ℂ) (hf : Integrable f)
    (hs : ∀ᵐ y, f y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2|) (i : Fin 3) :
    IntegrableOn (fun q : Plane => KernelConvolution.response (fun z => GreenKernel.phiGradient k z i) f
      (MaxwellPlaneTail.planePoint q)) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖KernelConvolution.response (fun z => GreenKernel.phiGradient k z i) f
      (MaxwellPlaneTail.planePoint q)‖) ≤ gradientMass k R T d*(∫ y, ‖f y‖) := by
  have hM0 : 0 ≤ T+R := (hd.trans_le hdM).le
  have hC : 0 ≤ PlaneMaxwellLocal.gradientCoefficient k R T := by
    unfold PlaneMaxwellLocal.gradientCoefficient
    positivity
  have hi := PlaneDynamicLocal.source_integrand_integrable _ f
    (KernelGradient.gradient_measurable k i) hf R T d _ hd hC
    (fun z hz hm => PlaneMaxwellLocal.gradient_kernel_bound k R T z hz hm i) hs
  apply mass_from_fibers _ f hf T _ hi
  filter_upwards [hs] with y hy
  by_cases hz : f y=0
  · simp [PlaneDynamicLocal.integrand, hz]
  · simp only [PlaneDynamicLocal.integrand, norm_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (gradient_fiber_mass k R T d hd hdM y (hy hz).1 (hy hz).2 i)
      (norm_nonneg (f y))

end OQ14.PlaneMaxwellSharp

#print axioms OQ14.PlaneMaxwellSharp.remainder_fiber_mass
#print axioms OQ14.PlaneMaxwellSharp.gradient_fiber_mass
#print axioms OQ14.PlaneMaxwellSharp.remainder_response_mass
#print axioms OQ14.PlaneMaxwellSharp.gradient_response_mass
