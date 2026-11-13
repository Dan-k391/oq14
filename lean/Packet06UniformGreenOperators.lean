import Packet06ComplexHessian
import ComplexMagneticOperator
import ComplexConvolutionAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06UniformGreenOperators
open MeasureTheory Metric Set Maxwell ComplexGreenKernel
open scoped Topology
abbrev ScalarL2 := FourierL2.ScalarL2

def phiOperator (z : ℂ) (T : ℝ) : ScalarL2 →L[ℂ] ScalarL2 :=
  LocalConvolution.operator (phi z) (Packet06ComplexScalarKernel.phi_locallyIntegrable z) T

def gradientOperator (z : ℂ) (T : ℝ) (j : Fin 3) : ScalarL2 →L[ℂ] ScalarL2 :=
  LocalConvolution.operator (fun x => phiGradient z x j) (ComplexMagneticLocal.gradient_locallyIntegrable z j) T

def hessianOperator (z : ℂ) (T : ℝ) (i j : Fin 3) : ScalarL2 →L[ℂ] ScalarL2 :=
  LocalConvolution.operator (fun x => Packet06ComplexHessian.hessianDifference z x i j)
    (Packet06ComplexHessian.hessian_locallyIntegrable z i j) T

/-- Scalar Green convolution is bounded uniformly on a compact frequency ball. -/
theorem phi_uniform (T Z : ℝ) (hT : 0 ≤ T) (_hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ Z → ‖phiOperator z T‖ ≤ C := by
  let q := LocalConvolution.kernel (phi 0) T
  let C := Real.exp (Z*T) * L1Convolution.mass q
  refine ⟨C,mul_nonneg (Real.exp_pos _).le (L1Convolution.mass_nonnegative q),?_⟩
  intro z hz
  apply (L1Convolution.operator_norm_le _ _).trans
  unfold L1Convolution.mass
  have hq : Integrable q := LocalConvolution.kernel_integrable (phi 0)
    (Packet06ComplexScalarKernel.phi_locallyIntegrable 0) T
  have hzq : Integrable (LocalConvolution.kernel (phi z) T) := LocalConvolution.kernel_integrable (phi z)
    (Packet06ComplexScalarKernel.phi_locallyIntegrable z) T
  change (∫ x, ‖LocalConvolution.kernel (phi z) T x‖) ≤ Real.exp (Z*T) * ∫ x, ‖q x‖
  rw [← integral_const_mul]
  apply integral_mono_ae hzq.norm (hq.norm.const_mul _)
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) T
  · have h := Packet06ComplexScalarKernel.phi_bound_ball z T x hx
    have he : Real.exp (‖z‖*T) ≤ Real.exp (Z*T) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz hT)
    have hp : phi 0 x = GreenKernel.phi 0 x := by rfl
    simpa only [LocalConvolution.kernel,indicator_of_mem hx,q,hp] using
      h.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  · simp [LocalConvolution.kernel,q,hx]

/-- The full gradient convolution agrees with the analytic magnetic entry. -/
theorem gradient_eq (z : ℂ) (T : ℝ) (j : Fin 3) :
    gradientOperator z T j = ComplexMagneticOperator.entry z T j := by
  rw [ComplexMagneticOperator.entry_eq]
  rfl

/-- The analytic gradient entries are uniformly bounded on compact frequency balls. -/
theorem gradient_uniform (T Z : ℝ) (_hZ : 0 ≤ Z) (j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ Z → ‖gradientOperator z T j‖ ≤ C := by
  have hc := (ComplexMagneticOperator.entry_differentiable T j).continuous.norm
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : ℂ) Z).bddAbove_image hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z hz
  rw [gradient_eq]
  exact (hC ⟨z,by simpa only [mem_closedBall,dist_zero_right] using hz,rfl⟩).trans (le_max_left _ _)

/-- The Hessian-difference operator is exactly the dynamic dyadic entry minus
its scalar Green diagonal term. -/
theorem hessian_eq (z : ℂ) (T : ℝ) (i j : Fin 3) :
    hessianOperator z T i j = ComplexConvolutionAnalytic.entry z T i j +
      (-(z^2 * (if i = j then 1 else 0))) • phiOperator z T := by
  let q := LocalConvolution.kernel (phi z) T
  let r := ComplexKernelAnalytic.kernel z T i j
  let a : ℂ := -(z^2 * (if i = j then 1 else 0))
  have hq : Integrable q := LocalConvolution.kernel_integrable (phi z)
    (Packet06ComplexScalarKernel.phi_locallyIntegrable z) T
  have hr : Integrable r := ComplexConvolutionAnalytic.kernel_integrable z T i j
  rw [ComplexConvolutionAnalytic.entry_eq]
  change L1Convolution.operator _ _ = L1Convolution.operator r hr + a • L1Convolution.operator q hq
  rw [← L1KernelOperator.operator_smul q hq a, ← L1KernelOperator.operator_add r (a • q) hr (hq.smul a)]
  apply L1KernelOperator.operator_congr
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) T
  · simp only [LocalConvolution.kernel,indicator_of_mem hx,ComplexKernelAnalytic.kernel,
      Packet06ComplexHessian.hessianDifference,Pi.add_apply,Pi.smul_apply,smul_eq_mul,r,q,a]
    ring
  · simp [LocalConvolution.kernel,ComplexKernelAnalytic.kernel,r,q,hx]

/-- The actual Hessian-difference entries have one bound on every compact
frequency ball. -/
theorem hessian_uniform (T Z : ℝ) (hT : 0 ≤ T) (hZ : 0 ≤ Z) (i j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ Z → ‖hessianOperator z T i j‖ ≤ C := by
  obtain ⟨P,hP,hphi⟩ := phi_uniform T Z hT hZ
  have hc := (ComplexConvolutionAnalytic.entry_differentiable T hT i j).continuous.norm
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : ℂ) Z).bddAbove_image hc.continuousOn
  let C := max B 0 + Z^2*P
  refine ⟨C,add_nonneg (le_max_right _ _) (mul_nonneg (sq_nonneg Z) hP),?_⟩
  intro z hz
  have hb : ‖ComplexConvolutionAnalytic.entry z T i j‖ ≤ max B 0 :=
    (hB ⟨z,by simpa only [mem_closedBall,dist_zero_right] using hz,rfl⟩).trans (le_max_left _ _)
  have hz2 : ‖z‖^2 ≤ Z^2 := by nlinarith [norm_nonneg z]
  rw [hessian_eq]
  calc
    _ ≤ ‖ComplexConvolutionAnalytic.entry z T i j‖ +
        ‖(-(z^2 * (if i = j then 1 else 0))) • phiOperator z T‖ := norm_add_le _ _
    _ ≤ max B 0 + Z^2*P := by
      have hδ : ‖(if i = j then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
      have ha : ‖-(z^2 * (if i = j then (1 : ℂ) else 0))‖ ≤ Z^2 := by
        rw [norm_neg,norm_mul,norm_pow]
        exact (mul_le_of_le_one_right (sq_nonneg _) hδ).trans hz2
      have hs := norm_smul_le (-(z^2 * (if i = j then (1 : ℂ) else 0))) (phiOperator z T)
      exact add_le_add hb (hs.trans (mul_le_mul ha (hphi z hz) (norm_nonneg _) (sq_nonneg Z)))
    _ = C := rfl

#print axioms OQ14.Packet06UniformGreenOperators.hessian_eq
#print axioms OQ14.Packet06UniformGreenOperators.hessian_uniform
#print axioms OQ14.Packet06UniformGreenOperators.phi_uniform
#print axioms OQ14.Packet06UniformGreenOperators.gradient_eq
#print axioms OQ14.Packet06UniformGreenOperators.gradient_uniform
end OQ14.Packet06UniformGreenOperators
