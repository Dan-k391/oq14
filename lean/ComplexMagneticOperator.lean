import ComplexMagneticAnalytic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexMagneticOperator
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.ComplexGreenKernel
  OQ14.ComplexMagneticAnalytic
open scoped Topology
abbrev ScalarL2 := FourierL2.ScalarL2

def staticKernel (R : ℝ) (j : Fin 3) : Space → ℂ :=
  (closedBall 0 R).indicator (fun x => phiGradient 0 x j)

def fullKernel (z : ℂ) (R : ℝ) (j : Fin 3) : Space → ℂ :=
  (closedBall 0 R).indicator (fun x => phiGradient z x j)

theorem static_integrable (R : ℝ) (j : Fin 3) : Integrable (staticKernel R j) :=
  (integrable_indicator_iff measurableSet_closedBall).mpr (ComplexMagneticLocal.gradient_integrable_ball 0 R j)

theorem full_integrable (z : ℂ) (R : ℝ) (j : Fin 3) : Integrable (fullKernel z R j) :=
  (integrable_indicator_iff measurableSet_closedBall).mpr (ComplexMagneticLocal.gradient_integrable_ball z R j)

theorem diff_integrable (z : ℂ) (R : ℝ) (j : Fin 3) : Integrable (kernel z R j) := by
  have h := (kernel_memLp z R j)
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_ne_top
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (((memLp_indicator_iff_restrict measurableSet_closedBall).mp h).integrable (by norm_num))

def entry (z : ℂ) (R : ℝ) (j : Fin 3) : ScalarL2 →L[ℂ] ScalarL2 :=
  L1Convolution.operator (staticKernel R j) (static_integrable R j) +
    L1KernelOperator.localOperator R (kernelL2 z R j)

theorem entry_differentiable (R : ℝ) (j : Fin 3) : Differentiable ℂ (fun z => entry z R j) := by
  unfold entry
  exact (differentiable_const _).add ((L1KernelOperator.localOperator R).differentiable.comp (kernel_differentiable R j))

theorem entry_eq (z : ℂ) (R : ℝ) (j : Fin 3) :
    entry z R j = L1Convolution.operator (fullKernel z R j) (full_integrable z R j) := by
  have h := L1KernelOperator.localOperator_toL1 R (kernelL2 z R j) (kernel z R j)
    (diff_integrable z R j) (kernel_memLp z R j).coeFn_toLp
    (fun x hx => indicator_of_not_mem hx _)
  unfold entry
  rw [h, ← L1KernelOperator.operator_add]
  apply L1KernelOperator.operator_congr
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) R
  · simp [staticKernel, fullKernel, kernel, gradientDifference, hx]
  · simp [staticKernel, fullKernel, kernel, hx]

theorem entry_ae (z : ℂ) (R : ℝ) (j : Fin 3) (F : ScalarL2) (hF : Integrable (F : Space → ℂ)) :
    entry z R j F =ᵐ[volume] HeatFourier.convolution (fullKernel z R j) F := by
  rw [entry_eq]
  exact L1Convolution.operator_ae_convolution _ _ F hF

#print axioms OQ14.ComplexMagneticOperator.entry_differentiable
#print axioms OQ14.ComplexMagneticOperator.entry_eq
#print axioms OQ14.ComplexMagneticOperator.entry_ae
end OQ14.ComplexMagneticOperator
