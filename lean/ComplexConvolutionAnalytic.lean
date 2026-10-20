import ComplexKernelAnalytic
import L1KernelOperator
import VolumeFredholm

/-! # The actual analytic compact volume pencil

The actual L2 kernel family is mapped through bounded-linear convolution
dependence, coordinate sums and material multipliers. The physical real
frequency family is recovered exactly. The dynamic remainder vanishes at zero.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ComplexConvolutionAnalytic

open MeasureTheory Metric OQ14.DynamicConvolution
open OQ14.StaticCoefficient (Coefficient)

theorem kernel_integrable (k : ℂ) (R : ℝ) (i j : Fin 3) :
    Integrable (ComplexKernelAnalytic.kernel k R i j) :=
  (integrable_indicator_iff measurableSet_closedBall).mpr
    (ComplexDynamicKernel.remainder_integrable_ball k R i j)

def entry (k : ℂ) (R : ℝ) (i j : Fin 3) : ScalarL2 →L[ℂ] ScalarL2 :=
  L1KernelOperator.localOperator R (ComplexKernelAnalytic.kernelL2 k R i j)

theorem entry_eq (k : ℂ) (R : ℝ) (i j : Fin 3) :
    entry k R i j = L1Convolution.operator (ComplexKernelAnalytic.kernel k R i j)
      (kernel_integrable k R i j) := by
  apply L1KernelOperator.localOperator_toL1 R _ _ _
    (ComplexKernelAnalytic.kernelL2_ae k R i j)
  intro x hx
  exact Set.indicator_of_not_mem hx _

theorem entry_spatial_ae (k : ℂ) (R : ℝ) (i j : Fin 3) (F : ScalarL2)
    (hF : Integrable (F : Space → ℂ)) :
    entry k R i j F =ᵐ[volume]
      HeatFourier.convolution (ComplexKernelAnalytic.kernel k R i j) F := by
  rw [entry_eq]
  exact L1Convolution.operator_ae_convolution _ _ F hF

theorem entry_differentiable (R : ℝ) (hR : 0 ≤ R) (i j : Fin 3) :
    Differentiable ℂ (fun k => entry k R i j) :=
  (L1KernelOperator.localOperator R).differentiable.comp
    (ComplexKernelAnalytic.kernel_differentiable R hR i j)

theorem entry_analyticAt (k : ℂ) (R : ℝ) (hR : 0 ≤ R) (i j : Fin 3) :
    AnalyticAt ℂ (fun w => entry w R i j) k :=
  (entry_differentiable R hR i j).analyticAt k

def row (k : ℂ) (R : ℝ) (i : Fin 3) : VectorL2 →L[ℂ] ScalarL2 :=
  ∑ j : Fin 3, (entry k R i j).comp (component j)

def operator (k : ℂ) (R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  ∑ i : Fin 3, (insert i).comp (row k R i)

theorem row_differentiable (R : ℝ) (hR : 0 ≤ R) (i : Fin 3) :
    Differentiable ℂ (fun k => row k R i) := by
  apply Differentiable.sum
  intro j _
  exact (entry_differentiable R hR i j).clm_comp (differentiable_const (component j))

theorem operator_differentiable (R : ℝ) (hR : 0 ≤ R) :
    Differentiable ℂ (fun k => operator k R) := by
  apply Differentiable.sum
  intro i _
  exact (differentiable_const (insert i)).clm_comp (row_differentiable R hR i)

theorem operator_analyticAt (k : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    AnalyticAt ℂ (fun w => operator w R) k :=
  (operator_differentiable R hR).analyticAt k

def weightedRemainder (c : Coefficient) (k : ℂ) (R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  (StaticCoefficient.sqrtMultiplier c).comp
    ((operator k (2*R)).comp (StaticCoefficient.sqrtMultiplier c))

def volumeBlock (c : Coefficient) (k : ℂ) (R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  StaticNewton.volumeBlock c - weightedRemainder c k R

def compactPart (c : Coefficient) (k : ℂ) (R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  (Ring.inverse (StaticNewton.volumeBlock c)).comp (weightedRemainder c k R)

def pencil (c : Coefficient) (k : ℂ) (R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  CompactPerturbation.defect (compactPart c k R)

theorem weightedRemainder_differentiable (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) :
    Differentiable ℂ (fun k => weightedRemainder c k R) :=
  (differentiable_const (StaticCoefficient.sqrtMultiplier c)).clm_comp
    ((operator_differentiable (2*R) (by positivity)).clm_comp
      (differentiable_const (StaticCoefficient.sqrtMultiplier c)))

theorem volumeBlock_differentiable (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) :
    Differentiable ℂ (fun k => volumeBlock c k R) :=
  (differentiable_const (StaticNewton.volumeBlock c)).sub
    (weightedRemainder_differentiable c R hR)

theorem compactPart_differentiable (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) :
    Differentiable ℂ (fun k => compactPart c k R) :=
  (differentiable_const (Ring.inverse (StaticNewton.volumeBlock c))).clm_comp
    (weightedRemainder_differentiable c R hR)

theorem pencil_analyticAt (c : Coefficient) (k : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    AnalyticAt ℂ (fun w => pencil c w R) k :=
  ((differentiable_const (1 : VectorL2 →L[ℂ] VectorL2)).sub
    (compactPart_differentiable c R hR)).analyticAt k

theorem entry_ofReal (k R : ℝ) (i j : Fin 3) :
    entry (k : ℂ) R i j = L1Convolution.operator (DynamicConvolution.kernel k R i j)
      (DynamicConvolution.kernel_integrable k R i j) := by rw [entry_eq]; rfl

theorem row_ofReal (k R : ℝ) (i : Fin 3) :
    row (k : ℂ) R i = DynamicConvolution.row k R i := by
  unfold row DynamicConvolution.row
  simp_rw [entry_ofReal]

theorem operator_ofReal (k R : ℝ) :
    operator (k : ℂ) R = DynamicConvolution.operator k R := by
  unfold operator DynamicConvolution.operator
  simp_rw [row_ofReal]

theorem weightedRemainder_ofReal (c : Coefficient) (k R : ℝ) :
    weightedRemainder c (k : ℂ) R = DynamicVolume.weightedRemainder c k R := by
  unfold weightedRemainder DynamicVolume.weightedRemainder
  rw [operator_ofReal]

theorem volumeBlock_ofReal (c : Coefficient) (k R : ℝ) :
    volumeBlock c (k : ℂ) R = DynamicVolume.volumeBlock c k R := by
  unfold volumeBlock DynamicVolume.volumeBlock
  rw [weightedRemainder_ofReal]

theorem compactPart_ofReal (c : Coefficient) (k R : ℝ) :
    compactPart c (k : ℂ) R = VolumeFredholm.compactPart c k R := by
  unfold compactPart VolumeFredholm.compactPart
  rw [weightedRemainder_ofReal]

theorem remainder_frequency_zero (x : Space) (i j : Fin 3) :
    ComplexDynamicKernel.remainder 0 x i j = 0 := by
  simp [ComplexDynamicKernel.remainder, ComplexDynamicKernel.dyadic]

theorem kernelL2_frequency_zero (R : ℝ) (i j : Fin 3) :
    ComplexKernelAnalytic.kernelL2 0 R i j = 0 := by
  apply Lp.ext
  filter_upwards [ComplexKernelAnalytic.kernelL2_ae 0 R i j] with x hx
  rw [hx]
  simp [ComplexKernelAnalytic.kernel, remainder_frequency_zero]

theorem entry_zero (R : ℝ) (i j : Fin 3) : entry 0 R i j = 0 := by
  unfold entry
  rw [kernelL2_frequency_zero, map_zero]

theorem operator_zero (R : ℝ) : operator 0 R = 0 := by simp [operator, row, entry_zero]

theorem weightedRemainder_zero (c : Coefficient) (R : ℝ) : weightedRemainder c 0 R = 0 := by
  simp [weightedRemainder, operator_zero]

theorem compactPart_zero (c : Coefficient) (R : ℝ) : compactPart c 0 R = 0 := by
  simp [compactPart, weightedRemainder_zero]

theorem pencil_zero (c : Coefficient) (R : ℝ) : pencil c 0 R = 1 := by
  simp [pencil, CompactPerturbation.defect, compactPart_zero]

theorem volumeBlock_zero_isUnit (c : Coefficient) (R : ℝ) : IsUnit (volumeBlock c 0 R) := by
  simpa [volumeBlock, weightedRemainder_zero] using StaticNewton.volumeBlock_isUnit c

theorem preconditioned_eq (c : Coefficient) (k : ℂ) (R : ℝ) :
    Ring.inverse (StaticNewton.volumeBlock c) * volumeBlock c k R = pencil c k R := by
  change Ring.inverse (StaticNewton.volumeBlock c) *
    (StaticNewton.volumeBlock c - weightedRemainder c k R) =
      1 - Ring.inverse (StaticNewton.volumeBlock c) * weightedRemainder c k R
  rw [mul_sub, Ring.inverse_mul_cancel _ (StaticNewton.volumeBlock_isUnit c)]

theorem weightedRemainder_analyticAt (c : Coefficient) (k : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    AnalyticAt ℂ (fun w => weightedRemainder c w R) k :=
  (weightedRemainder_differentiable c R hR).analyticAt k

theorem volumeBlock_analyticAt (c : Coefficient) (k : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    AnalyticAt ℂ (fun w => volumeBlock c w R) k :=
  (volumeBlock_differentiable c R hR).analyticAt k

theorem compactPart_analyticAt (c : Coefficient) (k : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    AnalyticAt ℂ (fun w => compactPart c w R) k :=
  (compactPart_differentiable c R hR).analyticAt k

theorem entry_compact (c : Coefficient) (k : ℂ) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i j : Fin 3) :
    IsCompactOperator ((entry k (2*R) i j).comp
      ((component j).comp (StaticCoefficient.sqrtMultiplier c))) := by
  have hI : Integrable (ComplexKernelAnalytic.kernelL2 k (2*R) i j : Space → ℂ) volume :=
    (kernel_integrable k (2*R) i j).congr (ComplexKernelAnalytic.kernelL2_ae k (2*R) i j).symm
  have h := L2KernelCompact.operator_comp_isCompact
    (ComplexKernelAnalytic.kernelL2 k (2*R) i j) hI (2*R) R
    (ComplexKernelAnalytic.kernelL2_supported k (2*R) i j)
    ((component j).comp (StaticCoefficient.sqrtMultiplier c))
    (fun u => DynamicVolumeCompact.material_component_supported c R hc u j)
  rw [L1KernelOperator.operator_congr _ _ hI (kernel_integrable k (2*R) i j)
    (ComplexKernelAnalytic.kernelL2_ae k (2*R) i j)] at h
  rwa [← entry_eq] at h

theorem row_compact (c : Coefficient) (k : ℂ) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    IsCompactOperator ((row k (2*R) i).comp (StaticCoefficient.sqrtMultiplier c)) := by
  have he : (row k (2*R) i).comp (StaticCoefficient.sqrtMultiplier c) =
      ∑ j : Fin 3, (entry k (2*R) i j).comp
        ((component j).comp (StaticCoefficient.sqrtMultiplier c)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp [row, ContinuousLinearMap.sum_apply]
  rw [he]
  simpa only [Fin.sum_univ_three, ContinuousLinearMap.coe_add] using
    ((entry_compact c k R hc i 0).add (entry_compact c k R hc i 1)).add
      (entry_compact c k R hc i 2)

theorem source_operator_compact (c : Coefficient) (k : ℂ) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    IsCompactOperator ((operator k (2*R)).comp (StaticCoefficient.sqrtMultiplier c)) := by
  have he : (operator k (2*R)).comp (StaticCoefficient.sqrtMultiplier c) =
      ∑ i : Fin 3, (insert i).comp
        ((row k (2*R) i).comp (StaticCoefficient.sqrtMultiplier c)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp [operator, ContinuousLinearMap.sum_apply]
  rw [he]
  have hi (i : Fin 3) := (row_compact c k R hc i).clm_comp (insert i)
  simpa only [Fin.sum_univ_three, ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_comp] using
    ((hi 0).add (hi 1)).add (hi 2)

theorem weightedRemainder_compact (c : Coefficient) (k : ℂ) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    IsCompactOperator (weightedRemainder c k R) :=
  (source_operator_compact c k R hc).clm_comp (StaticCoefficient.sqrtMultiplier c)

theorem compactPart_compact (c : Coefficient) (k : ℂ) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    IsCompactOperator (compactPart c k R) :=
  (weightedRemainder_compact c k R hc).clm_comp (Ring.inverse (StaticNewton.volumeBlock c))

theorem volumeBlock_factor (c : Coefficient) (k : ℂ) (R : ℝ) :
    volumeBlock c k R = StaticNewton.volumeBlock c * pencil c k R := by
  rw [← preconditioned_eq, ← mul_assoc,
    Ring.mul_inverse_cancel _ (StaticNewton.volumeBlock_isUnit c), one_mul]

theorem pencil_zero_isUnit (c : Coefficient) (R : ℝ) : IsUnit (pencil c 0 R) := by
  rw [pencil_zero]
  exact isUnit_one

end OQ14.ComplexConvolutionAnalytic

#print axioms OQ14.ComplexConvolutionAnalytic.kernel_integrable
#print axioms OQ14.ComplexConvolutionAnalytic.entry_eq
#print axioms OQ14.ComplexConvolutionAnalytic.entry_spatial_ae
#print axioms OQ14.ComplexConvolutionAnalytic.entry_differentiable
#print axioms OQ14.ComplexConvolutionAnalytic.entry_analyticAt
#print axioms OQ14.ComplexConvolutionAnalytic.row_differentiable
#print axioms OQ14.ComplexConvolutionAnalytic.operator_differentiable
#print axioms OQ14.ComplexConvolutionAnalytic.operator_analyticAt
#print axioms OQ14.ComplexConvolutionAnalytic.weightedRemainder_differentiable
#print axioms OQ14.ComplexConvolutionAnalytic.volumeBlock_differentiable
#print axioms OQ14.ComplexConvolutionAnalytic.compactPart_differentiable
#print axioms OQ14.ComplexConvolutionAnalytic.pencil_analyticAt
#print axioms OQ14.ComplexConvolutionAnalytic.entry_ofReal
#print axioms OQ14.ComplexConvolutionAnalytic.row_ofReal
#print axioms OQ14.ComplexConvolutionAnalytic.operator_ofReal
#print axioms OQ14.ComplexConvolutionAnalytic.weightedRemainder_ofReal
#print axioms OQ14.ComplexConvolutionAnalytic.volumeBlock_ofReal
#print axioms OQ14.ComplexConvolutionAnalytic.compactPart_ofReal
#print axioms OQ14.ComplexConvolutionAnalytic.remainder_frequency_zero
#print axioms OQ14.ComplexConvolutionAnalytic.kernelL2_frequency_zero
#print axioms OQ14.ComplexConvolutionAnalytic.entry_zero
#print axioms OQ14.ComplexConvolutionAnalytic.operator_zero
#print axioms OQ14.ComplexConvolutionAnalytic.weightedRemainder_zero
#print axioms OQ14.ComplexConvolutionAnalytic.compactPart_zero
#print axioms OQ14.ComplexConvolutionAnalytic.pencil_zero
#print axioms OQ14.ComplexConvolutionAnalytic.volumeBlock_zero_isUnit
#print axioms OQ14.ComplexConvolutionAnalytic.preconditioned_eq
#print axioms OQ14.ComplexConvolutionAnalytic.weightedRemainder_analyticAt
#print axioms OQ14.ComplexConvolutionAnalytic.volumeBlock_analyticAt
#print axioms OQ14.ComplexConvolutionAnalytic.compactPart_analyticAt
#print axioms OQ14.ComplexConvolutionAnalytic.entry_compact
#print axioms OQ14.ComplexConvolutionAnalytic.row_compact
#print axioms OQ14.ComplexConvolutionAnalytic.source_operator_compact
#print axioms OQ14.ComplexConvolutionAnalytic.weightedRemainder_compact
#print axioms OQ14.ComplexConvolutionAnalytic.compactPart_compact
#print axioms OQ14.ComplexConvolutionAnalytic.volumeBlock_factor
#print axioms OQ14.ComplexConvolutionAnalytic.pencil_zero_isUnit
