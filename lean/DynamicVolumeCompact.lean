import L2KernelCompact
import DynamicVolume

/-! # Compactness of the actual weighted dynamic Maxwell volume operator

The truncated physical remainder is genuinely in L2 for every finite radius.
Compactness follows from its L2 translation orbit, actual convolution
identification, finite coordinate sums, and bounded material multiplication.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.DynamicVolumeCompact

open MeasureTheory Metric OQ14.DynamicConvolution
open scoped FourierTransform

theorem remainder_memLp_two_ball (k R : ℝ) (i j : Fin 3) :
    MemLp (fun x : Space => DyadicKernel.remainder k x i j) 2
      (volume.restrict (closedBall 0 R)) := by
  have hm : Measurable (fun x : Space => ‖x‖⁻¹) := continuous_norm.measurable.inv
  have hi : MemLp (fun x : Space => ‖x‖⁻¹) 2 (volume.restrict (closedBall 0 R)) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using KernelIntegrability.inverse_norm_sq_integrable_ball R
  apply hi.of_le_mul (DynamicIntegrability.remainder_measurable k i j).aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_inv, abs_norm] using RealKernelBounds.remainder_bound_all k x i j

theorem kernel_memLp (k R : ℝ) (i j : Fin 3) : MemLp (kernel k R i j) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (remainder_memLp_two_ball k R i j)

def kernelL2 (k R : ℝ) (i j : Fin 3) : ScalarL2 :=
  (kernel_memLp k R i j).toLp (kernel k R i j)

theorem kernelL2_ae (k R : ℝ) (i j : Fin 3) :
    (kernelL2 k R i j : Space → ℂ) =ᵐ[volume] kernel k R i j :=
  (kernel_memLp k R i j).coeFn_toLp

theorem kernelL2_supported (k R : ℝ) (i j : Fin 3) :
    WeakCompactness.SupportedIn (kernelL2 k R i j) (closedBall 0 R) := by
  filter_upwards [kernelL2_ae k R i j] with x hx hn
  rw [hx]
  exact Set.indicator_of_not_mem hn _

theorem operator_congr (q r : Space → ℂ) (hq : Integrable q volume) (hr : Integrable r volume)
    (he : q =ᵐ[volume] r) : L1Convolution.operator q hq = L1Convolution.operator r hr := by
  have hf (ξ : Space) : 𝓕 q ξ = 𝓕 r ξ := by
    rw [HeatFourier.fourier_as_modulate, HeatFourier.fourier_as_modulate]
    apply integral_congr_ae
    filter_upwards [he] with x hx
    simp only [HeatFourier.modulate, hx]
  apply ContinuousLinearMap.ext
  intro u
  apply FourierL2.fourierEquiv.injective
  rw [L1Convolution.operator_fourier, L1Convolution.operator_fourier]
  apply Lp.ext
  filter_upwards [L1Convolution.frequencyProduct_ae q hq (FourierL2.fourierEquiv u),
    L1Convolution.frequencyProduct_ae r hr (FourierL2.fourierEquiv u)] with ξ hqξ hrξ
  rw [hqξ, hrξ, hf]

theorem material_component_supported (c : StaticCoefficient.Coefficient) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorL2) (j : Fin 3) :
    WeakCompactness.SupportedIn (component j (StaticCoefficient.sqrtMultiplier c u))
      (closedBall 0 R) := by
  filter_upwards [StaticNewton.material_source_ae c u j] with x hx hn
  exact hx.trans (DynamicVolume.source_zero c u R hc j x hn)

theorem entry_compact (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i j : Fin 3) :
    IsCompactOperator ((L1Convolution.operator (kernel k (2*R) i j)
      (kernel_integrable k (2*R) i j)).comp ((component j).comp (StaticCoefficient.sqrtMultiplier c))) := by
  have hI : Integrable (kernelL2 k (2*R) i j : Space → ℂ) volume :=
    (kernel_integrable k (2*R) i j).congr (kernelL2_ae k (2*R) i j).symm
  have h := L2KernelCompact.operator_comp_isCompact (kernelL2 k (2*R) i j) hI (2*R) R
    (kernelL2_supported k (2*R) i j) ((component j).comp (StaticCoefficient.sqrtMultiplier c))
    (fun u => material_component_supported c R hc u j)
  rw [operator_congr _ _ hI (kernel_integrable k (2*R) i j) (kernelL2_ae k (2*R) i j)] at h
  exact h

theorem row_compact (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    IsCompactOperator ((row k (2*R) i).comp (StaticCoefficient.sqrtMultiplier c)) := by
  have he : (row k (2*R) i).comp (StaticCoefficient.sqrtMultiplier c) =
      ∑ j : Fin 3, (L1Convolution.operator (kernel k (2*R) i j)
        (kernel_integrable k (2*R) i j)).comp
          ((component j).comp (StaticCoefficient.sqrtMultiplier c)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp [row, ContinuousLinearMap.sum_apply]
  rw [he]
  simpa only [Fin.sum_univ_three, ContinuousLinearMap.coe_add] using
    ((entry_compact c k R hc i 0).add (entry_compact c k R hc i 1)).add
      (entry_compact c k R hc i 2)

theorem source_operator_compact (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    IsCompactOperator ((operator k (2*R)).comp (StaticCoefficient.sqrtMultiplier c)) := by
  have he : (operator k (2*R)).comp (StaticCoefficient.sqrtMultiplier c) =
      ∑ i : Fin 3, (DynamicConvolution.insert i).comp
        ((row k (2*R) i).comp (StaticCoefficient.sqrtMultiplier c)) := by
    apply ContinuousLinearMap.ext
    intro u
    simp [operator, ContinuousLinearMap.sum_apply]
  rw [he]
  have hi (i : Fin 3) := (row_compact c k R hc i).clm_comp (DynamicConvolution.insert i)
  simpa only [Fin.sum_univ_three, ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_comp] using
    ((hi 0).add (hi 1)).add (hi 2)

/-- The physical weighted dynamic remainder is compact for every finite
material support radius; no small-volume hypothesis is used. -/
theorem weightedRemainder_compact (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    IsCompactOperator (DynamicVolume.weightedRemainder c k R) :=
  (source_operator_compact c k R hc).clm_comp (StaticCoefficient.sqrtMultiplier c)

end OQ14.DynamicVolumeCompact

#print axioms OQ14.DynamicVolumeCompact.remainder_memLp_two_ball
#print axioms OQ14.DynamicVolumeCompact.kernel_memLp
#print axioms OQ14.DynamicVolumeCompact.kernelL2_ae
#print axioms OQ14.DynamicVolumeCompact.kernelL2_supported
#print axioms OQ14.DynamicVolumeCompact.operator_congr
#print axioms OQ14.DynamicVolumeCompact.material_component_supported
#print axioms OQ14.DynamicVolumeCompact.entry_compact
#print axioms OQ14.DynamicVolumeCompact.row_compact
#print axioms OQ14.DynamicVolumeCompact.source_operator_compact
#print axioms OQ14.DynamicVolumeCompact.weightedRemainder_compact
