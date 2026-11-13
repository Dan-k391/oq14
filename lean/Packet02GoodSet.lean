import ComplexMagneticLocal
import ModalWeightedMode

/-! A frequency-independent domain of absolute convergence for the actual
magnetic convolution. The definition is coordinatewise, so it does not confuse
the sup norm on complex coordinate vectors with the Euclidean spatial norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02GoodSet
open MeasureTheory Metric OQ14.Maxwell OQ14.ModalWeightedMode

def inverseSquare (v : Space) : ℂ := (((‖v‖⁻¹)^2 : ℝ) : ℂ)

def good (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) (x : Space) : Prop :=
  ∀ l : Fin 3, Integrable (fun y =>
    DynamicVolume.source (coefficient n hn) u l y * inverseSquare (x-y))

theorem inverseSquare_locallyIntegrable : LocallyIntegrable inverseSquare := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  have hi : IntegrableOn inverseSquare (closedBall 0 R) :=
    (KernelIntegrability.inverse_norm_sq_integrable_ball R).ofReal
  exact hi.mono_set hR

theorem good_ae (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) :
    ∀ᵐ x ∂(volume : Measure Space), good n hn u x := by
  have h (N : ℕ) (l : Fin 3) : ∀ᵐ x ∂(volume : Measure Space),
      x ∈ closedBall 0 (N : ℝ) →
      Integrable (fun y => DynamicVolume.source (coefficient n hn) u l y *
        inverseSquare (x-y)) := by
    have hi := (DynamicVolume.source_integrable (coefficient n hn) u 1
      (coefficient_support n hn) l).ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ)
      (LocalConvolution.kernel_integrable inverseSquare inverseSquare_locallyIntegrable (N+1))
    filter_upwards [hi] with x hx hxN
    apply hx.congr
    filter_upwards with y
    exact LocalConvolution.kernel_source_eq inverseSquare
      (DynamicVolume.source (coefficient n hn) u l) N 1
      (DynamicVolume.source_zero (coefficient n hn) u 1 (coefficient_support n hn) l) x y hxN
  have hall := ae_all_iff.mpr (fun N => ae_all_iff.mpr (h N))
  filter_upwards [hall] with x hx
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  exact fun l => hx N l (by simpa only [mem_closedBall, dist_zero_right] using hN.le)

theorem gradient_bound_inverseSquare (z : ℂ) (R : ℝ) (v : Space)
    (hv : ‖v‖ ≤ R) (j : Fin 3) :
    ‖ComplexGreenKernel.phiGradient z v j‖ ≤
      ((4 * Real.pi)⁻¹ * Real.exp (‖z‖*R) * (‖z‖*R+1)) * (‖v‖⁻¹)^2 := by
  have hi : ‖v‖⁻¹ ≤ R * (‖v‖⁻¹)^2 := by
    by_cases hz : ‖v‖ = 0
    · simp [hz]
    · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hz)
      have he : ‖v‖ * (‖v‖⁻¹)^2 = ‖v‖⁻¹ := by field_simp; ring
      calc
        _ = ‖v‖ * (‖v‖⁻¹)^2 := he.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hv (sq_nonneg _)
  calc
    _ ≤ (4 * Real.pi)⁻¹ * Real.exp (‖z‖*R) *
        (‖z‖ * ‖v‖⁻¹ + (‖v‖⁻¹)^2) :=
      ComplexMagneticLocal.gradient_bound_ball z R v
        (by simpa only [mem_closedBall, dist_zero_right] using hv) j
    _ ≤ (4 * Real.pi)⁻¹ * Real.exp (‖z‖*R) *
        (‖z‖ * (R * (‖v‖⁻¹)^2) + (‖v‖⁻¹)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add_right (mul_le_mul_of_nonneg_left hi (norm_nonneg z)) _
    _ = _ := by ring

theorem good_gradient_integrable (n : ℝ) (hn : 1 < n)
    (u : VectorFourier.VectorL2) (x : Space) (hx : good n hn u x)
    (z : ℂ) (j l : Fin 3) : Integrable (fun y =>
      DynamicVolume.source (coefficient n hn) u l y *
      ComplexGreenKernel.phiGradient z (x-y) j) := by
  let C := (4 * Real.pi)⁻¹ * Real.exp (‖z‖*(‖x‖+1)) * (‖z‖*(‖x‖+1)+1)
  have hs := DynamicVolume.source_integrable (coefficient n hn) u 1
    (coefficient_support n hn) l
  have hm : AEStronglyMeasurable (fun y =>
      DynamicVolume.source (coefficient n hn) u l y *
      ComplexGreenKernel.phiGradient z (x-y) j) volume := hs.aestronglyMeasurable.mul
    ((ComplexMagneticLocal.gradient_measurable z j).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  apply (((hx l).norm).const_mul C).mono' hm
  filter_upwards with y
  rw [norm_mul, norm_mul]
  by_cases hy : y ∈ closedBall (0 : Space) 1
  · have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    have hxy : ‖x-y‖ ≤ ‖x‖+1 := (norm_sub_le x y).trans (by linarith)
    have hb := gradient_bound_inverseSquare z (‖x‖+1) (x-y) hxy j
    have hnI : ‖inverseSquare (x-y)‖ = (‖x-y‖⁻¹)^2 := by
      simp [inverseSquare]
    rw [hnI]
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hb
      (norm_nonneg (DynamicVolume.source (coefficient n hn) u l y))]
  · simp [DynamicVolume.source_zero (coefficient n hn) u 1
      (coefficient_support n hn) l y hy]

end OQ14.Packet02GoodSet
#print axioms OQ14.Packet02GoodSet.inverseSquare_locallyIntegrable
#print axioms OQ14.Packet02GoodSet.good_ae
#print axioms OQ14.Packet02GoodSet.gradient_bound_inverseSquare
#print axioms OQ14.Packet02GoodSet.good_gradient_integrable
