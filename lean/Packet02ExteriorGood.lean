import Packet02GoodSet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02ExteriorGood
open MeasureTheory Metric OQ14.Maxwell OQ14.ModalWeightedMode OQ14.Packet02GoodSet

theorem exterior_good (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (x : Space) (hx : 1 < ‖x‖) : good n hn u x := by
  intro l
  have hs := DynamicVolume.source_integrable (coefficient n hn) u 1 (coefficient_support n hn) l
  have hm : AEStronglyMeasurable (fun y => DynamicVolume.source (coefficient n hn) u l y *
      inverseSquare (x-y)) volume := by
    apply hs.aestronglyMeasurable.mul
    have hmeas : Measurable (fun y : Space => inverseSquare (x-y)) := by
      unfold inverseSquare
      fun_prop
    exact hmeas.aestronglyMeasurable
  apply (hs.norm.mul_const (((‖x‖-1)⁻¹)^2)).mono' hm
  filter_upwards with y
  by_cases hy : y ∈ closedBall (0 : Space) 1
  · have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    have hpos : 0 < ‖x‖-1 := by linarith
    have hdist : ‖x‖-1 ≤ ‖x-y‖ := by
      have h := norm_sub_le x y
      have h' := norm_sub_le (x-y) (-y)
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at h'
      linarith
    have hinv : ‖x-y‖⁻¹ ≤ (‖x‖-1)⁻¹ := inv_le_inv₀ (hpos.trans_le hdist) hpos |>.2 hdist
    have hsq : (‖x-y‖⁻¹)^2 ≤ ((‖x‖-1)⁻¹)^2 := by
      nlinarith [inv_nonneg.mpr (norm_nonneg (x-y)), inv_nonneg.mpr hpos.le]
    rw [norm_mul]
    have hi : ‖inverseSquare (x-y)‖ = (‖x-y‖⁻¹)^2 := by
      simp only [inverseSquare, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (sq_nonneg (‖x-y‖⁻¹))
    rw [hi]
    exact mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
  · simp [DynamicVolume.source_zero (coefficient n hn) u 1 (coefficient_support n hn) l y hy]

#print axioms OQ14.Packet02ExteriorGood.exterior_good
end OQ14.Packet02ExteriorGood
