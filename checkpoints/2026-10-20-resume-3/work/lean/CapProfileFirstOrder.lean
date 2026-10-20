import SphereCapWeak

/-! First-order integration by parts for the actual continuous cap profile. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.CapProfileFirstOrder
open MeasureTheory Set OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology

def rightSlope (a t z : ℝ) : ℝ :=
  if z < -t then negativeD a t z else if z < t then interiorD a t z else exteriorD a t z

theorem rightSlope_ae (a t : ℝ) : rightSlope a t =ᵐ[volume] CapSturmLiouville.slope a t := by
  have h : ∀ᵐ z : ℝ, z ≠ t := by
    simp only [ae_iff,not_not,setOf_eq_eq_singleton,measure_singleton]
  filter_upwards [h] with z hz
  by_cases hL : z < -t
  · simp [rightSlope,CapSturmLiouville.slope,hL]
  · by_cases hM : z < t
    · simp [rightSlope,CapSturmLiouville.slope,hL,hM,hM.le]
    · simp [rightSlope,CapSturmLiouville.slope,hL,hM,show ¬z ≤ t from not_le.mpr (lt_of_le_of_ne (le_of_not_gt hM) hz.symm)]

theorem profile_hasDeriv_right (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivWithinAt (profile a t) (rightSlope a t z) (Ioi z) z := by
  by_cases hL : z < -t
  · rw [rightSlope,if_pos hL]
    apply (negative_hasDerivAt a t z ha (left_argument t z ht ht1 ⟨hz.1.le,hL.le⟩)).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hL)] with y hy
      simp [profile,show y < -t from hy]
    · simp [profile,hL]
  · by_cases hM : z < t
    · rw [rightSlope,if_neg hL,if_pos hM]
      apply (interior_hasDerivAt a t z ha (middle_argument t z ht1 ⟨le_of_not_gt hL,hM.le⟩)).hasDerivWithinAt.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hM)] with y hy hyt
        have hyl : ¬y < -t := by have hy' : z < y := hy; linarith
        simp [profile,hyl,show y ≤ t from le_of_lt hyt]
      · exact profile_middle a t z ⟨le_of_not_gt hL,hM.le⟩
    · rw [rightSlope,if_neg hL,if_neg hM]
      apply (exterior_hasDerivAt a t z ha (right_argument t z ht ht1 ⟨le_of_not_gt hM,hz.2.le⟩)).hasDerivWithinAt.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hyt : t < y := lt_of_le_of_lt (le_of_not_gt hM) hy
        simp [profile,not_le.mpr hyt,show ¬y < -t by linarith]
      · exact profile_right a t z ht ⟨le_of_not_gt hM,hz.2.le⟩

theorem slope_intervalIntegrable (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) :
    IntervalIntegrable (CapSturmLiouville.slope a t) volume (-1) 1 := by
  have hL : ContinuousOn (negativeD a t) (Icc (-1 : ℝ) (-t)) :=
    fun z hz => (negativeD_hasDerivAt a t z ha (left_argument t z ht ht1 hz)).continuousAt.continuousWithinAt
  have hM : ContinuousOn (interiorD a t) (Icc (-t) t) :=
    fun z hz => (interiorD_hasDerivAt a t z ha (middle_argument t z ht1 hz)).continuousAt.continuousWithinAt
  have hR : ContinuousOn (exteriorD a t) (Icc t 1) :=
    fun z hz => (exteriorD_hasDerivAt a t z ha (right_argument t z ht ht1 hz)).continuousAt.continuousWithinAt
  have iL : IntervalIntegrable (CapSturmLiouville.slope a t) volume (-1) (-t) := by
    apply (hL.intervalIntegrable_of_Icc (by linarith)).congr
    have hn : ∀ᵐ z : ℝ, z ≠ -t := by
      simp only [ae_iff,not_not,setOf_eq_eq_singleton,measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_uIoc,ae_restrict_of_ae hn] with z hz hnz
    have hz' : z ∈ Ioc (-1 : ℝ) (-t) := by simpa [uIoc_of_le (show (-1 : ℝ) ≤ -t by linarith)] using hz
    have hzt : z < -t := lt_of_le_of_ne hz'.2 hnz
    simp [CapSturmLiouville.slope,hzt]
  have iM : IntervalIntegrable (CapSturmLiouville.slope a t) volume (-t) t := by
    apply (hM.intervalIntegrable_of_Icc (by linarith)).congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
    have hz' : z ∈ Ioc (-t) t := by simpa [uIoc_of_le (show -t ≤ t by linarith)] using hz
    simp [CapSturmLiouville.slope,not_lt.mpr hz'.1.le,hz'.2]
  have iR : IntervalIntegrable (CapSturmLiouville.slope a t) volume t 1 := by
    apply (hR.intervalIntegrable_of_Icc ht1.le).congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
    have hz' : z ∈ Ioc t 1 := by simpa [uIoc_of_le ht1.le] using hz
    simp [CapSturmLiouville.slope,not_le.mpr hz'.1,show ¬z < -t by linarith [hz'.1]]
  exact (iL.trans iM).trans iR

theorem profile_ibp (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (v vD : ℝ → ℝ)
    (hv : ContinuousOn v (Icc (-1 : ℝ) 1))
    (hD : ∀ z ∈ Ioo (-1 : ℝ) 1, HasDerivAt v (vD z) z)
    (hi : IntervalIntegrable vD volume (-1) 1) :
    (∫ z in (-1 : ℝ)..1, profile a t z*vD z) =
      profile a t 1*v 1-profile a t (-1)*v (-1)-
      ∫ z in (-1 : ℝ)..1, CapSturmLiouville.slope a t z*v z := by
  have ir : IntervalIntegrable (rightSlope a t) volume (-1) 1 :=
    (slope_intervalIntegrable a t ha ht ht1).congr (ae_restrict_of_ae (rightSlope_ae a t).symm)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (a := (-1 : ℝ)) (b := 1) (u := profile a t) (u' := rightSlope a t) (v := v) (v' := vD)
    (by simpa using profile_continuousOn a t ha ht ht1) (by simpa using hv)
    (fun z hz => profile_hasDeriv_right a t z ha ht ht1 (by simpa using hz))
    (fun z hz => (hD z (by simpa using hz)).hasDerivWithinAt) ir hi
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [rightSlope_ae a t] with z hz
  intro _
  rw [hz]

end OQ14.CapProfileFirstOrder
