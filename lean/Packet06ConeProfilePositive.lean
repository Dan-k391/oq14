import Packet06ConePolePositive
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeProfilePositive
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereCapH1 OQ14.SphereCapWeak
  OQ14.AngularPower OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology

theorem profile_positive (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht0 : (1/2 : ℝ) ≤ t) (ht1 : t < 1) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    0 < profile a t z := by
  have ht : 0 < t := by linarith
  have hpt := Packet06ConePolePositive.pole_positive_near_north a t ha ht0 ht1.le
  have hot := odd_positive a t ha ht ht1
  by_cases hmid : z ≤ t
  · rw [profile_middle a t z ⟨by linarith,hmid⟩]
    unfold CapAngularShooting.interior
    exact mul_pos hpt (odd_positive a z ha hz0 (lt_of_le_of_lt hmid ht1))
  · rw [profile_right a t z ht ⟨(le_of_not_ge hmid),hz1⟩]
    unfold CapAngularShooting.exterior
    exact mul_pos hot (Packet06ConePolePositive.pole_positive_near_north a z ha (by linarith) hz1)

theorem profile_mul_coordinate_nonnegative (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht0 : (1/2 : ℝ) ≤ t) (ht1 : t < 1) (hz : z ∈ Icc (-1 : ℝ) 1) :
    0 ≤ profile a t z * z := by
  by_cases hz0 : 0 < z
  · exact mul_nonneg (profile_positive a t z ha ht0 ht1 hz0 hz.2).le hz0.le
  · by_cases hzneg : z < 0
    · have hp := profile_positive a t (-z) ha ht0 ht1 (by linarith) (by linarith [hz.1])
      have hodd := profile_odd a t z (by linarith)
      nlinarith
    · have hz' : z = 0 := by linarith
      simp [hz']

theorem profile_axis_pair_positive (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht0 : (1/2 : ℝ) ≤ t) (ht1 : t < 1) :
    0 < ∫ q : Sphere, field a t q * ((q : Space) 2) ∂angularMeasure := by
  have ht : 0 < t := by linarith
  let F : Sphere → ℝ := fun q => field a t q * ((q : Space) 2)
  have hc : Continuous F := (profile_continuous a t ha ht ht1).mul
    (OQ14.ConicalAngularTrial.coordinate_continuous 2)
  have hi := OQ14.ConicalAngularTrial.continuous_integrable F hc
  have hn (q : Sphere) : 0 ≤ F q := profile_mul_coordinate_nonnegative a t ((q : Space) 2) ha ht0 ht1 (coordinate_range q)
  have hnint : 0 ≤ ∫ q : Sphere, F q ∂angularMeasure := integral_nonneg hn
  by_contra! hzero
  have he := OQ14.SphereMeasure.continuous_zero_of_integral_zero F hc hi hn (le_antisymm hzero hnint)
  have h := congrFun he north
  have hpos := field_nonzero a t ha ht ht1
  change field a t north * ((north : Space) 2) = 0 at h
  have hnorth : (north : Space) 2 = 1 := by simp [north,basis]
  rw [hnorth,mul_one] at h
  exact hpos.ne' h
#print axioms OQ14.Packet06ConeProfilePositive.profile_positive
#print axioms OQ14.Packet06ConeProfilePositive.profile_mul_coordinate_nonnegative
#print axioms OQ14.Packet06ConeProfilePositive.profile_axis_pair_positive
end OQ14.Packet06ConeProfilePositive
