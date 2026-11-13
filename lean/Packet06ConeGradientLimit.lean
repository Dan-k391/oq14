import Packet06ConeAngularLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeGradientLimit
open Filter Set OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology

theorem slope_parameter_continuousOn (t z : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hz0 : -1 ≤ z) (hz1 : z ≤ 1) :
    ContinuousOn (fun a => slope a t z) (Icc (0 : ℝ) 2) := by
  have hp_t : |(1-t)/2| < 1 := by rw [abs_of_pos (by linarith)]; linarith
  have ho_t : |t| < 1 := by rw [abs_of_pos ht]; exact ht1
  unfold CapSturmLiouville.slope
  split_ifs with hneg hmid
  · have hp : |(1-(-z))/2| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    exact (odd_parameter_continuousOn t ho_t).mul (poleD_parameter_continuousOn (-z) hp)
  · have ho : |z| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    exact (pole_parameter_continuousOn t hp_t).mul (oddD_parameter_continuousOn z ho)
  · have hp : |(1-z)/2| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    exact (odd_parameter_continuousOn t ho_t).mul (poleD_parameter_continuousOn z hp)

theorem slope_two (t z : ℝ) : slope 2 t z = t := by
  unfold CapSturmLiouville.slope negativeD CapAngularShooting.interiorD exteriorD
  simp only [pole_two,odd_two,poleD_two,oddD_two,mul_one]
  split_ifs <;> rfl

theorem normalized_slope_tendsto (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 2))
    (hbound : ∀ j, ell j ∈ Icc (0 : ℝ) 2) (t z : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hz0 : -1 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun j => slope (ell j) t z / t) atTop (𝓝 1) := by
  have hw : Tendsto ell atTop (𝓝[Icc (0 : ℝ) 2] 2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hell,Filter.Eventually.of_forall hbound⟩
  have h := ((slope_parameter_continuousOn t z ht ht1 hz0 hz1) 2 (by norm_num)).tendsto.comp hw
  have hn := h.div_const t
  have he : slope 2 t z / t = 1 := by rw [slope_two,div_self (ne_of_gt ht)]
  simpa only [he] using hn
#print axioms OQ14.Packet06ConeGradientLimit.slope_parameter_continuousOn
#print axioms OQ14.Packet06ConeGradientLimit.slope_two
#print axioms OQ14.Packet06ConeGradientLimit.normalized_slope_tendsto
end OQ14.Packet06ConeGradientLimit
