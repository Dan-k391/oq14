import Packet06ModalConeBranch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeAngularLimit
open Filter Set OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology

theorem exponent_tendsto_one (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 2)) :
    Tendsto (fun j => exponent (ell j)) atTop (𝓝 1) := by
  have hc : ContinuousAt exponent 2 := by
    unfold exponent
    fun_prop
  have h := hc.tendsto.comp hell
  have h9 : Real.sqrt 9 = 3 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 9 by norm_num)
    nlinarith [Real.sqrt_nonneg 9]
  have he : exponent 2 = 1 := by norm_num [exponent,h9]
  simpa only [he] using h

theorem profile_parameter_continuousOn (t z : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hz0 : -1 < z) (hz1 : z < 1) :
    ContinuousOn (fun a => profile a t z) (Icc (0 : ℝ) 2) := by
  have hp_t : |(1-t)/2| < 1 := by rw [abs_of_pos (by linarith)]; linarith
  have ho_t : |t| < 1 := by rw [abs_of_pos ht]; exact ht1
  have ho_z : |z| < 1 := abs_lt.mpr ⟨hz0,hz1⟩
  have hp_z : |(1-z)/2| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
  have hp_nz : |(1-(-z))/2| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
  unfold profile
  split_ifs
  · exact ((odd_parameter_continuousOn t ho_t).mul (pole_parameter_continuousOn (-z) hp_nz)).neg
  · exact (pole_parameter_continuousOn t hp_t).mul (odd_parameter_continuousOn z ho_z)
  · exact (odd_parameter_continuousOn t ho_t).mul (pole_parameter_continuousOn z hp_z)

theorem profile_two (t z : ℝ) : profile 2 t z = t*z := by
  unfold profile negative CapAngularShooting.exterior CapAngularShooting.interior
  simp only [pole_two,odd_two]
  split_ifs <;> ring

theorem normalized_profile_tendsto (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 2))
    (hbound : ∀ j, ell j ∈ Icc (0 : ℝ) 2) (t z : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hz0 : -1 < z) (hz1 : z < 1) :
    Tendsto (fun j => profile (ell j) t z / t) atTop (𝓝 z) := by
  have hw : Tendsto ell atTop (𝓝[Icc (0 : ℝ) 2] 2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hell,Filter.Eventually.of_forall hbound⟩
  have h := ((profile_parameter_continuousOn t z ht ht1 hz0 hz1) 2 (by norm_num)).tendsto.comp hw
  have hn := h.div_const t
  have he : profile 2 t z / t = z := by rw [profile_two]; field_simp
  simpa only [he] using hn
#print axioms OQ14.Packet06ConeAngularLimit.exponent_tendsto_one
#print axioms OQ14.Packet06ConeAngularLimit.profile_parameter_continuousOn
#print axioms OQ14.Packet06ConeAngularLimit.profile_two
#print axioms OQ14.Packet06ConeAngularLimit.normalized_profile_tendsto
end OQ14.Packet06ConeAngularLimit
