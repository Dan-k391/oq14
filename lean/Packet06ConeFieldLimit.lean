import Packet06ConeProfileLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeFieldLimit
open Filter Set OQ14.CapAngularShooting OQ14.CapSturmLiouville OQ14.Maxwell
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Sphere := AngularPower.Sphere

theorem normalized_angular_electric_tendsto (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 2))
    (hbound : ∀ j, ell j ∈ Icc (0 : ℝ) 2) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (q : Sphere) :
    Tendsto (fun j => t⁻¹ • ConicalCapField.angularElectric (exponent (ell j)) (ell j) t q)
      atTop (𝓝 (basis 2)) := by
  have hz := SphereCapWeak.coordinate_range q
  have hf := Packet06ConeProfileLimit.normalized_profile_tendsto ell hell hbound t ((q : Space) 2) ht ht1 hz.1 hz.2
  have hg := Packet06ConeGradientLimit.normalized_slope_tendsto ell hell hbound t ((q : Space) 2) ht ht1 hz.1 hz.2
  have hv := Packet06ConeAngularLimit.exponent_tendsto_one ell hell
  have hleft := (hv.mul hf).smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => (q : Space)) atTop (𝓝 (q : Space)))
  have hright := hg.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => basis 2 - ((q : Space) 2) • (q : Space)) atTop
    (𝓝 (basis 2 - ((q : Space) 2) • (q : Space))))
  have h := hleft.add hright
  have he : ((q : Space) 2) • (q : Space) + (basis 2 - ((q : Space) 2) • (q : Space)) = basis 2 := by abel
  simp only [one_mul,one_smul,he] at h
  apply h.congr'
  filter_upwards with j
  simp only [ConicalCapField.angularElectric,SphereCapH1.field,SphereCapH1.gradient,smul_add,smul_smul]
  congr 1 <;> congr 1 <;> field_simp
#print axioms OQ14.Packet06ConeFieldLimit.normalized_angular_electric_tendsto
end OQ14.Packet06ConeFieldLimit
