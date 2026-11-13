import Packet07VerticalPath

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07RadialPath
open Set

theorem radial_joined (n : ℕ) (m a z c : ℝ) (u : ConicalSmoothCapGraph.Plane)
    (hm : 0 < m) (hz : 0 < z) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hc : 2*ConicalTipRounding.radius n ≤ c*‖u‖)
    (hinc : (u,z) ∈ ConicalSmoothJunction.inclusion n m a) :
    JoinedIn (ConicalSmoothJunction.inclusion n m a ∩ {x | 0 < x.2}) (u,z) (c • u,z) := by
  apply JoinedIn.of_segment_subset
  rw [segment_eq_image]
  rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
  change (1-t) • (u,z) + t • (c • u,z) ∈ _
  have hx : (1-t) • (u,z) + t • (c • u,z) = (((1-t)+t*c) • u,z) := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    · simp only [mul_smul, add_smul]
    · ring
  rw [hx]
  let d : ℝ := 1-t+t*c
  have hd0 : 0 ≤ d := by dsimp [d]; nlinarith
  have hdc : c ≤ d := by dsimp [d]; nlinarith
  have hd1 : d ≤ 1 := by dsimp [d]; nlinarith
  have hn : ‖d • u‖ = d*‖u‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0]
  refine ⟨Packet07RadialMonotone.inclusion_inward n m a z u (d • u) hm hz.le ?_ ?_ hinc, hz⟩
  · rw [hn]
    nlinarith [norm_nonneg u]
  · rw [hn]
    nlinarith [norm_nonneg u]

end OQ14.Packet07RadialPath
#print axioms OQ14.Packet07RadialPath.radial_joined
