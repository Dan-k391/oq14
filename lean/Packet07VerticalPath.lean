import Packet07VerticalAccess

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07VerticalPath
open Set

theorem vertical_joined (n : ℕ) (m a z : ℝ) (u : ConicalSmoothCapGraph.Plane)
    (hm : 0 < m) (ha : 0 < a)
    (hcap : (2*m+2)*ConicalTipRounding.radius n < a/2)
    (hrad : (2*ConicalTipRounding.radius n)^2 < a^2/8)
    (heball : ConicalTipRounding.radius n < a^2/8)
    (hu : ‖u‖ ≤ 2*ConicalTipRounding.radius n)
    (hz : 0 < z) (hinc : (u,z) ∈ ConicalSmoothJunction.inclusion n m a) :
    JoinedIn (ConicalSmoothJunction.inclusion n m a ∩ {x | 0 < x.2}) (u,z) (u,a/2) := by
  apply JoinedIn.of_segment_subset
  rw [segment_eq_image]
  rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hx : (1-t) • (u,z) + t • (u,a/2) = (u,(1-t)*z+t*(a/2)) := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    · rw [← add_smul]
      simp
  change (1-t) • (u,z) + t • (u,a/2) ∈ _
  rw [hx]
  have hlow : min z (a/2) ≤ (1-t)*z+t*(a/2) := by
    rcases le_total z (a/2) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hhigh : (1-t)*z+t*(a/2) ≤ max z (a/2) := by
    rcases le_total z (a/2) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  refine ⟨Packet07VerticalAccess.inner_vertical n m a z _ u hm ha hcap hrad heball hu hz hinc hlow hhigh, ?_⟩
  change 0 < (1-t)*z+t*(a/2)
  exact lt_of_lt_of_le (lt_min hz (by linarith)) hlow

end OQ14.Packet07VerticalPath
#print axioms OQ14.Packet07VerticalPath.vertical_joined
