import Packet07PositiveConnected

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07SignedConnected
open Set

def flip (x : ConicalSmoothCapGraph.Plane × ℝ) := (x.1,-x.2)

theorem flip_continuous : Continuous flip := continuous_fst.prodMk continuous_snd.neg

theorem flip_inclusion_iff (n : ℕ) (m a : ℝ) (x : ConicalSmoothCapGraph.Plane × ℝ) :
    flip x ∈ ConicalSmoothJunction.inclusion n m a ↔ x ∈ ConicalSmoothJunction.inclusion n m a := by
  simp only [ConicalSmoothJunction.inclusion, mem_setOf_eq,
    ConicalSmoothJunction.coneMargin, ConicalSmoothJunction.ballMargin,
    flip, Prod.fst, Prod.snd, abs_neg, neg_sq]

theorem negative_path_connected (n : ℕ) (m a : ℝ) (hm : 0 < m) (ha : 0 < a)
    (hcap : (2*m+2)*ConicalTipRounding.radius n < a/2)
    (hrad : (2*ConicalTipRounding.radius n)^2 < a^2/8)
    (heball : ConicalTipRounding.radius n < a^2/8)
    (hc : (2*m+1)*ConicalTipRounding.radius n < a/3)
    (hr : (2*ConicalTipRounding.radius n)^2 < a^2/9) :
    IsPathConnected (ConicalSmoothJunction.inclusion n m a ∩ {x | x.2 < 0}) := by
  have h := (Packet07PositiveConnected.positive_path_connected n m a hm ha hcap hrad heball hc hr).image flip_continuous
  have heq : flip '' Packet07PositiveConnected.positiveLobe n m a =
      ConicalSmoothJunction.inclusion n m a ∩ {x | x.2 < 0} := by
    ext ⟨u,z⟩
    constructor
    · rintro ⟨⟨v,w⟩, ⟨hi,hz⟩, he⟩
      have hif := (flip_inclusion_iff n m a (v,w)).mpr hi
      rw [he] at hif
      have hz' : -w = z := by simpa [flip] using congrArg Prod.snd he
      refine ⟨hif, ?_⟩
      change z < 0
      change 0 < w at hz
      linarith
    · rintro ⟨hi,hz⟩
      refine ⟨(u,-z), ⟨?_,?_⟩, ?_⟩
      · apply (flip_inclusion_iff n m a (u,-z)).mp
        simpa [flip] using hi
      · change 0 < -z
        exact neg_pos.mpr hz
      · simp [flip]
  simpa only [heq] using h

end OQ14.Packet07SignedConnected
#print axioms OQ14.Packet07SignedConnected.flip_continuous
#print axioms OQ14.Packet07SignedConnected.flip_inclusion_iff
#print axioms OQ14.Packet07SignedConnected.negative_path_connected
