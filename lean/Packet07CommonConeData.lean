import Packet07FiniteSeparation
import ConicalFamily

/-! Fixed common contrast and conical data adapted to any finite separated centers. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07CommonConeData
open Set Metric
abbrev Space := Maxwell.Space

/-- For any finite distinct centers and any positive prescribed contrast, one
    common conical datum and radius satisfy the small-tip and separation requirements. -/
theorem exists_common_cone {ι : Type*} [Fintype ι] [DecidableEq ι]
    (center : ι → Space) (hinj : Function.Injective center) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ (p : ConicalStaticVolume.Data) (a : ℝ),
      p.contrast = d ∧ p.threshold = t ∧ p.exponent < 1 ∧
      0 < a ∧ a < p.cutoff.rIn ∧ a ≤ p.cutoff.rOut ∧
      (∀ i j, i ≠ j → a+a < dist (center i) (center j)) ∧
      (∀ i j, i ≠ j → Disjoint (closedBall (center i) p.cutoff.rOut)
        (closedBall (center j) p.cutoff.rOut)) := by
  obtain ⟨r,hr,hsep⟩ := Packet07FiniteSeparation.separated_radius center hinj
  let χ : ContDiffBump (0 : Space) := ⟨r/2, r, by positivity, by linarith⟩
  obtain ⟨p,hχ,hpd,hpt,hν,_⟩ := ConicalFamily.exists_data χ d t hd ht ht1
  refine ⟨p,r/4,hpd,hpt,hν,by positivity,?_,?_,?_,?_⟩
  · rw [hχ]
    change r/4 < r/2
    linarith
  · rw [hχ]
    change r/4 ≤ r
    linarith
  · intro i j hij
    have hh := hsep i j hij
    linarith
  · intro i j hij
    rw [hχ]
    change Disjoint (closedBall (center i) r) (closedBall (center j) r)
    have hdj := Packet07FiniteSeparation.disjoint_outer_balls center r hsep i j hij
    exact hdj.mono (closedBall_subset_closedBall (by linarith)) (closedBall_subset_closedBall (by linarith))

end OQ14.Packet07CommonConeData
#print axioms OQ14.Packet07CommonConeData.exists_common_cone
