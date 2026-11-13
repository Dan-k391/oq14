import Packet07CommonConeData

/-! A finite family of bounded translated balls has one explicit enclosing ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07Enclosure
open Set Metric
abbrev Space := Maxwell.Space

theorem exists_enclosing_radius {ι : Type*} [Fintype ι] [DecidableEq ι]
    (center : ι → Space) (r : ℝ) (hr : 0 ≤ r) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i : ι, closedBall (center i) r ⊆ closedBall (0 : Space) R := by
  let R := 1 + r + ∑ i, ‖center i‖
  have hsum : 0 ≤ ∑ i, ‖center i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨R, by dsimp [R]; linarith, ?_⟩
  intro i x hx
  have hi : ‖center i‖ ≤ ∑ j, ‖center j‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hx' : ‖x - center i‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have ht : ‖x‖ ≤ ‖x - center i‖ + ‖center i‖ := by
    have h := norm_add_le (x - center i) (center i)
    simpa using h
  simp only [mem_closedBall, dist_zero_right]
  dsimp [R]
  linarith

end OQ14.Packet07Enclosure
#print axioms OQ14.Packet07Enclosure.exists_enclosing_radius
