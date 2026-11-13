import Packet07BoundaryNormalRefined

/-! Converting a strictly monotone normal slice into exact material sides. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundarySides
open Set

theorem increasing_side {f : ℝ → ℝ} {I : Set ℝ} (h : StrictMonoOn f I)
    {z r : ℝ} (hz : z ∈ I) (hr : r ∈ I) (hroot : f r = 0) :
    (0 < f z ↔ r < z) := by
  constructor
  · intro hf
    by_contra hn
    have hzle : z ≤ r := le_of_not_gt hn
    rcases hzle.eq_or_lt with he | hl
    · subst z; linarith
    · have hh := h hz hr hl
      linarith
  · intro hlt
    have hh := h hr hz hlt
    linarith

theorem decreasing_side {f : ℝ → ℝ} {I : Set ℝ} (h : StrictAntiOn f I)
    {z r : ℝ} (hz : z ∈ I) (hr : r ∈ I) (hroot : f r = 0) :
    (0 < f z ↔ z < r) := by
  constructor
  · intro hf
    by_contra hn
    have hzle : r ≤ z := le_of_not_gt hn
    rcases hzle.eq_or_lt with he | hl
    · subst z; linarith
    · have hh := h hr hz hl
      linarith
  · intro hlt
    have hh := h hz hr hlt
    linarith

end OQ14.Packet07BoundarySides
#print axioms OQ14.Packet07BoundarySides.increasing_side
#print axioms OQ14.Packet07BoundarySides.decreasing_side
