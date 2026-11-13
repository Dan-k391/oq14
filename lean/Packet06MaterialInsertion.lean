import Packet06ConeUnionSymmetry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06MaterialInsertion
open MeasureTheory Set Metric OQ14.StaticCoefficient Packet06MaterialSymmetry
abbrev Space := FourierL2.Space

def unionCoefficient (c d : Coefficient) : Coefficient where
  value x := max (c.value x) (d.value x)
  bound := max c.bound d.bound
  measurable := c.measurable.max d.measurable
  nonnegative x := le_trans (c.nonnegative x) (le_max_left _ _)
  bounded x := max_le_max (c.bounded x) (d.bounded x)

theorem union_axial (c d : Coefficient) (hc : Axial c) (hd : Axial d) :
    Axial (unionCoefficient c d) := by
  intro θ x
  change max (c.value _) (d.value _) = max (c.value _) (d.value _)
  rw [hc θ x,hd θ x]

theorem union_meridional (c d : Coefficient) (hc : Meridional c) (hd : Meridional d) :
    Meridional (unionCoefficient c d) := by
  intro x
  change max (c.value _) (d.value _) = max (c.value _) (d.value _)
  rw [hc x,hd x]

theorem union_support (c d : Coefficient) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hd : ∀ x : Space, x ∉ closedBall 0 R → d.value (VectorFourier.coordinateMap x) = 0) :
    ∀ x : Space, x ∉ closedBall 0 R → (unionCoefficient c d).value (VectorFourier.coordinateMap x) = 0 := by
  intro x hx
  simp [unionCoefficient,hc x hx,hd x hx]

theorem union_spatial (c d : Coefficient) (x : Space) :
    (unionCoefficient c d).value (VectorFourier.coordinateMap x) =
      max (c.value (VectorFourier.coordinateMap x)) (d.value (VectorFourier.coordinateMap x)) := rfl

theorem union_binary (c d : Coefficient) (q : ℝ) (hq : 0 ≤ q) (x : Space)
    (hc : c.value (VectorFourier.coordinateMap x) = 0 ∨ c.value (VectorFourier.coordinateMap x) = q)
    (hd : d.value (VectorFourier.coordinateMap x) = 0 ∨ d.value (VectorFourier.coordinateMap x) = q) :
    (unionCoefficient c d).value (VectorFourier.coordinateMap x) = 0 ∨
      (unionCoefficient c d).value (VectorFourier.coordinateMap x) = q := by
  rw [union_spatial]
  rcases hc with hc | hc <;> rcases hd with hd | hd <;> simp [hc,hd,hq]
#print axioms OQ14.Packet06MaterialInsertion.union_axial
#print axioms OQ14.Packet06MaterialInsertion.union_meridional
#print axioms OQ14.Packet06MaterialInsertion.union_support
#print axioms OQ14.Packet06MaterialInsertion.union_spatial
#print axioms OQ14.Packet06MaterialInsertion.union_binary
end OQ14.Packet06MaterialInsertion
