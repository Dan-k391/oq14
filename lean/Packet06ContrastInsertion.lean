import Packet06ConcreteInsertion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ContrastInsertion
open Filter MeasureTheory Set Metric OQ14.StaticCoefficient Packet06MaterialSymmetry
open scoped Topology
abbrev Space := FourierL2.Space

def addScaled (base cone : Coefficient) (η : ℝ) (hη : 0 ≤ η) : Coefficient where
  value x := base.value x + η * cone.value x
  bound := base.bound + η * cone.bound
  measurable := base.measurable.add (measurable_const.mul cone.measurable)
  nonnegative x := add_nonneg (base.nonnegative x) (mul_nonneg hη (cone.nonnegative x))
  bounded x := add_le_add (base.bounded x) (mul_le_mul_of_nonneg_left (cone.bounded x) hη)

theorem axial (base cone : Coefficient) (η : ℝ) (hη : 0 ≤ η)
    (hb : Axial base) (hc : Axial cone) : Axial (addScaled base cone η hη) := by
  intro θ x
  change base.value _ + η * cone.value _ = base.value _ + η * cone.value _
  rw [hb θ x,hc θ x]

theorem meridional (base cone : Coefficient) (η : ℝ) (hη : 0 ≤ η)
    (hb : Meridional base) (hc : Meridional cone) : Meridional (addScaled base cone η hη) := by
  intro x
  change base.value _ + η * cone.value _ = base.value _ + η * cone.value _
  rw [hb x,hc x]

theorem support (base cone : Coefficient) (η : ℝ) (hη : 0 ≤ η) (R : ℝ)
    (hb : ∀ x : Space, x ∉ closedBall 0 R → base.value (VectorFourier.coordinateMap x) = 0)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → cone.value (VectorFourier.coordinateMap x) = 0) :
    ∀ x : Space, x ∉ closedBall 0 R → (addScaled base cone η hη).value (VectorFourier.coordinateMap x) = 0 := by
  intro x hx
  simp [addScaled,hb x hx,hc x hx]

theorem tends_pointwise (base cone : Coefficient) (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j)
    (ht : Tendsto η atTop (𝓝 0)) (x : StaticCoefficient.Space) :
    Tendsto (fun j => (addScaled base cone (η j) (hη j)).value x) atTop (𝓝 (base.value x)) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => base.value x) atTop (𝓝 (base.value x))).add (ht.mul_const (cone.value x))
  simpa only [zero_mul,add_zero,addScaled] using h

theorem uniform_bound (base cone : Coefficient) (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j)
    (hηb : ∀ j, η j ≤ 1) (j : ℕ) :
    (addScaled base cone (η j) (hη j)).bound ≤ base.bound + cone.bound := by
  change base.bound + η j * cone.bound ≤ base.bound + cone.bound
  have hn := bound_nonnegative cone
  nlinarith [hηb j]

theorem strictly_increases (base cone : Coefficient) (η : ℝ) (hη : 0 ≤ η)
    (hηpos : 0 < η) (x : StaticCoefficient.Space) (hx : 0 < cone.value x) :
    base.value x < (addScaled base cone η hη).value x := by
  change base.value x < base.value x + η*cone.value x
  nlinarith
#print axioms OQ14.Packet06ContrastInsertion.axial
#print axioms OQ14.Packet06ContrastInsertion.meridional
#print axioms OQ14.Packet06ContrastInsertion.support
#print axioms OQ14.Packet06ContrastInsertion.tends_pointwise
#print axioms OQ14.Packet06ContrastInsertion.uniform_bound
#print axioms OQ14.Packet06ContrastInsertion.strictly_increases
end OQ14.Packet06ContrastInsertion
