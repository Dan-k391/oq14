import Packet06ContrastInsertion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SphereInsertion
open Filter Set MeasureTheory Metric OQ14.StaticCoefficient Packet06MaterialSymmetry Packet06ContrastInsertion
open scoped Topology
abbrev Space := FourierL2.Space

def family (n : ℝ) (hn : 1 < n) (cone : Coefficient)
    (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j) (j : ℕ) : Coefficient :=
  addScaled (ModalWeightedMode.coefficient n hn) cone (η j) (hη j)

theorem admissible (n : ℝ) (hn : 1 < n) (cone : Coefficient)
    (hax : Axial cone) (hmer : Meridional cone)
    (hsupp : ∀ x : Space, x ∉ closedBall 0 1 → cone.value (VectorFourier.coordinateMap x) = 0)
    (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j) (hηb : ∀ j, η j ≤ 1)
    (ht : Tendsto η atTop (𝓝 0)) :
    let D := (ModalWeightedMode.coefficient n hn).bound + cone.bound
    (∀ j, (family n hn cone η hη j).bound ≤ D) ∧
    (ModalWeightedMode.coefficient n hn).bound ≤ D ∧
    (∀ᵐ x : StaticCoefficient.Space, Tendsto (fun j => (family n hn cone η hη j).value x) atTop
      (𝓝 ((ModalWeightedMode.coefficient n hn).value x))) ∧
    (∀ j x, x ∉ closedBall 0 1 → (family n hn cone η hη j).value (VectorFourier.coordinateMap x) = 0) ∧
    (∀ j, Axial (family n hn cone η hη j)) ∧
    (∀ j, Meridional (family n hn cone η hη j)) := by
  dsimp only
  refine ⟨fun j => uniform_bound _ _ η hη hηb j, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_add_of_nonneg_right (bound_nonnegative cone)
  · exact Filter.Eventually.of_forall (fun x => tends_pointwise _ _ η hη ht x)
  · intro j x hx
    exact support _ _ (η j) (hη j) 1 (ModalWeightedMode.coefficient_support n hn) hsupp x hx
  · intro j
    exact axial _ _ (η j) (hη j) (Packet06SphereSymmetry.sphere_axial n hn) hax
  · intro j
    exact meridional _ _ (η j) (hη j) (Packet06SphereSymmetry.sphere_meridional n hn) hmer
#print axioms OQ14.Packet06SphereInsertion.admissible
end OQ14.Packet06SphereInsertion
