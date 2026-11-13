import Packet05RoundedModeBoundary

/-! The actual rounded modal material has the support needed by the mode
regularity theorem, directly from the geometry. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RoundedModeSupport
open Set Metric Maxwell Packet06ConcreteModalRounding
abbrev Space := Maxwell.Space

theorem rounded_support {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η) (j : ℕ) :
    ∀ x : Space, x ∉ closedBall 0 1 →
      (rounded n hn g η hη j).value (VectorFourier.coordinateMap x)=0 := by
  apply Packet06ContrastInsertion.support (ModalWeightedMode.coefficient n hn)
    (CommonBinaryRounding.coefficient (fun _ => g.datum) (fun _ => g.radius) g.center
      (n^2) (sq_nonneg n) (fun _ => g.contrast.le) (fun _ => g.radius_outer)
      g.outer_disjoint (fun _ => g.radius_pos) j) η hη 1
    (ModalWeightedMode.coefficient_support n hn)
  exact CommonBinaryRounding.coefficient_support (fun _ => g.datum) (fun _ => g.radius) g.center
    (n^2) (sq_nonneg n) (fun _ => g.contrast.le) (fun _ => g.radius_outer)
    g.outer_disjoint (fun _ => g.radius_pos) j 1
    (fun i => (g.outer_inside i).trans ball_subset_closedBall)

end OQ14.Packet05RoundedModeSupport
#print axioms OQ14.Packet05RoundedModeSupport.rounded_support
