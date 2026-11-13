import Packet06PlacedPole
import Packet05RoundedModeSupport

/-! Actual rounded material symmetry supplies a genuine observed simple pole
in the physically transported sector at the final prescribed frequency. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RoundedPlacedPole
open Set Metric Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
abbrev Space := Maxwell.Space

theorem rounded_symmetries {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) :
    Packet06MaterialSymmetry.Axial (rounded n hn g η hη j) ∧
      Packet06MaterialSymmetry.Meridional (rounded n hn g η hη j) := by
  obtain ⟨_,_,_,_,_,ha,hm,_,_⟩ := Packet06RoundedInsertion.admissible
    (fun _ : Fin N => g.datum) (fun _ => g.radius) g.center (n^2) (sq_nonneg n)
    (fun _ => g.contrast.le) (fun _ => g.radius_outer) g.outer_disjoint (fun _ => g.radius_pos)
    (ModalWeightedMode.coefficient n hn) η hη (ModalWeightedMode.coefficient_support n hn)
    (Packet06SphereSymmetry.sphere_axial n hn) (Packet06SphereSymmetry.sphere_meridional n hn)
    g.onAxis (fun i => (g.outer_inside i).trans ball_subset_closedBall)
  exact ⟨ha j,hm j⟩

theorem rounded_placed_observed_pole {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (z : ℂ) (u : Packet06SectorOperator.Sector)
    (hcert : Packet06SimpleCertificate.Certified (rounded n hn g η hη j) 1 z u)
    (s : ℝ) (hs : 0 < s) (a : Space) :
    Packet06PlacedPole.SimpleObservedPole (rounded n hn g η hη j) 1 s hs a ((s : ℂ)*z) u := by
  obtain ⟨ha,hm⟩ := rounded_symmetries n hn g η hη j
  exact Packet06PlacedPole.certified_observed_pole _ ha hm 1 (by norm_num)
    (Packet05RoundedModeSupport.rounded_support n hn g η hη j) s hs a z u hcert

end OQ14.Packet06RoundedPlacedPole
#print axioms OQ14.Packet06RoundedPlacedPole.rounded_symmetries
#print axioms OQ14.Packet06RoundedPlacedPole.rounded_placed_observed_pole
