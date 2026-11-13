import Packet06PlanarProjection
import Packet05BinaryPhaseMaximum
import Mathlib.Topology.Homeomorph.Lemmas

/-! The actual positive Maxwell placement as a homeomorphism, including
the literal two material phase closures and observation balls. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06PlacementHomeomorph
open Set Metric Maxwell Packet06CyclicRotation Packet05BinaryPhaseMaximum

def placement (s : ℝ) (hs : 0 < s) (a : Space) : Space ≃ₜ Space where
  toFun := Packet06PhysicalPlacement.point s a
  invFun y := unrotate (s • (y-a))
  left_inv := Packet06PlacedPeaks.inverse_point s hs a
  right_inv := Packet06PlanarProjection.inverse_point_right s hs a
  continuous_toFun := continuous_const.add (rotation.continuous.const_smul _)
  continuous_invFun := by
    change Continuous (fun y : Space => rotation.symm (s • (y-a)))
    exact rotation.symm.continuous.comp
      ((continuous_id.sub continuous_const).const_smul s)

theorem image_phase (s : ℝ) (hs : 0 < s) (a : Space) (body : Set Space) (b : Bool) :
    placement s hs a '' phaseDomain body b = phaseDomain (placement s hs a '' body) b := by
  cases b <;> simp only [phaseDomain, (placement s hs a).image_closure,
    (placement s hs a).image_compl]

theorem image_ball (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ) :
    placement s hs a '' ball c r = ball (placement s hs a c) (r/s) := by
  ext y
  change y ∈ (placement s hs a).toEquiv '' ball c r ↔ _
  rw [(placement s hs a).toEquiv.image_eq_preimage]
  exact (Packet06PlanarProjection.point_ball_iff s hs a c y r).symm

theorem image_closedBall (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ) :
    placement s hs a '' closedBall c r = closedBall (placement s hs a c) (r/s) := by
  ext y
  change y ∈ (placement s hs a).toEquiv '' closedBall c r ↔ _
  rw [(placement s hs a).toEquiv.image_eq_preimage]
  let x := (placement s hs a).symm y
  have hxy : placement s hs a x = y := (placement s hs a).apply_symm_apply y
  change dist x c ≤ r ↔ dist y (placement s hs a c) ≤ r/s
  rw [← hxy, show dist (placement s hs a x) (placement s hs a c) = s⁻¹*dist x c from
    Packet06PlanarProjection.point_distance_pair s hs a x c, div_eq_mul_inv,
    mul_comm r s⁻¹]
  exact (mul_le_mul_left (inv_pos.mpr hs)).symm

theorem image_phase_ball (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ)
    (body : Set Space) (b : Bool) :
    placement s hs a '' (closedBall c r ∩ phaseDomain body b) =
      closedBall (placement s hs a c) (r/s) ∩ phaseDomain (placement s hs a '' body) b := by
  rw [Set.image_inter (placement s hs a).injective, image_closedBall, image_phase]

end OQ14.Packet06PlacementHomeomorph
#print axioms OQ14.Packet06PlacementHomeomorph.image_phase
#print axioms OQ14.Packet06PlacementHomeomorph.image_ball
#print axioms OQ14.Packet06PlacementHomeomorph.image_closedBall
#print axioms OQ14.Packet06PlacementHomeomorph.image_phase_ball
