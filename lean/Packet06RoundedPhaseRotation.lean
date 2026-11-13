import Packet05BinaryPhaseMaximum
import Packet06ConeUnionSymmetry

/-! The literal rounded inclusion, its two phase closures and the observation
balls centered on the axis are invariant under axial rotations. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RoundedPhaseRotation
open Set Metric Maxwell ModalAxialRotation Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum
abbrev Space := Maxwell.Space

theorem body_rotation {N : ℕ} {n : ℝ}
    (g : Packet06ConcreteModalGeometry.Geometry N n) (j : ℕ) (θ : ℝ) (x : Space) :
    rotation θ x ∈ body g j ↔ x ∈ body g j := by
  simp only [body,CommonBinaryInterface.body,mem_iUnion]
  change (∃ i, rotation θ x-g.center i ∈ ConicalJunctionPhysical.inclusion j
    (ConicalJunctionPhysical.slope g.datum.threshold) g.radius) ↔
    ∃ i, x-g.center i ∈ ConicalJunctionPhysical.inclusion j
      (ConicalJunctionPhysical.slope g.datum.threshold) g.radius
  exact exists_congr (fun i => Packet06ConeSymmetry.rounded_inclusion_invariant j _ _
    (Packet06ConeUnionSymmetry.rotation_norm_axis g.center g.onAxis θ i x).1
    (Packet06ConeUnionSymmetry.rotation_norm_axis g.center g.onAxis θ i x).2)

theorem closure_rotation (U : Set Space)
    (hU : ∀ θ x, rotation θ x ∈ U ↔ x ∈ U) (θ : ℝ) (x : Space) :
    rotation θ x ∈ closure U ↔ x ∈ closure U := by
  have hm (t : ℝ) : MapsTo (rotation t) U U := fun y hy => (hU t y).mpr hy
  constructor
  · intro hx
    have hh := (hm (-θ)).closure (rotation (-θ)).continuous hx
    simpa only [rotation,LinearIsometryEquiv.coe_mk,LinearIsometryEquiv.coe_toLinearEquiv,
      LinearEquiv.coe_mk,spatial_inverse] using hh
  · intro hx
    exact (hm θ).closure (rotation θ).continuous hx

theorem phase_rotation {N : ℕ} {n : ℝ}
    (g : Packet06ConcreteModalGeometry.Geometry N n) (j : ℕ) (b : Bool) (θ : ℝ) (x : Space) :
    rotation θ x ∈ phaseDomain (body g j) b ↔ x ∈ phaseDomain (body g j) b := by
  have hc := closure_rotation (body g j) (body_rotation g j)
  cases b
  · exact closure_rotation (closure (body g j))ᶜ (fun t y => not_congr (hc t y)) θ x
  · exact hc θ x

theorem ball_rotation {N : ℕ} {n : ℝ}
    (g : Packet06ConcreteModalGeometry.Geometry N n) (i : Fin N) (r θ : ℝ) (x : Space) :
    rotation θ x ∈ ball (g.center i) r ↔ x ∈ ball (g.center i) r := by
  simp only [mem_ball,dist_eq_norm,(Packet06ConeUnionSymmetry.rotation_norm_axis g.center g.onAxis θ i x).1]

theorem closedBall_rotation {N : ℕ} {n : ℝ}
    (g : Packet06ConcreteModalGeometry.Geometry N n) (i : Fin N) (r θ : ℝ) (x : Space) :
    rotation θ x ∈ closedBall (g.center i) r ↔ x ∈ closedBall (g.center i) r := by
  simp only [mem_closedBall,dist_eq_norm,(Packet06ConeUnionSymmetry.rotation_norm_axis g.center g.onAxis θ i x).1]

end OQ14.Packet06RoundedPhaseRotation
#print axioms OQ14.Packet06RoundedPhaseRotation.body_rotation
#print axioms OQ14.Packet06RoundedPhaseRotation.closure_rotation
#print axioms OQ14.Packet06RoundedPhaseRotation.phase_rotation
#print axioms OQ14.Packet06RoundedPhaseRotation.ball_rotation
#print axioms OQ14.Packet06RoundedPhaseRotation.closedBall_rotation
