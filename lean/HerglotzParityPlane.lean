import HerglotzPointTail

/-! Actual magnetic/electric parity plane flux selectors and whole-plane integrability. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HerglotzParityPlane
open MeasureTheory Metric Set SphereReactionKernel SphereMagneticParity HerglotzPointTail
open scoped ComplexConjugate Topology

def flux (electric magnetic : Bool) (k : ℝ) (x y z : Space) (j m : Fin 3) : ℂ :=
  crossProduct (fun i => reaction electric k x y i j)
    (Maxwell.conjugate (fun i => magneticReaction magnetic k x z i m)) 2

theorem plane_identity (electric magnetic : Bool) (k : ℝ) (x y z : Space)
    (hx : x 2=0) (j m : Fin 3) :
    flux electric magnetic k x y z j m =
      if electric=false ∧ magnetic=true then regularFlux k x y z j m else 0 := by
  change reaction electric k x y 0 j*star (magneticReaction magnetic k x z 1 m)-
    reaction electric k x y 1 j*star (magneticReaction magnetic k x z 0 m) = _
  rw [reaction_on_plane electric k x y hx 0 j, reaction_on_plane electric k x y hx 1 j,
    magnetic_on_plane magnetic k x z hx 1 m, magnetic_on_plane magnetic k x z hx 0 m]
  cases electric <;> cases magnetic <;>
    norm_num [sign, Fin.ext_iff, regularFlux, cross_apply, Maxwell.conjugate]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals simp
  all_goals ring

theorem flux_norm_le (electric magnetic : Bool) (k : ℝ) (x y z : Space)
    (hx : x 2=0) (j m : Fin 3) :
    ‖flux electric magnetic k x y z j m‖ ≤ ‖regularFlux k x y z j m‖ := by
  rw [plane_identity electric magnetic k x y z hx j m]
  split_ifs
  · exact le_rfl
  · simp only [norm_zero]; exact norm_nonneg _

theorem whole_plane_bound (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ electric magnetic : Bool, ∀ y z : Space,
      y ∈ closedBall 0 R → z ∈ closedBall 0 R → ∀ j m : Fin 3,
        Integrable (fun q : Plane => flux electric magnetic k (MaxwellPlaneTail.planePoint q) y z j m) ∧
        (∫ q : Plane, ‖flux electric magnetic k (MaxwellPlaneTail.planePoint q) y z j m‖) ≤ C := by
  obtain ⟨C,hC,hb⟩ := HerglotzPointTail.whole_plane_bound k R hR hk
  refine ⟨C,hC,?_⟩
  intro electric magnetic y z hy hz j m
  have he (q : Plane) := plane_identity electric magnetic k (MaxwellPlaneTail.planePoint q) y z (by rfl) j m
  simp_rw [he]
  by_cases h : electric=false ∧ magnetic=true
  · simpa only [h, if_true] using hb y z hy hz j m
  · simp only [h, if_false, norm_zero, integral_zero, hC, and_true]
    exact integrable_zero Plane ℂ volume

theorem flux_tail (electric magnetic : Bool) (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0)
    (x y z : Space) (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hp : x 2=0)
    (hy : y ∈ closedBall 0 R) (hz : z ∈ closedBall 0 R) (j m : Fin 3) :
    ‖flux electric magnetic k x y z j m‖ ≤ PointMaxwellTail.tailConstant k k R/‖x‖^3 :=
  (flux_norm_le electric magnetic k x y z hp j m).trans
    (regular_flux_tail k R hR hk x y z hx hx₂ hp hy hz j m)

end OQ14.HerglotzParityPlane
#print axioms OQ14.HerglotzParityPlane.plane_identity
#print axioms OQ14.HerglotzParityPlane.flux_norm_le
#print axioms OQ14.HerglotzParityPlane.whole_plane_bound
#print axioms OQ14.HerglotzParityPlane.flux_tail
