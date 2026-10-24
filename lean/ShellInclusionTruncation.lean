import ShellInclusionSmall
import MaterialVolumeConverse

/-! The dynamic volume block of a coefficient supported in a ball does not depend on the enclosing
radius used to truncate the dynamic convolution, as long as that radius encloses the support. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ShellInclusionTruncation
open MeasureTheory Metric
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

theorem volumeBlock_radius_independent (c : Coefficient) (k R R' : ℝ)
    (hR : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x)=0)
    (hR' : ∀ x : Space, x ∉ closedBall (0 : Space) R' → c.value (VectorFourier.coordinateMap x)=0) :
    DynamicVolume.volumeBlock c k R=DynamicVolume.volumeBlock c k R' := by
  apply ContinuousLinearMap.ext
  intro u
  apply MaterialVolumeConverse.vector_ext
  intro i
  filter_upwards [NewtonL2.physicalCoordinate_ae (DynamicVolume.volumeBlock c k R u) i,
    NewtonL2.physicalCoordinate_ae (DynamicVolume.volumeBlock c k R' u) i,
    DynamicVolume.volumeBlock_actual c u k R hR i,DynamicVolume.volumeBlock_actual c u k R' hR' i]
    with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

theorem sandwich_radius_independent (c : Coefficient) (k R R' : ℝ)
    (hR : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x)=0)
    (hR' : ∀ x : Space, x ∉ closedBall (0 : Space) R' → c.value (VectorFourier.coordinateMap x)=0) :
    StaticCoefficient.sqrtMultiplier c*ShellInclusionVolume.kernel k R*StaticCoefficient.sqrtMultiplier c=
      StaticCoefficient.sqrtMultiplier c*ShellInclusionVolume.kernel k R'*StaticCoefficient.sqrtMultiplier c := by
  have h := volumeBlock_radius_independent c k R R' hR hR'
  rw [ShellInclusionVolume.volumeBlock_eq_sandwich,ShellInclusionVolume.volumeBlock_eq_sandwich] at h
  exact sub_right_inj.mp h

/-- With the inclusion supported in the ball of radius b, its own block in the effective inclusion
block may be taken at the enclosing radius b, independently of the shell's enclosing radius. -/
theorem effective_eq_inclusion_radius (cs ci : Coefficient) (k R b : ℝ)
    (hb : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x)=0)
    (hR : ∀ x : Space, x ∉ closedBall (0 : Space) R → ci.value (VectorFourier.coordinateMap x)=0) :
    DynamicVolume.volumeBlock ci k R-ShellInclusionReaction.reaction cs ci k R=
      DynamicVolume.volumeBlock ci k b-ShellInclusionReaction.reaction cs ci k R := by
  rw [volumeBlock_radius_independent ci k R b hR hb]

end OQ14.ShellInclusionTruncation
#print axioms OQ14.ShellInclusionTruncation.volumeBlock_radius_independent
#print axioms OQ14.ShellInclusionTruncation.sandwich_radius_independent
#print axioms OQ14.ShellInclusionTruncation.effective_eq_inclusion_radius
