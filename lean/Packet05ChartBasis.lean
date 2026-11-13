import Packet05ChartOrientationMeasure

/-! The inverse chart's signed Cartesian basis map gives the exact component
permutation and normal sign for gradients and vector fields. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05ChartBasis
open OQ14.Maxwell OQ14.Packet05ChartOrientation OQ14.Packet07BoundaryCoordinates

def chartSign (up : Bool) (j : Fin 3) : ℝ := if up || j != 2 then 1 else -1

def inverseOriented (up : Bool) (i : Fin 3) (x : Maxwell.Space) : Maxwell.Space :=
  swap i (reflectNormal up x)

theorem inverse_oriented_basis (up : Bool) (i j : Fin 3) :
    inverseOriented up i (basis j) = chartSign up j • basis (Equiv.swap i 2 j) := by
  cases up <;> fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
    simp [inverseOriented,chartSign,reflectNormal,swap,basis,Equiv.swap_apply_def,
      EuclideanSpace.single_apply,PiLp.sub_apply,PiLp.smul_apply] <;> norm_num

theorem inverse_oriented_left (up : Bool) (i : Fin 3) (x : Maxwell.Space) :
    inverseOriented up i (reflectNormal up (swap i x)) = x := by
  simp [inverseOriented,Packet05ChartOrientationMeasure.reflect_involution,swap_involution]

theorem inverse_oriented_right (up : Bool) (i : Fin 3) (x : Maxwell.Space) :
    reflectNormal up (swap i (inverseOriented up i x)) = x := by
  simp [inverseOriented,swap_involution,Packet05ChartOrientationMeasure.reflect_involution]

end OQ14.Packet05ChartBasis
#print axioms OQ14.Packet05ChartBasis.inverse_oriented_basis
#print axioms OQ14.Packet05ChartBasis.inverse_oriented_left
#print axioms OQ14.Packet05ChartBasis.inverse_oriented_right
