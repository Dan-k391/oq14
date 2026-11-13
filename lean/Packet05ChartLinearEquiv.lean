import Packet05ChartBasis

/-! Forward and inverse signed-coordinate maps as continuous linear
homeomorphisms, with their exact measure-preserving changes of variables. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ChartLinearEquiv
open MeasureTheory OQ14.Maxwell OQ14.Packet05ChartOrientation OQ14.Packet05ChartOrientationMeasure
  OQ14.Packet05ChartBasis OQ14.Packet07BoundaryCoordinates

def orientedLinear (up : Bool) (i : Fin 3) : Maxwell.Space →ₗ[ℝ] Maxwell.Space :=
  (reflectLinear up).comp (swapLinear i)

def orientedEquiv (up : Bool) (i : Fin 3) : Maxwell.Space ≃ₗ[ℝ] Maxwell.Space where
  toLinearMap := orientedLinear up i
  invFun := inverseOriented up i
  left_inv := inverse_oriented_left up i
  right_inv := inverse_oriented_right up i

def orientedHomeomorph (up : Bool) (i : Fin 3) : Maxwell.Space ≃ₜ Maxwell.Space :=
  (orientedEquiv up i).toContinuousLinearEquiv.toHomeomorph

theorem oriented_inverse_measure_preserving (up : Bool) (i : Fin 3) :
    MeasurePreserving (inverseOriented up i) (volume : Measure Maxwell.Space) volume :=
  (Packet07BoundarySwapMeasure.swap_measure_preserving i).comp (reflect_measure_preserving up)

theorem oriented_forward_basis (up : Bool) (i j : Fin 3) :
    orientedLinear up i (basis (Equiv.swap i 2 j)) = chartSign up j • basis j := by
  have h := congrArg (orientedLinear up i) (inverse_oriented_basis up i j)
  change reflectNormal up (swap i (inverseOriented up i (basis j))) = _ at h
  rw [inverse_oriented_right up i (basis j)] at h
  have hs := congrArg (fun v : Maxwell.Space => chartSign up j • v) h
  cases up <;> fin_cases j <;> simp [chartSign] at hs ⊢ <;> exact hs.symm

end OQ14.Packet05ChartLinearEquiv
#print axioms OQ14.Packet05ChartLinearEquiv.oriented_inverse_measure_preserving
#print axioms OQ14.Packet05ChartLinearEquiv.oriented_forward_basis
