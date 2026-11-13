import Packet05ChartOrientation
import Packet07BoundarySwapMeasure

/-! Normal orientation reversal is a genuine volume-preserving orthogonal
linear equivalence, including when composed with the Cartesian swap. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05ChartOrientationMeasure
open MeasureTheory OQ14.Maxwell OQ14.Packet05ChartOrientation OQ14.Packet07BoundaryCoordinates

def reflectLinear (up : Bool) : Maxwell.Space →ₗ[ℝ] Maxwell.Space where
  toFun := reflectNormal up
  map_add' x y := by
    cases up <;> ext j <;> fin_cases j <;> simp [reflectNormal,basis,EuclideanSpace.single_apply,
      PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply] <;> ring
  map_smul' c x := by
    cases up <;> ext j <;> fin_cases j <;> simp [reflectNormal,basis,EuclideanSpace.single_apply,
      PiLp.sub_apply,PiLp.smul_apply] <;> ring

theorem reflect_involution (up : Bool) (x : Maxwell.Space) : reflectNormal up (reflectNormal up x) = x := by
  cases up <;> ext j <;> fin_cases j <;> simp [reflectNormal,basis,EuclideanSpace.single_apply,
    PiLp.sub_apply,PiLp.smul_apply] <;> ring

theorem reflect_norm (up : Bool) (x : Maxwell.Space) : ‖reflectNormal up x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_three,Fin.sum_univ_three]
  cases up <;> simp [reflectNormal,basis,EuclideanSpace.single_apply,
    PiLp.sub_apply,PiLp.smul_apply,Real.norm_eq_abs,sq_abs] <;> ring

def reflectIsometry (up : Bool) : Maxwell.Space ≃ₗᵢ[ℝ] Maxwell.Space where
  toLinearEquiv :=
    { toLinearMap := reflectLinear up
      invFun := reflectNormal up
      left_inv := reflect_involution up
      right_inv := reflect_involution up }
  norm_map' := reflect_norm up

theorem reflect_measure_preserving (up : Bool) :
    MeasurePreserving (reflectNormal up) (volume : Measure Maxwell.Space) volume :=
  (reflectIsometry up).measurePreserving

theorem oriented_coordinates_measure_preserving (up : Bool) (i : Fin 3) :
    MeasurePreserving (fun x => reflectNormal up (swap i x)) (volume : Measure Maxwell.Space) volume :=
  (reflect_measure_preserving up).comp (Packet07BoundarySwapMeasure.swap_measure_preserving i)

end OQ14.Packet05ChartOrientationMeasure
#print axioms OQ14.Packet05ChartOrientationMeasure.reflect_involution
#print axioms OQ14.Packet05ChartOrientationMeasure.reflect_norm
#print axioms OQ14.Packet05ChartOrientationMeasure.reflect_measure_preserving
#print axioms OQ14.Packet05ChartOrientationMeasure.oriented_coordinates_measure_preserving
