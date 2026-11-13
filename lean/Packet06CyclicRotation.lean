import Packet06ComplexAffine
import ModalAxialRotation

/-! Proper cyclic 120-degree Cartesian rotation taking the cone axis to the plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06CyclicRotation
open MeasureTheory Maxwell WeakCurl

def rotate (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => x (previous i))
def unrotate (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => x (next i))

theorem rotate_unrotate (x : Space) : rotate (unrotate x) = x := by
  ext i
  fin_cases i <;> simp [rotate,unrotate,next,previous]

theorem unrotate_rotate (x : Space) : unrotate (rotate x) = x := by
  ext i
  fin_cases i <;> simp [rotate,unrotate,next,previous]

theorem rotate_norm (x : Space) : ‖rotate x‖ = ‖x‖ := by
  have h : ‖rotate x‖^2 = ‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_three, rotate, previous]
    ring
  nlinarith [norm_nonneg (rotate x), norm_nonneg x]

def rotation : Space ≃ₗᵢ[ℝ] Space where
  toFun := rotate
  invFun := unrotate
  left_inv := unrotate_rotate
  right_inv := rotate_unrotate
  map_add' x y := by ext i; simp [rotate, PiLp.add_apply]
  map_smul' a x := by ext i; simp [rotate, PiLp.smul_apply]
  norm_map' := rotate_norm

theorem rotate_axis : rotate (EuclideanSpace.single 2 1) = EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp [rotate, previous, EuclideanSpace.single_apply]

theorem rotation_basis (i : Fin 3) : rotate (EuclideanSpace.single i 1) = EuclideanSpace.single (next i) 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [rotate, previous,next,EuclideanSpace.single_apply]

end OQ14.Packet06CyclicRotation
#print axioms OQ14.Packet06CyclicRotation.rotate_unrotate
#print axioms OQ14.Packet06CyclicRotation.unrotate_rotate
#print axioms OQ14.Packet06CyclicRotation.rotate_norm
#print axioms OQ14.Packet06CyclicRotation.rotate_axis
#print axioms OQ14.Packet06CyclicRotation.rotation_basis
