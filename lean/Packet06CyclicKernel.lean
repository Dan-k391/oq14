import Packet06CyclicMaterial
import ModalAxialKernel

/-! The true dyadic remainder respects the proper cyclic coordinate rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicKernel
open Maxwell Packet06CyclicRotation
open WeakCurl (previous)

theorem remainder_rotate (k : ℝ) (x : Space) (i j : Fin 3) :
    DyadicKernel.remainder k (rotate x) i j =
      DyadicKernel.remainder k x (previous i) (previous j) := by
  simp only [DyadicKernel.remainder, DyadicKernel.dyadic, GreenKernel.phiHessian, GreenKernel.phi,
    rotate_norm]
  fin_cases i <;> fin_cases j <;>
    simp [rotate, previous, WithLp.equiv_symm_pi_apply, GreenKernel.unitCoordinate]

end OQ14.Packet06CyclicKernel
#print axioms OQ14.Packet06CyclicKernel.remainder_rotate
