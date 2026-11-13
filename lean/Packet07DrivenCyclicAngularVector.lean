import Packet07DrivenAxialHerglotzMagnetic
import Packet06CyclicRotationMaxwell

/-! Cyclic proper rotation on complex angular polarization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenCyclicAngularVector
open Maxwell Packet06CyclicRotation
abbrev Vector := ComplexVectorSphere.Vector

def rotate (v : Vector) : Vector := (WithLp.equiv 2 (Fin 3 → ℂ)).symm (fun i => v (WeakCurl.previous i))

theorem rotate_norm (v : Vector) : ‖rotate v‖=‖v‖ := by
  have h : ‖rotate v‖^2=‖v‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_three,rotate,WeakCurl.previous]
    ring
  nlinarith [norm_nonneg (rotate v),norm_nonneg v]

theorem rotate_sub (u v : Vector) : rotate (u-v)=rotate u-rotate v := by
  ext i
  simp [rotate,PiLp.sub_apply]

theorem rotate_continuous : Continuous rotate := by
  apply (isometry_iff_dist_eq.mpr ?_).continuous
  intro u v
  rw [dist_eq_norm,dist_eq_norm,←rotate_sub,rotate_norm]
end OQ14.Packet07DrivenCyclicAngularVector
#print axioms OQ14.Packet07DrivenCyclicAngularVector.rotate_norm
#print axioms OQ14.Packet07DrivenCyclicAngularVector.rotate_sub
#print axioms OQ14.Packet07DrivenCyclicAngularVector.rotate_continuous
