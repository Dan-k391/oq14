import Packet06AxialAmplitude
import ComplexVectorSphere

/-! Axial rotation on complex angular polarization is a genuine isometry. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenAxialAngularVector
open Maxwell ModalAxialRotation
abbrev Vector := ComplexVectorSphere.Vector

def rotate (θ : ℝ) (v : Vector) : Vector :=
  (WithLp.equiv 2 (Fin 3 → ℂ)).symm (ModalAxialRotation.vector θ (fun i => v i))

theorem rotate_norm (θ : ℝ) (v : Vector) : ‖rotate θ v‖=‖v‖ := by
  have h : ‖rotate θ v‖^2=‖v‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simpa only [Maxwell.energy,Complex.normSq_eq_norm_sq,rotate,WithLp.equiv_symm_pi_apply,Fin.sum_univ_three] using
      Packet06AxialAmplitude.rotation_energy θ (fun i => v i)
  nlinarith [norm_nonneg (rotate θ v),norm_nonneg v]

theorem rotate_sub (θ : ℝ) (u v : Vector) : rotate θ (u-v)=rotate θ u-rotate θ v := by
  ext i
  fin_cases i <;> simp [rotate,vector,PiLp.sub_apply] <;> ring

theorem rotate_continuous (θ : ℝ) : Continuous (rotate θ) := by
  apply (isometry_iff_dist_eq.mpr ?_).continuous
  intro u v
  rw [dist_eq_norm,dist_eq_norm,← rotate_sub,rotate_norm]

end OQ14.Packet07DrivenAxialAngularVector
#print axioms OQ14.Packet07DrivenAxialAngularVector.rotate_norm
#print axioms OQ14.Packet07DrivenAxialAngularVector.rotate_sub
#print axioms OQ14.Packet07DrivenAxialAngularVector.rotate_continuous
