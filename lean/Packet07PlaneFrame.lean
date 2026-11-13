import Packet06CyclicRotation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Every unit normal is reached by two axial rotations and one proper cyclic conjugation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07PlaneFrame
open Maxwell ModalAxialRotation Packet06CyclicRotation
abbrev Space := Maxwell.Space

def normalRotation (θ φ : ℝ) : Space ≃ₗᵢ[ℝ] Space :=
  (((Packet06CyclicRotation.rotation.trans (ModalAxialRotation.rotation φ)).trans
    Packet06CyclicRotation.rotation.symm).trans (ModalAxialRotation.rotation θ))

theorem normal_rotation_basis (θ φ : ℝ) :
    normalRotation θ φ (EuclideanSpace.single 2 1) =
      (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![Real.cos θ*Real.sin φ, Real.sin θ*Real.sin φ, Real.cos φ] := by
  change ModalAxialRotation.spatial θ (Packet06CyclicRotation.unrotate
    (ModalAxialRotation.spatial φ (Packet06CyclicRotation.rotate (EuclideanSpace.single 2 1)))) = _
  ext i
  fin_cases i <;> simp [normalRotation,ModalAxialRotation.rotation,ModalAxialRotation.spatial,
    Packet06CyclicRotation.rotation,Packet06CyclicRotation.rotate,Packet06CyclicRotation.unrotate,
    WeakCurl.previous,WeakCurl.next,EuclideanSpace.single_apply]

theorem exists_frame (n : Space) (hn : ‖n‖=1) :
    ∃ θ φ : ℝ, normalRotation θ φ (EuclideanSpace.single 2 1)=n := by
  let w : ℂ := ⟨n 0,n 1⟩
  let ρ : ℝ := ‖w‖
  let v : ℂ := ⟨n 2,ρ⟩
  have hn2 : (n 0)^2+(n 1)^2+(n 2)^2=1 := by
    have h : ‖n‖^2=1 := by rw [hn]; norm_num
    rw [PiLp.norm_sq_eq_of_L2] at h
    simpa only [Fin.sum_univ_three,Real.norm_eq_abs,sq_abs] using h
  have hρ : ρ^2=(n 0)^2+(n 1)^2 := by
    dsimp [ρ,w]
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.ofReal_re,Complex.ofReal_im]
    ring
  have hv : ‖v‖=1 := by
    have hv2 : ‖v‖^2=1 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      dsimp [v]
      nlinarith
    nlinarith [norm_nonneg v]
  have hwc : ρ*Real.cos (Complex.arg w)=n 0 := by simpa only [w,Complex.ofReal_re,Complex.ofReal_im] using Complex.norm_mul_cos_arg w
  have hws : ρ*Real.sin (Complex.arg w)=n 1 := by simpa only [w,Complex.ofReal_re,Complex.ofReal_im] using Complex.norm_mul_sin_arg w
  have hvc : Real.cos (Complex.arg v)=n 2 := by simpa [hv,v] using Complex.norm_mul_cos_arg v
  have hvs : Real.sin (Complex.arg v)=ρ := by simpa [hv,v] using Complex.norm_mul_sin_arg v
  refine ⟨Complex.arg w,Complex.arg v,?_⟩
  rw [normal_rotation_basis]
  ext i
  fin_cases i <;> simp [hvc,hvs,hwc,hws,mul_comm]
end OQ14.Packet07PlaneFrame
#print axioms OQ14.Packet07PlaneFrame.normal_rotation_basis
#print axioms OQ14.Packet07PlaneFrame.exists_frame
