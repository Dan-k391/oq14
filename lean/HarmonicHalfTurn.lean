import HarmonicRotation
import SphereMagneticParity

/-! Actual orthogonal half-turn and symmetry projection on homogeneous harmonic polynomials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HarmonicHalfTurn
open Maxwell HarmonicPolynomial

theorem reflect_norm (x : Space) : ‖SphereReactionKernel.reflect x‖=‖x‖ := by
  have he : ‖SphereReactionKernel.reflect x‖^2=‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_three,SphereReactionKernel.reflect,SphereReactionKernel.sign,Real.norm_eq_abs,sq_abs]
  nlinarith [norm_nonneg x,norm_nonneg (SphereReactionKernel.reflect x)]

def rotation : Space ≃ₗᵢ[ℝ] Space :=
  { LinearEquiv.ofInvolutive (-SphereMagneticParity.reflection).toLinearMap (by
      intro x
      ext i
      fin_cases i <;> simp [ContinuousLinearMap.neg_apply,SphereMagneticParity.reflection_apply,
        SphereReactionKernel.reflect,SphereReactionKernel.sign]) with
    norm_map' := fun x => by
      change ‖-SphereMagneticParity.reflection x‖=‖x‖
      rw [norm_neg,SphereMagneticParity.reflection_apply,reflect_norm] }

theorem rotation_apply (x : Space) : rotation x= -SphereReactionKernel.reflect x := by
  change -SphereMagneticParity.reflection x= -SphereReactionKernel.reflect x
  rw [SphereMagneticParity.reflection_apply]

theorem rotation_involutive (x : Space) : rotation (rotation x)=x := by
  ext i
  fin_cases i <;> simp [rotation_apply,SphereReactionKernel.reflect,SphereReactionKernel.sign]

def project (p : Poly) : Poly := (1/2 : ℝ) • (p+HarmonicRotation.rotate rotation p)

theorem project_homogeneous (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) : (project p).IsHomogeneous l := by
  simpa only [project,Algebra.smul_def] using
    (hp.add (HarmonicRotation.rotate_homogeneous rotation p l hp)).C_mul (1/2 : ℝ)

theorem project_harmonic (p : Poly) (hp : formalLaplacian p=0) : formalLaplacian (project p)=0 := by
  simp only [project,map_smul,map_add,hp,HarmonicRotation.rotate_harmonic rotation p hp,add_zero,smul_zero]

theorem project_invariant (p : Poly) (x : Space) : evaluate (project p) (rotation x)=evaluate (project p) x := by
  have he (y : Space) : evaluate (project p) y=(1/2 : ℝ)*(evaluate p y+evaluate (HarmonicRotation.rotate rotation p) y) := by
    simp [project,evaluate,Algebra.smul_def]
  rw [he,he,HarmonicRotation.rotate_evaluate,HarmonicRotation.rotate_evaluate,rotation_involutive]
  ring

end OQ14.HarmonicHalfTurn
#print axioms OQ14.HarmonicHalfTurn.reflect_norm
#print axioms OQ14.HarmonicHalfTurn.rotation_apply
#print axioms OQ14.HarmonicHalfTurn.rotation_involutive
#print axioms OQ14.HarmonicHalfTurn.project_homogeneous
#print axioms OQ14.HarmonicHalfTurn.project_harmonic
#print axioms OQ14.HarmonicHalfTurn.project_invariant
