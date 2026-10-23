import HarmonicHalfTurn
import SolidScalarHelmholtz
import FischerDecomposition

/-! Actual even-degree half-turn projection and its scalar-wave symmetries. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.EvenHarmonicProjection
open Maxwell HarmonicPolynomial

def project (l : ℕ) (p : Poly) : Poly := if Even l then HarmonicHalfTurn.project p else 0

theorem homogeneous (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) : (project l p).IsHomogeneous l := by
  unfold project
  split_ifs with he
  · exact HarmonicHalfTurn.project_homogeneous p l hp
  · exact MvPolynomial.isHomogeneous_zero (Fin 3) ℝ l

theorem harmonic (p : Poly) (l : ℕ) (hp : formalLaplacian p=0) : formalLaplacian (project l p)=0 := by
  unfold project
  split_ifs with he
  · exact HarmonicHalfTurn.project_harmonic p hp
  · exact map_zero _

theorem invariant (p : Poly) (l : ℕ) (x : Space) :
    evaluate (project l p) (HarmonicHalfTurn.rotation x)=evaluate (project l p) x := by
  unfold project
  split_ifs with he
  · exact HarmonicHalfTurn.project_invariant p x
  · simp [evaluate]

theorem central_even (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (x : Space) :
    evaluate (project l p) (-x)=evaluate (project l p) x := by
  by_cases he : Even l
  · have h := FischerDecomposition.evaluate_smul (HarmonicHalfTurn.project p) l
      (HarmonicHalfTurn.project_homogeneous p l hp) (-1) x
    simpa only [project,if_pos he,neg_one_smul,he.neg_one_pow,one_mul] using h
  · simp [project,he,evaluate]

theorem equator_even (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (x : Space) :
    evaluate (project l p) (SphereReactionKernel.reflect x)=evaluate (project l p) x := by
  have he : SphereReactionKernel.reflect x= -HarmonicHalfTurn.rotation x := by
    rw [HarmonicHalfTurn.rotation_apply,neg_neg]
  rw [he,central_even p l hp,invariant]

theorem wave_invariant (p : Poly) (l : ℕ) (k : ℝ) (x : Space) :
    SolidScalarHelmholtz.wave l k (project l p) (HarmonicHalfTurn.rotation x)=
      SolidScalarHelmholtz.wave l k (project l p) x := by
  simp only [SolidScalarHelmholtz.wave,HarmonicHalfTurn.rotation.norm_map,complexEvaluate,invariant]

theorem wave_central_even (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (k : ℝ) (x : Space) :
    SolidScalarHelmholtz.wave l k (project l p) (-x)=SolidScalarHelmholtz.wave l k (project l p) x := by
  simp only [SolidScalarHelmholtz.wave,norm_neg,complexEvaluate,central_even p l hp]

end OQ14.EvenHarmonicProjection
#print axioms OQ14.EvenHarmonicProjection.homogeneous
#print axioms OQ14.EvenHarmonicProjection.harmonic
#print axioms OQ14.EvenHarmonicProjection.invariant
#print axioms OQ14.EvenHarmonicProjection.central_even
#print axioms OQ14.EvenHarmonicProjection.equator_even
#print axioms OQ14.EvenHarmonicProjection.wave_invariant
#print axioms OQ14.EvenHarmonicProjection.wave_central_even
