import SourceTECorrection

/-! Actual TE source correction equations on a neighborhood of the origin. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceTENear
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.SourceTECorrection

theorem equation (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (f : DynamicSource.Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) (d.R/2)) :
    ForcedTestLocalization.Equation 1 (polarization d p) (electric d p) (magnetic d p) f := by
  have hreg := TestFieldLocalization.vacuum_smul (multiplier d) 1
    (SolidMaxwellProfiles.magnetic d.l p) (-SolidMaxwellProfiles.electric d.l p)
    (vacuum_dual 1 _ _ (MaterialMaxwell.classical_vacuum_testMaxwell 1 _ _
      (fun i => (SolidMaxwellProfiles.electric_smooth d.l p i).of_le (by simp))
      (fun i => (SolidMaxwellProfiles.magnetic_smooth d.l p i).of_le (by simp))
      (SolidMaxwellProfiles.actual_maxwell d.l p hp hh)))
  apply TestFieldLocalization.equation_congr 1 (fun _ _ => 0) _
    (multiplier d • SolidMaxwellProfiles.magnetic d.l p)
    (multiplier d • (-SolidMaxwellProfiles.electric d.l p)) _ _ f
  · intro x hx
    exact (SourceRegularCorrection.magnetic_inner d p x (mem_ball_zero_iff.mp (hf hx)).le).symm
  · intro x hx
    change multiplier d • (-SolidMaxwellProfiles.electric d.l p x)= -SourceRegularCorrection.electric d p x
    rw [SourceRegularCorrection.electric_inner d p x (mem_ball_zero_iff.mp (hf hx)).le,smul_neg]
  · intro i x hx
    have hn := mem_ball_zero_iff.mp (hf hx)
    exact (polarization_inner d p x (by linarith [d.hR]) i).symm
  · exact fun i => hreg i f

end OQ14.SourceTENear
#print axioms OQ14.SourceTENear.equation
