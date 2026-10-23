import TestFieldLocalization

/-! Literal source correction equations on a neighborhood containing the origin. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceRegularNear
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.SourceRegularCorrection

theorem equation (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (f : DynamicSource.Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) (d.R/2)) :
    ForcedTestLocalization.Equation 1 (polarization d p) (electric d p) (magnetic d p) f := by
  have hreg := TestFieldLocalization.vacuum_smul (multiplier d) 1
    (SolidMaxwellProfiles.electric d.l p) (SolidMaxwellProfiles.magnetic d.l p)
    (MaterialMaxwell.classical_vacuum_testMaxwell 1 _ _
      (fun i => (SolidMaxwellProfiles.electric_smooth d.l p i).of_le (by simp))
      (fun i => (SolidMaxwellProfiles.magnetic_smooth d.l p i).of_le (by simp))
      (SolidMaxwellProfiles.actual_maxwell d.l p hp hh))
  apply TestFieldLocalization.equation_congr 1 (fun _ _ => 0) _
    (multiplier d • SolidMaxwellProfiles.electric d.l p)
    (multiplier d • SolidMaxwellProfiles.magnetic d.l p) _ _ f
  · intro x hx
    exact (electric_inner d p x (show ‖x‖≤d.R/2 from (by simpa only [mem_ball,dist_zero_right] using hf hx : ‖x‖<d.R/2).le)).symm
  · intro x hx
    exact (magnetic_inner d p x (show ‖x‖≤d.R/2 from (by simpa only [mem_ball,dist_zero_right] using hf hx : ‖x‖<d.R/2).le)).symm
  · intro i x hx
    have hn : ‖x‖<d.R/2 := by simpa only [mem_ball,dist_zero_right] using hf hx
    exact (polarization_inner d p x (by linarith [d.hR]) i).symm
  · exact fun i => hreg i f

end OQ14.SourceRegularNear
#print axioms OQ14.SourceRegularNear.equation
