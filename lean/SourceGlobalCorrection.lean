import SourcePuncturedCorrection
import SourceCorrectionLocalBounds

/-! Actual global forced Maxwell equations for the regularized layered source correction. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceGlobalCorrection
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceRegularCorrection

theorem forced_maxwell (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) :
    ForcedMaxwellResponse.TestForced 1 (polarization d p) (electric d p) (magnetic d p) := by
  exact ForcedTestLocalization.of_near_and_punctured 1 (polarization d p) (electric d p) (magnetic d p)
    (fun i => (SourcePuncturedCorrection.polarization_integrable d p i).locallyIntegrable)
    (SourceCorrectionLocalBounds.electric_locallyIntegrable d p)
    (SourceCorrectionLocalBounds.magnetic_locallyIntegrable d p)
    (ball (0 : Space) (d.R/2)) isOpen_ball (mem_ball_self (by linarith [d.hR]))
    (SourceRegularNear.equation d p hp hh) (SourcePuncturedCorrection.equation d hdisp p hp hh)

end OQ14.SourceGlobalCorrection
#print axioms OQ14.SourceGlobalCorrection.forced_maxwell
