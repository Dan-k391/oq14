import SourceTEPunctured
import SourceTENear
import SourceMuBounds

/-! Global forced Maxwell equations for the actual corrected TE source mode. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceTEGlobal
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceTECorrection

theorem forced_maxwell (d : Data) (hσ : ∀ g∈d.gs,g.σ=1)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) :
    ForcedMaxwellResponse.TestForced 1 (polarization d p) (electric d p) (magnetic d p) := by
  exact ForcedTestLocalization.of_near_and_punctured 1 (polarization d p) (electric d p) (magnetic d p)
    (fun i => (SourceMuBounds.polarization_integrable d p i).locallyIntegrable)
    (SourceMuBounds.electric_locallyIntegrable d p)
    (SourceMuBounds.magnetic_locallyIntegrable d p)
    (ball (0 : Space) (d.R/2)) isOpen_ball (mem_ball_self (by linarith [d.hR]))
    (SourceTENear.equation d p hp hh)
    (SourceTEPunctured.equation d hσ p hp hh (SourceMuBounds.polarization_integrable d p))

end OQ14.SourceTEGlobal
#print axioms OQ14.SourceTEGlobal.forced_maxwell
