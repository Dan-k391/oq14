import SourceVolumeRepresentation
import ConicalInteriorResponse

/-! Exact literal dyadic response of one layered source mode throughout the vacuum core. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceCoreVolumeIntegral
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction

theorem correction_core (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (x : Space) (hx : ‖x‖≤d.R) :
    SourceRegularCorrection.electric d p x=multiplier d • SolidMaxwellProfiles.electric d.l p x := by
  by_cases hhalf : ‖x‖≤d.R/2
  · exact SourceRegularCorrection.electric_inner d p x hhalf
  · have hx0 : x≠0 := norm_pos_iff.mp (by linarith [d.hR])
    rw [SourceRegularCorrection.electric_away d p hp hh x hx0]
    exact electric_core_difference d p hp hh x hx0 hx

theorem dyadic_core (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) :
    EqOn (ExteriorContinuity.electric 1 (SourceRegularCorrection.polarization d p))
      (multiplier d • SolidMaxwellProfiles.electric d.l p) (ball (0 : Space) d.R) := by
  have hi (j : Fin 3) (y : Space) (hy : y∈ball (0 : Space) d.R) :
      SourceRegularCorrection.polarization d p j y=0 :=
    SourceRegularCorrection.polarization_inner d p y (show ‖y‖≤d.R from (mem_ball_zero_iff.mp hy).le) j
  have ho (j : Fin 3) (y : Space) (hy : y∉closedBall (0 : Space) d.X) :
      SourceRegularCorrection.polarization d p j y=0 :=
    SourceRegularCorrection.polarization_outer d p y (by simpa only [mem_closedBall,dist_zero_right,not_le] using hy) j
  have hae := ConicalInteriorResponse.electric_ae_interior 1 (SourceVolumeRepresentation.sourceL2 d p)
    (SourceRegularCorrection.polarization d p) (SourceCorrectionLocalBounds.polarization_integrable d p)
    (SourceVolumeRepresentation.sourceL2_actual d p) d.R d.X ho hi
  have heq : ExteriorContinuity.electric 1 (SourceRegularCorrection.polarization d p)
      =ᵐ[volume.restrict (ball (0 : Space) d.R)] multiplier d • SolidMaxwellProfiles.electric d.l p := by
    filter_upwards [ae_restrict_of_ae hae,
      ae_restrict_of_ae (SourceVolumeRepresentation.actual_response d hdisp p hp hh).1,
      ae_restrict_mem measurableSet_ball] with x hg hx hm
    exact (hg hm).symm.trans (hx.symm.trans (correction_core d p hp hh x (mem_ball_zero_iff.mp hm).le))
  apply Measure.eqOn_open_of_ae_eq heq isOpen_ball
  · apply continuousOn_pi.mpr
    intro i x hx
    exact (ConicalInteriorResponse.electric_smooth_interior 1 (SourceRegularCorrection.polarization d p)
      (SourceCorrectionLocalBounds.polarization_integrable d p)
      (SourceCorrectionLocalBounds.polarization_compact d p) d.R hi i x hx).continuousAt.continuousWithinAt
  · exact ((continuous_const : Continuous (fun _ : Space => multiplier d)).smul
      (continuous_pi (fun i => (SolidMaxwellProfiles.electric_smooth d.l p i).continuous))).continuousOn

theorem integral_core (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (x : Space) (hx : ‖x‖<d.R) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, SourceRegularCorrection.polarization d p j y*DyadicKernel.dyadic 1 (x-y) i j)=
      multiplier d*SolidMaxwellProfiles.electric d.l p x i := by
  exact congrFun (dyadic_core d hdisp p hp hh (mem_ball_zero_iff.mpr hx)) i

end OQ14.SourceCoreVolumeIntegral
#print axioms OQ14.SourceCoreVolumeIntegral.correction_core
#print axioms OQ14.SourceCoreVolumeIntegral.dyadic_core
#print axioms OQ14.SourceCoreVolumeIntegral.integral_core
