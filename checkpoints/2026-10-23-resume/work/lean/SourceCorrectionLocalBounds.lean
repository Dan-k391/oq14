import SourceRegularCorrection
import SourceLocalBounds
import SourceRadiatingTrace
import RadiatingTraceTransport

/-! Genuine local L2 and outgoing trace of the actual origin-corrected source difference. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceCorrectionLocalBounds
open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
open OQ14.SourceCoreReaction OQ14.SourceLocalBounds
open scoped Topology

def clipped (d : Data) : Data := SourceUnclippedMaxwell.reclip d (d.R/4) (by linarith [d.hR])

theorem electric_memLp_ball (d : Data) (P : Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => SourceRegularCorrection.electric d P x i) 2 (volume.restrict (closedBall 0 T)) := by
  let f := fun x => multiplier d*SolidMaxwellProfiles.electric d.l P x i
  let g := fun x => SourceElectricProfiles.electric (clipped d) P x i-
    SourceElectricProfiles.electric (clipped (vacuum d)) P x i
  have hf : Continuous f := continuous_const.mul (SolidMaxwellProfiles.electric_smooth d.l P i).continuous
  have hg : MemLp g 2 (volume.restrict (closedBall 0 T)) :=
    (SourceLocalBounds.electric_memLp_ball (clipped d) P T i).sub
      (SourceLocalBounds.electric_memLp_ball (clipped (vacuum d)) P T i)
  have h := piecewise_memLp_ball (d.R/2) T f g hf hg
  convert h using 1
  funext x
  dsimp [SourceRegularCorrection.electric]
  split_ifs with hx
  · rfl
  · have hr : d.R/4<‖x‖ := by linarith [d.hR]
    have hE := congrFun (SourceUnclippedMaxwell.electric_agrees d (d.R/4) (by linarith [d.hR]) P x hr) i
    have hV := congrFun (SourceUnclippedMaxwell.electric_agrees (vacuum d) (d.R/4) (by linarith [d.hR]) P x hr) i
    change _=g x
    dsimp only [g,clipped,vacuum] at hE hV ⊢
    rw [hE,hV]
    rfl

theorem magnetic_memLp_ball (d : Data) (P : Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => SourceRegularCorrection.magnetic d P x i) 2 (volume.restrict (closedBall 0 T)) := by
  let f := fun x => multiplier d*SolidMaxwellProfiles.magnetic d.l P x i
  let g := fun x => SourceElectricProfiles.magnetic (clipped d) P x i-
    SourceElectricProfiles.magnetic (clipped (vacuum d)) P x i
  have hf : Continuous f := continuous_const.mul (SolidMaxwellProfiles.magnetic_smooth d.l P i).continuous
  have hg : MemLp g 2 (volume.restrict (closedBall 0 T)) :=
    (SourceLocalBounds.magnetic_memLp_ball (clipped d) P T i).sub
      (SourceLocalBounds.magnetic_memLp_ball (clipped (vacuum d)) P T i)
  have h := piecewise_memLp_ball (d.R/2) T f g hf hg
  convert h using 1
  funext x
  dsimp [SourceRegularCorrection.magnetic]
  split_ifs with hx
  · rfl
  · have hr : d.R/4<‖x‖ := by linarith [d.hR]
    have hE := congrFun (SourceUnclippedMaxwell.magnetic_agrees d (d.R/4) (by linarith [d.hR]) P x hr) i
    have hV := congrFun (SourceUnclippedMaxwell.magnetic_agrees (vacuum d) (d.R/4) (by linarith [d.hR]) P x hr) i
    change _=g x
    dsimp only [g,clipped,vacuum] at hE hV ⊢
    rw [hE,hV]
    rfl

theorem electric_locallyIntegrable (d : Data) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SourceRegularCorrection.electric d P x i) :=
  HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => electric_memLp_ball d P T i)

theorem magnetic_locallyIntegrable (d : Data) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SourceRegularCorrection.magnetic d P x i) :=
  HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => magnetic_memLp_ball d P T i)

theorem polarization_memLp (d : Data) (P : Poly) (i : Fin 3) :
    MemLp (SourceRegularCorrection.polarization d P i) 2 volume := by
  have h := source_memLp (clipped d) (by change d.R/4<d.R;linarith [d.hR]) P i
  exact h

theorem polarization_integrable (d : Data) (P : Poly) (i : Fin 3) :
    Integrable (SourceRegularCorrection.polarization d P i) := by
  have h := source_integrable (clipped d) (by change d.R/4<d.R;linarith [d.hR]) P i
  exact h

theorem polarization_compact (d : Data) (P : Poly) (i : Fin 3) :
    HasCompactSupport (SourceRegularCorrection.polarization d P i) := source_compact d P i

def trace (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    RadiatingTrace.Trace 1 (SourceRegularCorrection.electric d P) (SourceRegularCorrection.magnetic d P) :=
  RadiatingTraceTransport.exteriorCongr (SourceRadiatingTrace.tm_difference_trace d P hp) (d.R/2)
    (fun x hx => by
      change (if ‖x‖≤d.R/2 then _ else _)=_
      rw [if_neg (not_le.mpr hx)]
      rfl)
    (fun x hx => by
      change (if ‖x‖≤d.R/2 then _ else _)=_
      rw [if_neg (not_le.mpr hx)]
      rfl)

def dual_trace (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    RadiatingTrace.Trace 1 (SourceRegularCorrection.magnetic d P) (-SourceRegularCorrection.electric d P) :=
  SourceRadiatingTrace.dual_trace (trace d P hp)

end OQ14.SourceCorrectionLocalBounds

#print axioms OQ14.SourceCorrectionLocalBounds.electric_memLp_ball
#print axioms OQ14.SourceCorrectionLocalBounds.magnetic_memLp_ball
#print axioms OQ14.SourceCorrectionLocalBounds.electric_locallyIntegrable
#print axioms OQ14.SourceCorrectionLocalBounds.magnetic_locallyIntegrable
#print axioms OQ14.SourceCorrectionLocalBounds.polarization_memLp
#print axioms OQ14.SourceCorrectionLocalBounds.polarization_integrable
#print axioms OQ14.SourceCorrectionLocalBounds.polarization_compact
#print axioms OQ14.SourceCorrectionLocalBounds.trace
#print axioms OQ14.SourceCorrectionLocalBounds.dual_trace
