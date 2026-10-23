import SourceCoreReaction
import ForcedTestLocalization

/-! The layered outgoing source correction with its actual regular value at the origin. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.SourceRegularCorrection
open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open scoped Topology

def electric (d : Data) (p : HarmonicPolynomial.Poly) : Field := fun x =>
  if ‖x‖≤d.R/2 then multiplier d • SolidMaxwellProfiles.electric d.l p x
  else SourceUnclippedMaxwell.electric d p x-SourceUnclippedMaxwell.electric (vacuum d) p x

def magnetic (d : Data) (p : HarmonicPolynomial.Poly) : Field := fun x =>
  if ‖x‖≤d.R/2 then multiplier d • SolidMaxwellProfiles.magnetic d.l p x
  else SourceUnclippedMaxwell.magnetic d p x-SourceUnclippedMaxwell.magnetic (vacuum d) p x

def polarization (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) (x : Space) : ℂ :=
  (sigma d ‖x‖-1)*SourceUnclippedMaxwell.electric d p x i

theorem electric_away (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (x : Space) (hx : x≠0) :
    electric d p x=SourceUnclippedMaxwell.electric d p x-SourceUnclippedMaxwell.electric (vacuum d) p x := by
  unfold electric
  split_ifs with h
  · exact (electric_core_difference d p hp hh x hx (by linarith [d.hR])).symm
  · rfl

theorem magnetic_away (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) (hx : x≠0) :
    magnetic d p x=SourceUnclippedMaxwell.magnetic d p x-SourceUnclippedMaxwell.magnetic (vacuum d) p x := by
  unfold magnetic
  split_ifs with h
  · exact (magnetic_core_difference d p x hx (by linarith [d.hR])).symm
  · rfl

theorem electric_inner (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) (hx : ‖x‖≤d.R/2) :
    electric d p x=multiplier d • SolidMaxwellProfiles.electric d.l p x := if_pos hx

theorem magnetic_inner (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) (hx : ‖x‖≤d.R/2) :
    magnetic d p x=multiplier d • SolidMaxwellProfiles.magnetic d.l p x := if_pos hx

theorem polarization_inner (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) (hx : ‖x‖≤d.R) (i : Fin 3) :
    polarization d p i x=0 := by simp [polarization,sigma,SourceRadialSystem.extend,hx]

theorem polarization_outer (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    polarization d p i x=0 := by
  unfold polarization sigma SourceRadialSystem.extend
  split_ifs <;> simp_all [not_le.mpr hx]

theorem vacuum_sigma (d : Data) (r : ℝ) : sigma (vacuum d) r=1 := by
  simp only [sigma,SourceRadialSystem.extend,vacuum]
  split_ifs <;> simp_all

end OQ14.SourceRegularCorrection
#print axioms OQ14.SourceRegularCorrection.electric_away
#print axioms OQ14.SourceRegularCorrection.magnetic_away
#print axioms OQ14.SourceRegularCorrection.electric_inner
#print axioms OQ14.SourceRegularCorrection.magnetic_inner
#print axioms OQ14.SourceRegularCorrection.polarization_inner
#print axioms OQ14.SourceRegularCorrection.polarization_outer
#print axioms OQ14.SourceRegularCorrection.vacuum_sigma
