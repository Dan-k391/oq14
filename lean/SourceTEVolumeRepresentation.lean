import SourceTEGlobal
import RadiatingSourceRepresentation

/-! The actual layered TE source correction is its genuine outgoing volume response. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.SourceTEVolumeRepresentation
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceTECorrection

def sourceL2 (d : Data) (p : HarmonicPolynomial.Poly) : VectorFourier.VectorL2 :=
  ∑ i : Fin 3, DynamicConvolution.insert i
    ((SourceMuBounds.polarization_memLp d p i).toLp (polarization d p i))

theorem sourceL2_coordinate (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    NewtonL2.physicalCoordinate (sourceL2 d p) i=
      (SourceMuBounds.polarization_memLp d p i).toLp (polarization d p i) := by
  change DynamicConvolution.component i (∑ j : Fin 3,DynamicConvolution.insert j _) = _
  simp only [map_sum,DynamicConvolution.component_insert]
  simp

theorem sourceL2_actual (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    (NewtonL2.physicalCoordinate (sourceL2 d p) i : Space → ℂ) =ᵐ[volume] polarization d p i := by
  rw [sourceL2_coordinate]
  exact (SourceMuBounds.polarization_memLp d p i).coeFn_toLp

theorem actual_response (d : Data) (hσ : ∀ g∈d.gs,g.σ=1)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) :
    (electric d p =ᵐ[volume] FieldResponse.electric 1 (sourceL2 d p) (polarization d p)) ∧
      (magnetic d p =ᵐ[volume] MagneticResponse.magnetic 1 (polarization d p)) := by
  apply RadiatingSourceRepresentation.actual_response 1 (by norm_num) d.X
    (d.hR.le.trans (RadialStack.chain_ordered d.chain)) (sourceL2 d p) (polarization d p)
    (SourceMuBounds.polarization_integrable d p)
    (fun i x hx => polarization_outer d p x (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx) i)
    (sourceL2_actual d p) (electric d p) (magnetic d p)
    (SourceMuBounds.electric_memLp_ball d p) (SourceMuBounds.magnetic_memLp_ball d p)
    (SourceTEGlobal.forced_maxwell d hσ p hp hh)
    (fun i x hx => SourceExteriorSmooth.correction_magnetic_smooth d p x hx i)
    (SourceCorrectionLocalBounds.dual_trace d p hp)

end OQ14.SourceTEVolumeRepresentation
#print axioms OQ14.SourceTEVolumeRepresentation.sourceL2_coordinate
#print axioms OQ14.SourceTEVolumeRepresentation.sourceL2_actual
#print axioms OQ14.SourceTEVolumeRepresentation.actual_response
