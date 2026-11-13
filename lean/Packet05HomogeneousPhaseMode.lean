import Packet05HomogeneousActualMode
import Packet05BoundaryMaterialMode
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05HomogeneousPhaseMode
open MeasureTheory Set Maxwell Packet05HomogeneousActualMode Packet05BoundaryMaterialMode

/-- A homogeneous actual mode supplies both literal material-phase representatives
at the point, without any regularity hypothesis on the field. -/
theorem homogeneous_phase_mode
    (c : StaticCoefficient.Coefficient) (z : ℂ) (hz : z ≠ 0) (R : ℝ)
    (mode : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ Metric.closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (hmode : ComplexConvolutionAnalytic.volumeBlock c z R mode=0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (x : Space) (hx : x ∈ Ω)
    (host : ℂ) (hhost : host ≠ 0)
    (hε : ∀ y ∈ Ω, Packet06MaxwellScalarEquation.epsilon c y = host) (body : Set Space) :
    HasPhaseRepresentatives
      (Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode) (DynamicVolume.source c mode)) body x := by
  obtain ⟨U,reps,hU,hxU,_,hcont,hae⟩ :=
    actual_homogeneous_neighborhood c z hz R mode hc hmode Ω hΩ x hx host hhost hε
  refine ⟨U,reps,reps,hU,hxU,hcont,hcont,?_,?_⟩
  · intro j
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae j)
  · intro j
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae j)

#print axioms OQ14.Packet05HomogeneousPhaseMode.homogeneous_phase_mode
end OQ14.Packet05HomogeneousPhaseMode
