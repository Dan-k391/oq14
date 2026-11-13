import Packet06RoundedPeakFamily
import Packet05BinaryPhaseMaximum

/-! Positive-volume coordinate peaks of the actual local response are peaks
of the physical Euclidean amplitude of the actual electric field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PhysicalAmplitudePeak
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum

theorem coordinate_peak (K : Set Space) (E : Field) (F : Space → ℂ) (i : Fin 3)
    (hAE : F =ᵐ[volume.restrict K] (fun y => E y i))
    (M : ℝ) (hpeak : 0 < (volume.restrict K) {y | M < ‖F y‖}) :
    0 < (volume.restrict K) {y | M < physicalAmplitude (fun j x => E x j) y} := by
  apply hpeak.trans_le
  apply measure_mono_ae
  filter_upwards [hAE] with y hy hhigh
  change M < ‖F y‖ at hhigh
  rw [hy] at hhigh
  exact hhigh.trans_le (Packet05HighMaximum.component_le_physicalAmplitude (fun j x => E x j) y i)

theorem actual_response_peak (c : StaticCoefficient.Coefficient) (z : ℂ) (S T : ℝ)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x)=0)
    (K : Set Space) (hK : K ⊆ closedBall (0 : Space) T) (i : Fin 3)
    (M : ℝ) (hpeak : 0 < (volume.restrict K) {y | M <
      ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response c z S T u) i y‖}) :
    let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
    0 < (volume.restrict K) {y | M < physicalAmplitude (fun j x => E x j) y} := by
  apply coordinate_peak K _ _ i _ M hpeak
  have he := Packet06ComplexElectric.electric_ae_on_ball z S T (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
    (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u) i
  have hf := NewtonL2.physicalCoordinate_ae (Packet06LocalPencil.response c z S T u) i
  have hh : (fun y => NewtonL2.physicalCoordinate (Packet06LocalPencil.response c z S T u) i y)
      =ᵐ[volume.restrict (closedBall 0 T)]
      (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) y i) := by
    filter_upwards [ae_restrict_of_ae hf,he] with y hf he
    exact hf.trans he
  exact ae_restrict_of_ae_restrict_of_subset hK hh

end OQ14.Packet06PhysicalAmplitudePeak
#print axioms OQ14.Packet06PhysicalAmplitudePeak.coordinate_peak
#print axioms OQ14.Packet06PhysicalAmplitudePeak.actual_response_peak
