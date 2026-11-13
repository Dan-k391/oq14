import Packet05OneSidedCollar

/-! The packaged actual one-sided collar survives normalized Maxwell
placement on the literal image of the same open collar. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedOneSidedCollar
open MeasureTheory Set Metric Maxwell Packet05OneSidedCollar Packet06PlacedKernel
  Packet06PlacementHomeomorph Packet06PlacedPhaseField
abbrev Space := Maxwell.Space

theorem placed_one_sided_collar (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (body A : Set Space) (hb : IsOpen body) (hA : IsOpen A) (hAball : A ⊆ ball (0 : Space) 1)
    (B : ℝ) (hcollar : OneSidedCollar c z u body A B)
    (s : ℝ) (hs : 0 < s) (a : Space) :
    OneSidedCollar (placedCoefficient s a c) ((s : ℂ)*z) (placedUnknown s a u)
      (placement s hs a '' body) (placement s hs a '' A) (scale s*B) := by
  obtain ⟨inside,outside,hin,hout,hiae,hoae,hbound⟩ := hcollar
  have h := Packet06PlacedTraceCollar.placed_trace_collar c hc hpos z u hu hN body A A hb hA.measurableSet
    hAball inside outside hin hout hiae hoae B hbound s hs a
  exact ⟨transport s hs a inside,transport s hs a outside,h⟩

end OQ14.Packet06PlacedOneSidedCollar
#print axioms OQ14.Packet06PlacedOneSidedCollar.placed_one_sided_collar
