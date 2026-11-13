import Packet06AffineTraceGeneral
import Packet05OneSidedCollar

/-! The actual one-sided collar certificate transports under a proper cyclic rotation followed by arbitrary
translation with positivity only on that collar. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06AffineOneSidedGeneral
open MeasureTheory Set Metric Maxwell Packet05OneSidedCollar Packet06PlacedKernel
  Packet06PlacementHomeomorph Packet06PlacedPhaseField
abbrev Space := Maxwell.Space

theorem affine_one_sided_general (c : StaticCoefficient.Coefficient) (R T : ℝ)
    (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1) (a : Space)
    (body A : Set Space) (hb : IsOpen body) (hA : IsOpen A) (hAball : A ⊆ closedBall (0 : Space) T)
    (hpos : ∀ x ∈ A, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (B : ℝ) (hcollar : OneSidedCollar c z u body A B) :
    OneSidedCollar (placedCoefficient 1 a c) z (placedUnknown 1 a u)
      (placement 1 (by norm_num) a '' body) (placement 1 (by norm_num) a '' A) B := by
  obtain ⟨inside,outside,hin,hout,hiae,hoae,hbound⟩ := hcollar
  have h := Packet06AffineTraceGeneral.affine_trace_general c R T hR hRT hc z u hu hN a body A A
    hb hA.measurableSet hAball hpos inside outside hin hout hiae hoae B hbound
  exact ⟨transport 1 (by norm_num) a inside,transport 1 (by norm_num) a outside,h⟩
end OQ14.Packet06AffineOneSidedGeneral
#print axioms OQ14.Packet06AffineOneSidedGeneral.affine_one_sided_general
