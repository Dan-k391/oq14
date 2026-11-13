import Packet06WeightedPencilLimit
import Packet06SchurLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06WeightedPencilHolomorphic
open Filter Set MeasureTheory Metric OQ14.StaticCoefficient
open scoped Topology
abbrev Space := FourierL2.Space

theorem pencil_locally_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0) :
    TendstoLocallyUniformlyOn (fun n z => ComplexConvolutionAnalytic.pencil (c n) z R)
      (fun z => ComplexConvolutionAnalytic.pencil c₀ z R) atTop univ := by
  have h := Packet06WeightedPencilLimit.compactPart_locally_uniform c c₀ D R hR hb hb₀ ha hc hc₀
  have hcont := (ComplexConvolutionAnalytic.compactPart_differentiable c₀ R hR).continuous
  have h' := Packet06SchurLimit.locally_uniform_comp univ
    (fun n z => ComplexConvolutionAnalytic.compactPart (c n) z R)
    (fun z => ComplexConvolutionAnalytic.compactPart c₀ z R) (fun B => 1-B)
    h hcont.continuousOn (fun _ _ => (continuous_const.sub continuous_id).continuousAt)
  exact h'
#print axioms OQ14.Packet06WeightedPencilHolomorphic.pencil_locally_uniform
end OQ14.Packet06WeightedPencilHolomorphic
