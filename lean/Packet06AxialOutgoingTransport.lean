import Packet06AxialReciprocalTransport
import Packet06OutgoingMode

/-! The genuinely outgoing unit-normalized physical mode for any axially
rotated bounded material. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06AxialOutgoingTransport
open MeasureTheory Metric Set Maxwell ModalAxialRotation Packet06AxialMaterialTransport
  Packet06AxialComplexTransport Packet06AxialReciprocalTransport Packet06PhysicalNormalization

theorem rotated_normalized_mode (θ : ℝ) (c : StaticCoefficient.Coefficient) (z : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : reciprocalNorm c R z u=1) :
    (∀ x : Maxwell.Space, x ∉ closedBall 0 R → (coefficient θ c).value (VectorFourier.coordinateMap x)=0) ∧
    ComplexConvolutionAnalytic.volumeBlock (coefficient θ c) z R (action θ u)=0 ∧
    reciprocalNorm (coefficient θ c) R z (action θ u)=1 ∧
    Packet06OutgoingMode.IsActualOutgoingMode (coefficient θ c) z R (action θ u) := by
  have hs : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → (coefficient θ c).value (VectorFourier.coordinateMap x)=0 := by
    intro x hx
    rw [coefficient_value]
    apply hc
    simpa [mem_closedBall,dist_zero_right,(rotation (-θ)).norm_map] using hx
  have hk : ComplexConvolutionAnalytic.volumeBlock (coefficient θ c) z R (action θ u)=0 := by
    have hh := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L u)
      (complex_conjugacy θ c R hR hc z)
    simpa [left,right,hu] using hh
  have hn : reciprocalNorm (coefficient θ c) R z (action θ u)=1 := by
    rw [reciprocalNorm_rotation θ c z R hR hc, hN]
  have hne : action θ u ≠ 0 := by
    intro hzero
    rw [hzero] at hn
    simp [reciprocalNorm,KernelReciprocity.vectorPair,KernelReciprocity.scalarPair] at hn
  exact ⟨hs,hk,hn,Packet06OutgoingMode.actual_outgoing_mode (coefficient θ c) z R hR (action θ u) hs hk hne⟩

end OQ14.Packet06AxialOutgoingTransport
#print axioms OQ14.Packet06AxialOutgoingTransport.rotated_normalized_mode
