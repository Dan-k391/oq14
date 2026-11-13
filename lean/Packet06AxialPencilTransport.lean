import Packet06AxialEquivalence
import Packet06PlacedConjugacy

/-! The full actual analytic pencil conjugates under arbitrary axial rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06AxialPencilTransport
open Metric Maxwell ModalAxialRotation Packet06AxialMaterialTransport Packet06AxialComplexTransport
abbrev V := VectorFourier.VectorL2

theorem volume_intertwines (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : V) :
    ComplexConvolutionAnalytic.volumeBlock (coefficient θ c) z R (action θ u) =
      action θ (ComplexConvolutionAnalytic.volumeBlock c z R u) := by
  have h := congrArg (fun A : V →L[ℂ] V => A u) (complex_conjugacy θ c R hR hc z)
  exact h

theorem static_intertwines (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0) (u : V) :
    StaticNewton.volumeBlock (coefficient θ c) (action θ u) = action θ (StaticNewton.volumeBlock c u) := by
  simpa only [ComplexConvolutionAnalytic.volumeBlock,
    ComplexConvolutionAnalytic.weightedRemainder_zero,sub_zero] using volume_intertwines θ c R hR hc 0 u

theorem pencil_intertwines (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : V) :
    ComplexConvolutionAnalytic.pencil (coefficient θ c) z R (action θ u) =
      action θ (ComplexConvolutionAnalytic.pencil c z R u) := by
  let B := StaticNewton.volumeBlock (coefficient θ c)
  have hfactor (d : StaticCoefficient.Coefficient) (w : ℂ) (S : ℝ) (v : V) :
      StaticNewton.volumeBlock d (ComplexConvolutionAnalytic.pencil d w S v) =
        ComplexConvolutionAnalytic.volumeBlock d w S v :=
    congrArg (fun A : V →L[ℂ] V => A v) (ComplexConvolutionAnalytic.volumeBlock_factor d w S).symm
  have he : B (ComplexConvolutionAnalytic.pencil (coefficient θ c) z R (action θ u)) =
      B (action θ (ComplexConvolutionAnalytic.pencil c z R u)) := by
    dsimp only [B]
    rw [hfactor,volume_intertwines θ c R hR hc z u,static_intertwines θ c R hR hc _,hfactor]
  have hInv (v : V) : Ring.inverse B (B v)=v := by
    change (Ring.inverse B*B) v=v
    rw [Ring.inverse_mul_cancel _ (StaticNewton.volumeBlock_isUnit _)]
    rfl
  simpa only [hInv] using congrArg (fun v : V => Ring.inverse B v) he

end OQ14.Packet06AxialPencilTransport
#print axioms OQ14.Packet06AxialPencilTransport.volume_intertwines
#print axioms OQ14.Packet06AxialPencilTransport.static_intertwines
#print axioms OQ14.Packet06AxialPencilTransport.pencil_intertwines
