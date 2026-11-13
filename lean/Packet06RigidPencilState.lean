import Packet06CyclicAxialKernel

/-! Successive rigid transformations retain the full actual pencil and
compact support, with an explicit invertible L² embedding. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidPencilState
open Metric Maxwell ModalAxialRotation Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06AxialMaterialTransport Packet06CyclicAxialKernel
abbrev V := VectorFourier.VectorL2

structure State (c₀ : StaticCoefficient.Coefficient) (R₀ : ℝ) where
  material : StaticCoefficient.Coefficient
  radius : ℝ
  nonnegative : 0 ≤ radius
  support : ∀ x : Space, x ∉ closedBall 0 radius → material.value (VectorFourier.coordinateMap x)=0
  embedding : V ≃L[ℂ] V
  pencil : ∀ z : ℂ, ∀ u : V, ComplexConvolutionAnalytic.pencil material z radius (embedding u) =
    embedding (ComplexConvolutionAnalytic.pencil c₀ z R₀ u)
  volume : ∀ z : ℂ, ∀ u : V, ComplexConvolutionAnalytic.volumeBlock material z radius (embedding u) =
    embedding (ComplexConvolutionAnalytic.volumeBlock c₀ z R₀ u)

def initial (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0) : State c R where
  material := c
  radius := R
  nonnegative := hR
  support := hc
  embedding := ContinuousLinearEquiv.refl ℂ V
  pencil := fun _ _ => rfl
  volume := fun _ _ => rfl

end OQ14.Packet06RigidPencilState
#print axioms OQ14.Packet06RigidPencilState.initial
