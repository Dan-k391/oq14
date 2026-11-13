import Packet06RigidPencilState
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidPencilState
open Metric Maxwell ModalAxialRotation Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06AxialMaterialTransport Packet06CyclicAxialKernel
def axial {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ} (θ : ℝ) (d : State c₀ R₀) : State c₀ R₀ where
  material := coefficient θ d.material
  radius := d.radius
  nonnegative := d.nonnegative
  support := axial_support θ d.material d.radius d.support
  embedding := d.embedding.trans (Packet06AxialEquivalence.equivalence θ)
  pencil := by
    intro z u
    change ComplexConvolutionAnalytic.pencil (coefficient θ d.material) z d.radius
      (action θ (d.embedding u)) = action θ (d.embedding (ComplexConvolutionAnalytic.pencil c₀ z R₀ u))
    rw [Packet06AxialPencilTransport.pencil_intertwines θ d.material d.radius d.nonnegative d.support,
      d.pencil]
  volume := by
    intro z u
    change ComplexConvolutionAnalytic.volumeBlock (coefficient θ d.material) z d.radius
      (action θ (d.embedding u)) = action θ (d.embedding (ComplexConvolutionAnalytic.volumeBlock c₀ z R₀ u))
    rw [Packet06AxialPencilTransport.volume_intertwines θ d.material d.radius d.nonnegative d.support,
      d.volume]

end OQ14.Packet06RigidPencilState
#print axioms OQ14.Packet06RigidPencilState.axial
