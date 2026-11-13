import Packet06RigidPencilState
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidPencilState
open Metric Maxwell ModalAxialRotation Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06AxialMaterialTransport Packet06CyclicAxialKernel
def affine {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ} (a : Space) (d : State c₀ R₀) : State c₀ R₀ where
  material := placedCoefficient 1 a d.material
  radius := d.radius+‖a‖
  nonnegative := add_nonneg d.nonnegative (norm_nonneg a)
  support := by simpa using Packet06PlacedPole.coefficient_support d.material d.radius d.support 1 (by norm_num) a
  embedding := d.embedding.trans (placed 1 (by norm_num) a)
  pencil := by
    intro z u
    have h := Packet06PlacedConjugacy.pencil_intertwines d.material d.radius d.nonnegative d.support
      1 (by norm_num) a z (d.embedding u)
    simp only [Complex.ofReal_one,one_mul,div_one,d.pencil] at h
    exact h
  volume := by
    intro z u
    have h := Packet06PlacedConjugacy.volume_intertwines d.material d.radius d.nonnegative d.support
      1 (by norm_num) a z (d.embedding u)
    simp only [Complex.ofReal_one,one_mul,div_one,d.volume] at h
    exact h

end OQ14.Packet06RigidPencilState
#print axioms OQ14.Packet06RigidPencilState.affine
