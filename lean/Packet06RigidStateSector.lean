import Packet06RigidStateSectorDefs
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateSector
open Metric Maxwell Packet06SectorOperator Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06GenericSectorConjugate Packet06RigidPencilState
theorem pencil_eq {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ} (d : State c₀ R₀)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) :
    pencil d s hs a z = Packet06SectorFamily.compression (conjugate (placed s hs a) (ComplexConvolutionAnalytic.pencil c₀ z R₀)) := by
  have he : conjugate d.embedding (ComplexConvolutionAnalytic.pencil d.material z d.radius) =
      ComplexConvolutionAnalytic.pencil c₀ z R₀ :=
    conjugate_eq d.embedding _ _ (d.pencil z)
  change Packet06SectorFamily.compression (conjugate (placed s hs a)
    (conjugate d.embedding (ComplexConvolutionAnalytic.pencil d.material z d.radius))) = _
  rw [he]

end OQ14.Packet06RigidStateSector
#print axioms OQ14.Packet06RigidStateSector.pencil_eq
