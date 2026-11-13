import Packet06RigidPencilAxial
import Packet06RigidPencilAffine
import Packet06TransportedObservedPole

/-! The actual observed simple pole follows any finite chain of the
constructed rigid pencil states, in the explicitly transported sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 20000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateSector
open Metric Maxwell Packet06SectorOperator Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06GenericSectorConjugate Packet06RigidPencilState

def embedding {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ} (d : State c₀ R₀)
    (s : ℝ) (hs : 0 < s) (a : Space) : Sector →L[ℂ] VectorL2 :=
  d.embedding.toContinuousLinearMap.comp ((placed s hs a).toContinuousLinearMap.comp Sector.subtypeL)

def pencil {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ} (d : State c₀ R₀)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) : Sector →L[ℂ] Sector :=
  Packet06SectorFamily.compression (conjugate (placed s hs a)
    (conjugate d.embedding (ComplexConvolutionAnalytic.pencil d.material z d.radius)))

end OQ14.Packet06RigidStateSector
