import Packet06RigidStateEmbedding
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateObservedPole
open Metric Maxwell Packet06SectorOperator Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06GenericSectorConjugate Packet06RigidPencilState Packet06RigidStateSector
theorem certified_observed_pole (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : Sector)
    (hcert : Packet06SimpleCertificate.Certified c R z u)
    (d : State (placedCoefficient s a c) (R/s+‖a‖)) :
    Packet06GenericObservedPole.SimpleObservedPole d.material d.radius (embedding d s hs a)
      (pencil d s hs a) ((s : ℂ)*z) u := by
  have hAeq : pencil d s hs a = Packet06PlacedSector.pencil c R s hs a := by
    funext v
    simpa [Packet06PlacedSector.pencil,Packet06GenericSectorConjugate.conjugate] using pencil_eq d s hs a v
  have hbase : ComplexConvolutionAnalytic.volumeBlock c z R (u : VectorL2)=0 := by
    obtain ⟨_,_,_,hku,_,_⟩ := hcert
    exact hku
  have hp : ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z)
      (R/s+‖a‖) (placed s hs a (u : VectorL2))=0 := by
    rw [Packet06PlacedConjugacy.volume_intertwines c R hR hc s hs a z u,hbase,map_zero]
  have hker : ComplexConvolutionAnalytic.volumeBlock d.material ((s : ℂ)*z) d.radius (embedding d s hs a u)=0 := by
    change ComplexConvolutionAnalytic.volumeBlock d.material ((s : ℂ)*z) d.radius
      (d.embedding (placed s hs a (u : VectorL2)))=0
    rw [d.volume,hp,map_zero]
  have hne : embedding d s hs a u ≠ 0 := by
    intro he
    have he' : embedding d s hs a u = embedding d s hs a 0 := by simpa using he
    exact Packet06SimpleCertificate.certified_nonzero c R z u hcert (embedding_injective d s hs a he')
  exact Packet06TransportedObservedPole.certified_transport c d.material R d.radius hR d.nonnegative hc d.support
    ha hm s hs a z u hcert (embedding d s hs a) (pencil d s hs a) hAeq hker hne
end OQ14.Packet06RigidStateObservedPole
#print axioms OQ14.Packet06RigidStateObservedPole.certified_observed_pole
