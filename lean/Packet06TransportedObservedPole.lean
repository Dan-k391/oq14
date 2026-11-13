import Packet06GenericObservedPole

/-! The original certified pole remains an actual observed pole for any
transported physical material whose embedded mode and pencil are exactly
identified with the original selected-sector data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
namespace OQ14.Packet06TransportedObservedPole
open Metric Maxwell Packet06SectorOperator Packet06PlacedKernel Packet06PlacedEquivalence

theorem certified_transport (c d : StaticCoefficient.Coefficient) (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (hd : ∀ x : Space, x ∉ closedBall 0 S → d.value (VectorFourier.coordinateMap x)=0)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : Sector)
    (hcert : Packet06SimpleCertificate.Certified c R z u)
    (J : Sector →L[ℂ] VectorL2) (A : ℂ → Sector →L[ℂ] Sector)
    (hAeq : A = Packet06PlacedSector.pencil c R s hs a)
    (hker : ComplexConvolutionAnalytic.volumeBlock d ((s : ℂ)*z) S (J u)=0)
    (hne : J u ≠ 0) :
    Packet06GenericObservedPole.SimpleObservedPole d S J A ((s : ℂ)*z) u := by
  obtain ⟨w,ψ,hC,hk,hψ,hds⟩ := Packet06PlacedSchur.certified_schur c ha hm R hR hc s hs a z u hcert
  rw [← hAeq] at hC hk hds
  have han : AnalyticAt ℂ A ((s : ℂ)*z) := by
    rw [hAeq]
    exact Packet06PlacedSchur.pencil_analyticAt c R hR hc s hs a _
  exact Packet06GenericObservedPole.observed_of_simple d S hS hd J A ((s : ℂ)*z) u w ψ han hC hk hψ hds hker hne
end OQ14.Packet06TransportedObservedPole
#print axioms OQ14.Packet06TransportedObservedPole.certified_transport
