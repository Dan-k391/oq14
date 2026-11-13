import Packet06RigidFullSync
import Packet06TransportedObservedPole
import Packet06RigidStateEmbeddingApply

/-! An arbitrary matching physical state and its full frame retain the
actual observed simple pole of the same certified base mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidGenericPole
open Metric Maxwell Packet06SectorOperator Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06RigidPencilState Packet06RigidStateSector Packet06RigidStateSync Packet06FullFrameObservedPole

theorem same_actual_observed_pole {N : ℕ} {r M B : ℝ} (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : Sector)
    (hcert : Packet06SimpleCertificate.Certified c R z u)
    (q : Packet06RigidHotspotState.State N ((s : ℂ)*z) r M B)
    (hmat : q.material = placedCoefficient s a c) (hrad : q.supportRadius = R/s+‖a‖)
    (hunk : q.unknown = placedUnknown s a u) (θ φ : ℝ) (t : Space) :
    let p := full θ φ t (initial q.material q.supportRadius q.support_nonnegative q.support)
    let d := Packet06RigidHotspotFrame.transform θ φ t q
    embedding p s hs a u = d.unknown ∧
    Packet06GenericObservedPole.SimpleObservedPole d.material d.supportRadius (embedding p s hs a)
      (pencil p s hs a) ((s : ℂ)*z) u := by
  let p := full θ φ t (initial q.material q.supportRadius q.support_nonnegative q.support)
  let d := Packet06RigidHotspotFrame.transform θ φ t q
  have hsync := full_sync θ φ t q
  have hmode : embedding p s hs a u = d.unknown := by
    rw [Packet06RigidStateEmbeddingApply.embedding_apply, ← hunk]
    exact hsync.2.2
  refine ⟨hmode,?_⟩
  have hAeq : pencil p s hs a = Packet06PlacedSector.pencil c R s hs a := by
    funext w
    rw [pencil_eq p s hs a w,hmat,hrad]
    rfl
  have hker : ComplexConvolutionAnalytic.volumeBlock d.material ((s : ℂ)*z) d.supportRadius (embedding p s hs a u)=0 := by
    rw [hmode]
    exact d.kernel
  have hne : embedding p s hs a u ≠ 0 := by
    intro he
    have he' : embedding p s hs a u = embedding p s hs a 0 := by simpa using he
    exact Packet06SimpleCertificate.certified_nonzero c R z u hcert (embedding_injective p s hs a he')
  exact Packet06TransportedObservedPole.certified_transport c d.material R d.supportRadius hR d.support_nonnegative hc d.support
    ha hm s hs a z u hcert (embedding p s hs a) (pencil p s hs a) hAeq hker hne
end OQ14.Packet06RigidGenericPole
#print axioms OQ14.Packet06RigidGenericPole.same_actual_observed_pole
