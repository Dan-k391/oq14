import Packet06AffineModalExistence
import Packet06RigidFullSync
import Packet06RoundedPlacedPole

/-! The actual affine-frame device retains its nonzero observed simple pole
in the literal transported electric sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet06AffineModalPole
open Set Metric Maxwell Packet06ModalHotspotExistence Packet06ModalRetainedExistence Packet06RigidInitial
  Packet06RigidHotspotState Packet06RigidHotspotFrame Packet06RigidPencilState Packet06FullFrameObservedPole
  Packet06PlacedKernel Packet06PlacedEquivalence

theorem final_observed_pole {N : ℕ} (d : Device N) (K target Q ρ M : ℝ)
    (P : Set (EuclideanSpace ℝ (Fin 2))) (hv : Valid d K target Q ρ M P) (hr : Retained d)
    (θ φ : ℝ) (a : Maxwell.Space) :
    let base := Packet06RigidInitial.initial d K target Q ρ M P hv hr
    let final := transform θ φ a base
    let ps := full θ φ a (Packet06RigidPencilState.initial d.material d.supportRadius
      (Packet06ModalRetainedHost.supportRadius_nonneg d) hv.material_support)
    Packet06GenericObservedPole.SimpleObservedPole final.material final.supportRadius
      (Packet06RigidStateSector.embedding ps d.dilation d.dilation_pos d.translation)
      (Packet06RigidStateSector.pencil ps d.dilation d.dilation_pos d.translation) d.frequency d.baseUnknown := by
  let base := Packet06RigidInitial.initial d K target Q ρ M P hv hr
  have hs := Packet06RigidStateSync.full_sync θ φ a base
  have hsym := Packet06RoundedPlacedPole.rounded_symmetries d.n d.hn d.geometry d.η d.hη.le d.index
  have hsource := Packet05RoundedModeSupport.rounded_support d.n d.hn d.geometry d.η d.hη.le d.index
  have hp := full_frame_observed_pole d.baseMaterial hsym.1 hsym.2 1 (by norm_num) hsource
    d.dilation d.dilation_pos d.translation d.baseFrequency d.baseUnknown hr.base_certified θ φ a
  have hm := hs.1
  have hR := hs.2.1
  change (full θ φ a (Packet06RigidPencilState.initial d.material d.supportRadius
    (Packet06ModalRetainedHost.supportRadius_nonneg d) hv.material_support)).material =
      (transform θ φ a base).material at hm
  change (full θ φ a (Packet06RigidPencilState.initial d.material d.supportRadius
    (Packet06ModalRetainedHost.supportRadius_nonneg d) hv.material_support)).radius =
      (transform θ φ a base).supportRadius at hR
  change Packet06GenericObservedPole.SimpleObservedPole
    (full θ φ a (Packet06RigidPencilState.initial d.material d.supportRadius
      (Packet06ModalRetainedHost.supportRadius_nonneg d) hv.material_support)).material
    (full θ φ a (Packet06RigidPencilState.initial d.material d.supportRadius
      (Packet06ModalRetainedHost.supportRadius_nonneg d) hv.material_support)).radius _ _ d.frequency d.baseUnknown at hp
  dsimp only at hp ⊢
  rw [hm,hR] at hp
  exact hp

end OQ14.Packet06AffineModalPole
#print axioms OQ14.Packet06AffineModalPole.final_observed_pole
