import Packet06AxialTraceCollar
import Packet06PlacedHotspotGeometry

/-! Phase maxima and full half-amplitude components under axial rotations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06AxialHotspotGeometry
open Set Metric Maxwell ModalAxialRotation Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06AxialPhaseField Packet07HotspotComponent

theorem image_phase (θ : ℝ) (body : Set Space) (b : Bool) :
    (rotation θ) '' phaseDomain body b = phaseDomain ((rotation θ) '' body) b := by
  let h := (rotation θ).toHomeomorph
  change h '' phaseDomain body b = phaseDomain (h '' body) b
  cases b <;> simp only [phaseDomain,h.image_closure,h.image_compl]

theorem image_ball (θ : ℝ) (c : Space) (r : ℝ) :
    (rotation θ) '' ball c r = ball (rotation θ c) r := by
  ext y
  change y ∈ (rotation θ).toEquiv '' ball c r ↔ _
  rw [(rotation θ).toEquiv.image_eq_preimage]
  change dist ((rotation θ).symm y) c < r ↔ dist y (rotation θ c) < r
  rw [← (rotation θ).dist_map ((rotation θ).symm y) c, (rotation θ).apply_symm_apply]

theorem image_closedBall (θ : ℝ) (c : Space) (r : ℝ) :
    (rotation θ) '' closedBall c r = closedBall (rotation θ c) r := by
  ext y
  change y ∈ (rotation θ).toEquiv '' closedBall c r ↔ _
  rw [(rotation θ).toEquiv.image_eq_preimage]
  change dist ((rotation θ).symm y) c ≤ r ↔ dist y (rotation θ c) ≤ r
  rw [← (rotation θ).dist_map ((rotation θ).symm y) c, (rotation θ).apply_symm_apply]

theorem phase_superlevel_image (θ : ℝ) (body : Set Space) (inside outside : Fin 3 → Space → ℂ) (t : ℝ) :
    (rotation θ) '' branchSuperlevel (phaseDomain body)
      (fun b => physicalAmplitude (phaseField inside outside b)) t =
    branchSuperlevel (phaseDomain ((rotation θ) '' body))
      (fun b => physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b)) t := by
  let h := (rotation θ).toHomeomorph
  have he := Packet06PlacedHotspotGeometry.image_superlevel h (phaseDomain body)
    (fun b => physicalAmplitude (phaseField inside outside b)) t 1 (by norm_num)
  simp only [one_mul] at he
  change (rotation θ) '' branchSuperlevel (phaseDomain body) (fun b => physicalAmplitude (phaseField inside outside b)) t =
    branchSuperlevel (fun j => (rotation θ) '' phaseDomain body j)
      (fun j y => physicalAmplitude (phaseField inside outside j) (rotation (-θ) y)) t at he
  have hD : (fun j => (rotation θ) '' phaseDomain body j) = phaseDomain ((rotation θ) '' body) := by
    funext j
    exact image_phase θ body j
  have hF : (fun j y => physicalAmplitude (phaseField inside outside j) (rotation (-θ) y)) =
      (fun j => physicalAmplitude (phaseField (transport θ inside) (transport θ outside) j)) := by
    funext j y
    rw [phase_transport,amplitude_transport]
  rw [hD,hF] at he
  exact he

theorem maximum_transport (θ : ℝ) (c : Space) (r : ℝ) (body : Set Space)
    (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hx : x ∈ closedBall c r ∩ phaseDomain body b)
    (hmax : ∀ b' y, y ∈ closedBall c r ∩ phaseDomain body b' →
      physicalAmplitude (phaseField inside outside b') y ≤ physicalAmplitude (phaseField inside outside b) x) :
    rotation θ x ∈ closedBall (rotation θ c) r ∩ phaseDomain ((rotation θ) '' body) b ∧
    ∀ b' y, y ∈ closedBall (rotation θ c) r ∩ phaseDomain ((rotation θ) '' body) b' →
      physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b') y ≤
        physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b) (rotation θ x) := by
  have himg (b' : Bool) : (rotation θ) '' (closedBall c r ∩ phaseDomain body b') =
      closedBall (rotation θ c) r ∩ phaseDomain ((rotation θ) '' body) b' := by
    rw [Set.image_inter (rotation θ).injective,image_closedBall,image_phase]
  constructor
  · rw [← himg]
    exact mem_image_of_mem _ hx
  · intro b' y hy
    rw [← himg] at hy
    obtain ⟨w,hw,rfl⟩ := hy
    simp only [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hmax b' w hw

theorem half_component_transport (θ : ℝ) (c : Space) (r : ℝ) (body : Set Space)
    (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hx : x ∈ branchSuperlevel (phaseDomain body) (fun b' => physicalAmplitude (phaseField inside outside b'))
      (physicalAmplitude (phaseField inside outside b) x/2))
    (hcompact : IsCompact (connectedComponentIn (branchSuperlevel (phaseDomain body)
      (fun b' => physicalAmplitude (phaseField inside outside b')) (physicalAmplitude (phaseField inside outside b) x/2)) x))
    (hinside : connectedComponentIn (branchSuperlevel (phaseDomain body)
      (fun b' => physicalAmplitude (phaseField inside outside b')) (physicalAmplitude (phaseField inside outside b) x/2)) x ⊆ ball c r) :
    let S := branchSuperlevel (phaseDomain ((rotation θ) '' body))
      (fun b' => physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b'))
      (physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b) (rotation θ x)/2)
    rotation θ x ∈ connectedComponentIn S (rotation θ x) ∧
      IsConnected (connectedComponentIn S (rotation θ x)) ∧ IsCompact (connectedComponentIn S (rotation θ x)) ∧
      connectedComponentIn S (rotation θ x) ⊆ ball (rotation θ c) r := by
  let S₀ := branchSuperlevel (phaseDomain body) (fun b' => physicalAmplitude (phaseField inside outside b'))
    (physicalAmplitude (phaseField inside outside b) x/2)
  let h := (rotation θ).toHomeomorph
  have he : (rotation θ) '' S₀ = branchSuperlevel (phaseDomain ((rotation θ) '' body))
      (fun b' => physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b'))
      (physicalAmplitude (phaseField (transport θ inside) (transport θ outside) b) (rotation θ x)/2) := by
    dsimp only [S₀]
    rw [phase_superlevel_image,phase_transport,amplitude_transport]
    rw [show rotation (-θ) (rotation θ x)=x from spatial_inverse θ x]
  dsimp only
  rw [← he]
  have heq : (rotation θ) '' S₀ = h '' S₀ := rfl
  rw [heq]
  change h x ∈ connectedComponentIn (h '' S₀) (h x) ∧
    IsConnected (connectedComponentIn (h '' S₀) (h x)) ∧
    IsCompact (connectedComponentIn (h '' S₀) (h x)) ∧
    connectedComponentIn (h '' S₀) (h x) ⊆ ball (rotation θ c) r
  rw [← h.image_connectedComponentIn hx]
  have hmem : x ∈ connectedComponentIn S₀ x := mem_connectedComponentIn hx
  refine ⟨mem_image_of_mem h hmem,?_,hcompact.image h.continuous,?_⟩
  · exact (show IsConnected (connectedComponentIn S₀ x) from
      ⟨⟨x,hmem⟩,isPreconnected_connectedComponentIn⟩).image h h.continuous.continuousOn
  · rw [← image_ball θ c r]
    exact image_mono hinside

end OQ14.Packet06AxialHotspotGeometry
#print axioms OQ14.Packet06AxialHotspotGeometry.image_phase
#print axioms OQ14.Packet06AxialHotspotGeometry.image_ball
#print axioms OQ14.Packet06AxialHotspotGeometry.image_closedBall
#print axioms OQ14.Packet06AxialHotspotGeometry.phase_superlevel_image
#print axioms OQ14.Packet06AxialHotspotGeometry.maximum_transport
#print axioms OQ14.Packet06AxialHotspotGeometry.half_component_transport
