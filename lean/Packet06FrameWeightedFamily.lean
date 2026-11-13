import Packet06WeightedDirectionalFamily

/-! A single actual normalized family retains its exact weighted maxima
and directional volume subsequences on any fixed rigid frame. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06FrameWeightedFamily
open Filter Metric Set Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum Packet06PhaseWeightedMaximum
  Packet06RigidWeightedMaximum Packet06FrameWeightedMaximum Packet06PhysicalVolumeLimits
open scoped Topology
abbrev Space := Maxwell.Space

theorem frame_family_volume {N : ℕ} (z : ℕ → ℂ) (r M B : ℕ → ℝ)
    (d : ∀ j, Packet06RigidHotspotState.State N (z j) (r j) (M j) (B j))
    (θ φ : ℝ) (a : Space) (i : Fin N) (n η : ℝ) (hn : 1 < n) (hη : 0 ≤ η)
    (W : ℕ → ℝ) (hmax : ∀ j, HasValue (d j) i n η (W j)) (hdiv : Tendsto W atTop atTop) :
    ∃ (inside outside : ℕ → Fin 3 → Space → ℂ) (b : ℕ → Bool) (x : ℕ → Space),
      (∀ j, HasWeightedMaximum (Packet06RigidHotspotFrame.transform θ φ a (d j)).material (z j)
        (Packet06RigidHotspotFrame.transform θ φ a (d j)).unknown
        (Packet06RigidHotspotFrame.transform θ φ a (d j)).body
        (closedBall ((Packet06RigidHotspotFrame.transform θ φ a (d j)).center i) (r j))
        n η (inside j) (outside j) (b j) (x j)) ∧
      (∀ j, W j = phasePermittivity n η (b j) *
        (physicalAmplitude (phaseField (inside j) (outside j) (b j)) (x j))^2) ∧
      Tendsto (fun j => (W j)⁻¹) atTop (𝓝 0) ∧
      Tendsto (fun j => amplitude (fun k => phaseField (inside j) (outside j) (b j) k (x j))) atTop atTop ∧
      ∃ (k : Fin 3) (ψ : ℕ → ℕ), StrictMono ψ ∧
        (∀ᶠ j in atTop, phaseField (inside (ψ j)) (outside (ψ j)) (b (ψ j)) k (x (ψ j)) ≠ 0) ∧
        Tendsto (fun j => (((phasePermittivity n η (b (ψ j)) : ℝ) : ℂ)*
          (phaseField (inside (ψ j)) (outside (ψ j)) (b (ψ j)) k (x (ψ j)))^2)⁻¹) atTop (𝓝 0) := by
  let e := fun j => Packet06RigidHotspotFrame.transform θ φ a (d j)
  have hv (j : ℕ) : HasValue (e j) i n η (W j) := full_frame_value θ φ a (d j) i n η (W j) (hmax j)
  obtain ⟨inside,outside,b,x,hmax',hvalue,hamp,hdir⟩ :=
    Packet06WeightedDirectionalFamily.directional_from_weighted z r M B e i n η hn hη W hv hdiv
  exact ⟨inside,outside,b,x,hmax',hvalue,tendsto_inv_atTop_zero.comp hdiv,hamp,hdir⟩
end OQ14.Packet06FrameWeightedFamily
#print axioms OQ14.Packet06FrameWeightedFamily.frame_family_volume
