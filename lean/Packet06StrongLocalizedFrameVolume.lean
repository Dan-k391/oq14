import Packet06StrongPlacedState
import Packet06NeighborhoodWeightedFrame
import Packet06StrongDirectionalLimit
import Packet06WeightedMaximumDivergence

/-! Strong larger-ball provenance and the exact selected weighted maxima
survive the full frame and directional-volume extraction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet06StrongLocalizedFrameVolume
open Filter Metric Set Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06ConcreteModalGeometry Packet06ConcreteModalRounding Packet06PlacedKernel Packet06PlacementHomeomorph
  Packet06PlacedPhaseField Packet06PlacedRoundedVolumeLimits Packet06RoundedVolumeLimits Packet06PhaseWeightedMaximum
  Packet06StrongRoundedMaximum Packet06StrongPlacedWeighted Packet06NeighborhoodWeighted Packet06NeighborhoodWeightedFrame
  Packet06PhysicalVolumeLimits
open scoped Topology
abbrev Space := Maxwell.Space

theorem localized_strong_family_frame {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (r : ℝ) (hrg : r < g.radius)
    (md : ℕ → Fin N → MaximumData) (b : ℕ → Fin N → Bool) (x : ℕ → Fin N → Space)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (a : Space) (J : ℕ) (B : ℕ → ℝ)
    (q : ∀ j, Packet06RigidHotspotState.State N (((s (j+J)) : ℂ)*z (j+J)) (r/s (j+J)) 0 (B j))
    (hmat : ∀ j, (q j).material = placedCoefficient (s (j+J)) a (rounded n hn g η hη (j+J)))
    (hunk : ∀ j, (q j).unknown = placedUnknown (s (j+J)) a (v (j+J)))
    (hbody : ∀ j, (q j).body = placement (s (j+J)) (hs (j+J)) a '' body g (j+J))
    (hcenter : ∀ j i, (q j).center i = placement (s (j+J)) (hs (j+J)) a (g.center i))
    (hrad : ∀ j, (q j).supportRadius = 1/s (j+J)+‖a‖)
    (hcert : ∀ j i, StrongPlaced n hn g η hη (j+J) (z (j+J)) (v (j+J)) i r
      (md (j+J) i) (b (j+J) i) (x (j+J) i) (s (j+J)) (hs (j+J)) a)
    (hmax : ∀ᶠ j in atTop, ∀ i, StrongValid n hn g η hη (z j) (v j) j i r (md j i) ∧
      ∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
        weighted n η (md j i) b' y ≤ weighted n η (md j i) (b j i) (x j i))
    (hdiv : ∀ i, Tendsto (fun j => amplitude (placedVector (md j i) (s j) (hs j) a)) atTop atTop)
    (θ φ : ℝ) (t : Space) (i : Fin N) :
    let K := fun j => closedBall (placement (s (j+J)) (hs (j+J)) a (g.center i)) (g.radius/s (j+J))
    let inside := fun j => branches θ φ t (transport (s (j+J)) (hs (j+J)) a (md (j+J) i).inside)
    let outside := fun j => branches θ φ t (transport (s (j+J)) (hs (j+J)) a (md (j+J) i).outside)
    let side := fun j => b (j+J) i
    let point := fun j => Packet07DrivenRigidHotspot.placement θ φ t (placement (s (j+J)) (hs (j+J)) a (x (j+J) i))
    let W := fun j => scale (s (j+J))^2 * weighted n η (md (j+J) i) (b (j+J) i) (x (j+J) i)
    (∀ j, Certificate (Packet06RigidHotspotFrame.transform θ φ t (q j)) i (sets θ φ t (K j)) n η
      (inside j) (outside j) (side j) (point j)) ∧
    (∀ j, W j = phasePermittivity n η (side j) *
      (physicalAmplitude (phaseField (inside j) (outside j) (side j)) (point j))^2) ∧
    Tendsto (fun j => (W j)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun j => amplitude (fun k => phaseField (inside j) (outside j) (side j) k (point j))) atTop atTop ∧
    ∃ (k : Fin 3) (ψ : ℕ → ℕ), StrictMono ψ ∧
      (∀ᶠ j in atTop, phaseField (inside (ψ j)) (outside (ψ j)) (side (ψ j)) k (point (ψ j)) ≠ 0) ∧
      Tendsto (fun j => (((phasePermittivity n η (side (ψ j)) : ℝ) : ℂ)*
        (phaseField (inside (ψ j)) (outside (ψ j)) (side (ψ j)) k (point (ψ j)))^2)⁻¹) atTop (𝓝 0) := by
  dsimp only
  let W : ℕ → ℝ := fun j => scale (s (j+J))^2 * weighted n η (md (j+J) i) (b (j+J) i) (x (j+J) i)
  have hW : Tendsto W atTop atTop := by
    apply (Packet06WeightedMaximumDivergence.weighted_diverges n hn g η hη z v r md b x s hs a i
      (hmax.mono (fun j hj => ⟨(hj i).1.1,(hj i).2⟩)) (hdiv i)).comp
    exact tendsto_add_atTop_nat J
  have hframe (j : ℕ) := Packet06NeighborhoodWeightedFrame.frame θ φ t (q j) i
    (closedBall (placement (s (j+J)) (hs (j+J)) a (g.center i)) (g.radius/s (j+J))) n η
    (transport (s (j+J)) (hs (j+J)) a (md (j+J) i).inside)
    (transport (s (j+J)) (hs (j+J)) a (md (j+J) i).outside) (b (j+J) i)
    (placement (s (j+J)) (hs (j+J)) a (x (j+J) i))
    (Packet06StrongPlacedState.certificate n hn g η hη (j+J) (z (j+J)) (v (j+J)) i r hrg
      (md (j+J) i) (b (j+J) i) (x (j+J) i) (s (j+J)) (hs (j+J)) a 0 (B j) (q j)
      (hmat j) (hunk j) (hbody j) (hcenter j i) (hrad j) (hcert j i))
  have hvalue (j : ℕ) := (hcert j i).1.2.2.2.2.2.2
  have hWval (j : ℕ) : W j = phasePermittivity n η (b (j+J) i) *
      (physicalAmplitude (phaseField
        (branches θ φ t (transport (s (j+J)) (hs (j+J)) a (md (j+J) i).inside))
        (branches θ φ t (transport (s (j+J)) (hs (j+J)) a (md (j+J) i).outside)) (b (j+J) i))
        (Packet07DrivenRigidHotspot.placement θ φ t (placement (s (j+J)) (hs (j+J)) a (x (j+J) i))))^2 := by
    exact (hvalue j).symm.trans (hframe j).2.symm
  let E : ℕ → Fin 3 → ℂ := fun j k => phaseField
    (branches θ φ t (transport (s (j+J)) (hs (j+J)) a (md (j+J) i).inside))
    (branches θ φ t (transport (s (j+J)) (hs (j+J)) a (md (j+J) i).outside)) (b (j+J) i) k
    (Packet07DrivenRigidHotspot.placement θ φ t (placement (s (j+J)) (hs (j+J)) a (x (j+J) i)))
  have hw' (j : ℕ) : W j = phasePermittivity n η (b (j+J) i) * (amplitude (E j))^2 := hWval j
  have hd := Packet06StrongDirectionalLimit.from_given_vectors E (fun j => b (j+J) i) n η hn hη W hw' hW
  exact ⟨fun j => (hframe j).1,hWval,tendsto_inv_atTop_zero.comp hW,hd.1,hd.2⟩
end OQ14.Packet06StrongLocalizedFrameVolume
#print axioms OQ14.Packet06StrongLocalizedFrameVolume.localized_strong_family_frame
