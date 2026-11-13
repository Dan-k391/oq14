import Packet06FinalAllModalVolumes
import Packet06PlacedTraceCollar
import Packet06RoundedPlacement

/-! The selected phase-weighted maximum is an attained maximum of the
actual placed Maxwell field's continuous one-sided representatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06PlacedWeightedMaximum
open Set Metric MeasureTheory Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum Packet06RoundedVolumeLimits Packet06PhaseWeightedMaximum
  Packet06PlacedPhaseField Packet06PlacementHomeomorph Packet06PlacedKernel
open scoped Topology
abbrev Space := Maxwell.Space

theorem actual_placed_weighted_maximum {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (z : ℂ) (v : Packet06SectorOperator.Sector)
    (hu : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 v=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 z v=1)
    (i : Fin N) (r : ℝ) (hrg : r ≤ g.radius) (d : MaximumData)
    (hd : Valid n hn g η hη z v j i r d) (b : Bool) (x : Space)
    (hx : x ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b)
    (hmax : ∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
      weighted n η d b' y ≤ weighted n η d b x)
    (s : ℝ) (hs : 0 < s) (a : Space) :
    let h := placement s hs a
    let R := transport s hs a d.inside
    let T := transport s hs a d.outside
    let E := Packet06ComplexElectric.electric ((s : ℂ)*z)
      (StaticCoefficient.sqrtMultiplier (placedCoefficient s a (rounded n hn g η hη j)) (placedUnknown s a v))
      (DynamicVolume.source (placedCoefficient s a (rounded n hn g η hη j)) (placedUnknown s a v))
    (∀ k, ContinuousOn (R k) (h '' closedBall (g.center i) r ∩ closure (h '' body g j))) ∧
    (∀ k, ContinuousOn (T k) (h '' closedBall (g.center i) r ∩ closure (closure (h '' body g j))ᶜ)) ∧
    (∀ k, (fun y => E y k) =ᶠ[ae (volume.restrict (h '' closedBall (g.center i) r ∩ h '' body g j))] R k) ∧
    (∀ k, (fun y => E y k) =ᶠ[ae (volume.restrict (h '' closedBall (g.center i) r ∩ (closure (h '' body g j))ᶜ))] T k) ∧
    h x ∈ h '' closedBall (g.center i) r ∩ phaseDomain (h '' body g j) b ∧
    (∀ b' y, y ∈ h '' closedBall (g.center i) r ∩ phaseDomain (h '' body g j) b' →
      phasePermittivity n η b' * (physicalAmplitude (phaseField R T b') y)^2 ≤
        phasePermittivity n η b * (physicalAmplitude (phaseField R T b) (h x))^2) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField R T b) (h x))^2 =
      scale s^2 * weighted n η d b x := by
  dsimp only
  let K := closedBall (g.center i) r
  let h := placement s hs a
  have hK : K ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall (hrg.trans g.radius_outer)).trans (g.outer_inside i)
  have hb : IsOpen (body g j) := CommonBinaryInterface.body_open
    (fun _ => g.datum) (fun _ => g.radius) g.center j
  have htrace := Packet06PlacedTraceCollar.placed_trace_collar (rounded n hn g η hη j)
    (Packet05RoundedModeSupport.rounded_support n hn g η hη j)
    (fun y hy => (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη j y hy).ne')
    z v hu hN (body g j) K K hb (isClosed_closedBall.measurableSet) hK d.inside d.outside
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1
    (physicalAmplitude (phaseField d.inside d.outside d.side) d.point)
    (fun p y hy => hd.2.2.2.2.2 p y hy) s hs a
  refine ⟨htrace.1,htrace.2.1,htrace.2.2.1,htrace.2.2.2.1,?_,?_,?_⟩
  · exact ⟨⟨x,hx.1,rfl⟩,by rw [← image_phase s hs a (body g j) b]; exact ⟨x,hx.2,rfl⟩⟩
  · intro b' y hy
    have hyK : h.symm y ∈ K := by
      rcases hy.1 with ⟨q,hq,rfl⟩
      simpa [h] using hq
    have hyP : h.symm y ∈ phaseDomain (body g j) b' := by
      have hh := hy.2
      rw [← image_phase s hs a (body g j) b', (placement s hs a).image_eq_preimage] at hh
      exact hh
    rw [phase_transport, amplitude_transport, phase_transport, amplitude_transport]
    have ht := mul_le_mul_of_nonneg_left (hmax b' (h.symm y) ⟨hyK,hyP⟩) (sq_nonneg (scale s))
    simpa [weighted, h, mul_pow, mul_comm, mul_left_comm, mul_assoc] using ht
  · rw [phase_transport, amplitude_transport]
    simp [weighted,h,mul_pow,mul_comm,mul_left_comm,mul_assoc]
end OQ14.Packet06PlacedWeightedMaximum
#print axioms OQ14.Packet06PlacedWeightedMaximum.actual_placed_weighted_maximum
