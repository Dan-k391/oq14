import Packet06StrongRoundedMaximum
import Packet06PlacedWeightedCertificate

/-! A placed weighted maximum retains the very same genuine one-sided
representatives on a larger neighborhood, including small-ball tangencies. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06StrongPlacedWeighted
open MeasureTheory Set Metric Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum Packet06RoundedVolumeLimits Packet06PhaseWeightedMaximum
  Packet06StrongRoundedMaximum Packet06PlacedPhaseField Packet06PlacementHomeomorph Packet06PlacedKernel
  Packet06PlacedWeightedCertificate
abbrev Space := Maxwell.Space

def StrongPlaced {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (j : ℕ) (z : ℂ) (v : Packet06SectorOperator.Sector) (i : Fin N) (r : ℝ) (d : MaximumData)
    (b : Bool) (x : Space) (s : ℝ) (hs : 0 < s) (a : Space) : Prop :=
  HasPlacedWeightedMaximum n hn g η hη j z v i r d b x s hs a ∧
  let h := placement s hs a
  let K := closedBall (g.center i) g.radius
  let E := Packet06ComplexElectric.electric ((s : ℂ)*z)
    (StaticCoefficient.sqrtMultiplier (placedCoefficient s a (rounded n hn g η hη j)) (placedUnknown s a v))
    (DynamicVolume.source (placedCoefficient s a (rounded n hn g η hη j)) (placedUnknown s a v))
  (∀ k, ContinuousOn (transport s hs a d.inside k) (h '' K ∩ closure (h '' body g j))) ∧
  (∀ k, ContinuousOn (transport s hs a d.outside k) (h '' K ∩ closure (closure (h '' body g j))ᶜ)) ∧
  (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ h '' body g j)] transport s hs a d.inside k) ∧
  (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ (closure (h '' body g j))ᶜ)] transport s hs a d.outside k)

theorem strong_placed_certificate {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (j : ℕ) (z : ℂ) (v : Packet06SectorOperator.Sector)
    (hu : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 v=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 z v=1)
    (i : Fin N) (r : ℝ) (hrg : r < g.radius) (d : MaximumData)
    (hd : StrongValid n hn g η hη z v j i r d) (b : Bool) (x : Space)
    (hx : x ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b)
    (hmax : ∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
      weighted n η d b' y ≤ weighted n η d b x)
    (s : ℝ) (hs : 0 < s) (a : Space) : StrongPlaced n hn g η hη j z v i r d b x s hs a := by
  have hsmall := actual_certificate n hn g η hη j z v hu hN i r hrg.le d hd.1 b x hx hmax s hs a
  have hK : closedBall (g.center i) g.radius ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall g.radius_outer).trans (g.outer_inside i)
  have hb : IsOpen (body g j) := CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j
  obtain ⟨hi,ho,hiae,hoae⟩ := hd.2
  have ht := Packet06PlacedTraceCollar.placed_trace_collar (rounded n hn g η hη j)
    (Packet05RoundedModeSupport.rounded_support n hn g η hη j)
    (fun y hy => (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη j y hy).ne')
    z v hu hN (body g j) (closedBall (g.center i) g.radius) ∅ hb measurableSet_closedBall hK
    d.inside d.outside hi ho hiae hoae 0 (by intro p y hy; exact False.elim hy.1) s hs a
  exact ⟨hsmall,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1⟩
end OQ14.Packet06StrongPlacedWeighted
#print axioms OQ14.Packet06StrongPlacedWeighted.strong_placed_certificate
