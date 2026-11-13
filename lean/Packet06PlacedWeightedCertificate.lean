import Packet06PlacedWeightedMaximum

/-! Reusable actual placed phase-weighted maximum certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06PlacedWeightedCertificate
open Set Metric MeasureTheory Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum Packet06RoundedVolumeLimits Packet06PhaseWeightedMaximum
  Packet06PlacedPhaseField Packet06PlacementHomeomorph Packet06PlacedKernel
open scoped Topology
abbrev Space := Maxwell.Space

def HasPlacedWeightedMaximum {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (z : ℂ) (v : Packet06SectorOperator.Sector)
    (i : Fin N) (r : ℝ) (d : MaximumData) (b : Bool) (x : Space)
    (s : ℝ) (hs : 0 < s) (a : Space) : Prop :=
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
      scale s^2 * weighted n η d b x

theorem actual_certificate {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (z : ℂ) (v : Packet06SectorOperator.Sector)
    (hu : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 v=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 z v=1)
    (i : Fin N) (r : ℝ) (hrg : r ≤ g.radius) (d : MaximumData)
    (hd : Valid n hn g η hη z v j i r d) (b : Bool) (x : Space)
    (hx : x ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b)
    (hmax : ∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
      weighted n η d b' y ≤ weighted n η d b x)
    (s : ℝ) (hs : 0 < s) (a : Space) :
    HasPlacedWeightedMaximum n hn g η hη j z v i r d b x s hs a :=
  Packet06PlacedWeightedMaximum.actual_placed_weighted_maximum n hn g η hη j z v hu hN i r hrg d hd b x hx hmax s hs a
end OQ14.Packet06PlacedWeightedCertificate
#print axioms OQ14.Packet06PlacedWeightedCertificate.actual_certificate
