import Packet06StrongPlacedWeighted
import Packet06LargeTraceBallHost
import Packet06NeighborhoodWeighted

/-! The actual placed larger-ball representatives provide the strengthened
weighted certificate consumed by the full rigid frame. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06StrongPlacedState
open MeasureTheory Set Metric Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06PlacedKernel Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedWeightedCertificate
  Packet06RoundedVolumeLimits Packet06PhaseWeightedMaximum Packet06StrongPlacedWeighted
  Packet06NeighborhoodWeighted
abbrev Space := Maxwell.Space

theorem certificate {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (z : ℂ) (v : Packet06SectorOperator.Sector)
    (i : Fin N) (r : ℝ) (hrg : r < g.radius) (md : MaximumData) (b : Bool) (x : Space)
    (s : ℝ) (hs : 0 < s) (a : Space) (M B : ℝ)
    (q : Packet06RigidHotspotState.State N ((s : ℂ)*z) (r/s) M B)
    (hmat : q.material = placedCoefficient s a (rounded n hn g η hη j))
    (hunk : q.unknown = placedUnknown s a v)
    (hbody : q.body = placement s hs a '' body g j)
    (hcenter : q.center i = placement s hs a (g.center i))
    (hrad : q.supportRadius = 1/s+‖a‖)
    (hc : StrongPlaced n hn g η hη j z v i r md b x s hs a) :
    Certificate q i (closedBall (placement s hs a (g.center i)) (g.radius/s)) n η
      (transport s hs a md.inside) (transport s hs a md.outside) b (placement s hs a x) := by
  obtain ⟨hsmall,hi,ho,hiae,hoae⟩ := hc
  obtain ⟨hsi,hso,hsae,hsbe,hx,hmax,hval⟩ := hsmall
  have he := image_closedBall s hs a (g.center i) g.radius
  rw [he] at hi ho hiae hoae
  have hsball := image_closedBall s hs a (g.center i) r
  rw [hsball] at hsi hso hsae hsbe hx hmax
  have hhost := Packet06LargeTraceBallHost.placed_large_ball n hn g η hη j i s hs a
  refine ⟨measurableSet_closedBall,?_,?_,?_,?_,?_⟩
  · simpa only [hrad] using hhost.1
  · intro y hy
    rw [hmat]
    exact hhost.2 y hy
  · rw [hcenter]
    exact closedBall_subset_closedBall (div_le_div_of_nonneg_right hrg.le hs.le)
  · rw [hmat,hunk,hbody]
    exact ⟨hi,ho,hiae,hoae⟩
  · rw [hmat,hunk,hbody,hcenter]
    exact ⟨hsi,hso,hsae,hsbe,hx,hmax⟩
end OQ14.Packet06StrongPlacedState
#print axioms OQ14.Packet06StrongPlacedState.certificate
