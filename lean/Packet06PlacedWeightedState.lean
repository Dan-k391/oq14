import Packet06FrameWeightedMaximum
import Packet06PlacedWeightedCertificate

/-! An actual placed rounded-mode weighted maximum is a weighted-value
certificate for the corresponding physical hotspot state. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace OQ14.Packet06PlacedWeightedState
open Set Metric Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06PlacedKernel Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedWeightedCertificate
  Packet06RoundedVolumeLimits Packet06PhaseWeightedMaximum Packet06FrameWeightedMaximum

theorem placed_has_value {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (z : ℂ) (v : Packet06SectorOperator.Sector)
    (i : Fin N) (r : ℝ) (md : MaximumData) (b : Bool) (x : Maxwell.Space)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (M B : ℝ)
    (q : Packet06RigidHotspotState.State N ((s : ℂ)*z) (r/s) M B)
    (hmat : q.material = placedCoefficient s a (rounded n hn g η hη j))
    (hunk : q.unknown = placedUnknown s a v)
    (hbody : q.body = placement s hs a '' body g j)
    (hcenter : q.center i = placement s hs a (g.center i))
    (hc : HasPlacedWeightedMaximum n hn g η hη j z v i r md b x s hs a) :
    HasValue q i n η (scale s^2 * weighted n η md b x) := by
  obtain ⟨hi,ho,hiae,hoae,hx,hmax,hval⟩ := hc
  have he := image_closedBall s hs a (g.center i) r
  rw [he] at hi ho hiae hoae hx hmax
  refine ⟨transport s hs a md.inside,transport s hs a md.outside,b,placement s hs a x,?_,hval.symm⟩
  rw [hmat,hunk,hbody,hcenter]
  exact ⟨hi,ho,hiae,hoae,hx,hmax⟩
end OQ14.Packet06PlacedWeightedState
#print axioms OQ14.Packet06PlacedWeightedState.placed_has_value
