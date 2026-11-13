import Packet07PhysicalLobes

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07LobesEventually
open Filter Set
abbrev Data := ConicalStaticVolume.Data
abbrev Space := Maxwell.Space

theorem eventually_lobes_path_connected {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → Data) (a : ι → ℝ) (center : ι → Space) (ha : ∀ i, 0 < a i) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ι, ∀ up : Bool,
      IsPathConnected (Packet07LobeGeometry.lobe p a center n i up) := by
  let m : ι → ℝ := fun i => ConicalJunctionPhysical.slope (p i).threshold
  have h1 := Packet07VerticalAccess.eventually_vertical_bounds m a ha
  have h2 := Packet07CorridorEventually.eventually_corridor_bounds m a ha
  filter_upwards [h1,h2] with n hn1 hn2 i up
  have hm : 0 < m i := (ConicalJunctionPhysical.slope_properties (p i).threshold
    (p i).threshold_pos (p i).threshold_lt_one).1
  have hp := Packet07PhysicalLobes.physical_lobe_path_connected n (m i) (a i) (center i) up
    hm (ha i) (hn1 i).1 (hn1 i).2.1 (hn1 i).2.2 (hn2 i).1 (hn2 i).2.1
  simpa only [Packet07LobeGeometry.lobe, CommonBinaryInterface.component, Set.setOf_and,
    Set.mem_setOf_eq, m] using hp

end OQ14.Packet07LobesEventually
#print axioms OQ14.Packet07LobesEventually.eventually_lobes_path_connected
