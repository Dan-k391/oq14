import Packet07AffinePower

/-! Basic finite-body geometry under invertible affine placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07AffineGeometry
open Set Metric
abbrev Space := Maxwell.Space

def map (s : ℝ) (a : Space) (x : Space) : Space := s • (x-a)
def place (s : ℝ) (a : Space) (x : Space) : Space := s⁻¹ • x + a

theorem map_place (s : ℝ) (hs : s ≠ 0) (a x : Space) : map s a (place s a x) = x := by
  simp [map, place, smul_smul, hs]

theorem map_continuous (s : ℝ) (a : Space) : Continuous (map s a) :=
  continuous_const.smul (continuous_id.sub continuous_const)

theorem preimage_open (s : ℝ) (a : Space) (S : Set Space) (hS : IsOpen S) :
    IsOpen (map s a ⁻¹' S) := hS.preimage (map_continuous s a)

theorem preimage_nonempty (s : ℝ) (hs : s ≠ 0) (a : Space) (S : Set Space) (hS : S.Nonempty) :
    (map s a ⁻¹' S).Nonempty := by
  obtain ⟨x,hx⟩ := hS
  exact ⟨place s a x, by simpa only [mem_preimage, map_place s hs] using hx⟩

theorem preimage_disjoint (s : ℝ) (a : Space) (S T : Set Space) (h : Disjoint S T) :
    Disjoint (map s a ⁻¹' S) (map s a ⁻¹' T) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (Set.disjoint_left.mp h) hx hy

theorem placed_center (s : ℝ) (a : Packet07PlanarCenters.Plane) (v : Packet07PlanarCenters.Plane) :
    Packet07PlanarCenters.planeEmbed (a + s⁻¹ • v) = place s (Packet07PlanarCenters.planeEmbed a)
      (Packet07PlanarCenters.planeEmbed v) := by
  ext i
  fin_cases i <;> simp [Packet07PlanarCenters.planeEmbed, place, PiLp.add_apply, PiLp.smul_apply, add_comm]

/-- An enclosed device remains inside an explicit finite translated ball after dilation. -/
theorem preimage_enclosed (s : ℝ) (hs : 0 < s) (a : Space) (S : Set Space) (R : ℝ)
    (hS : S ⊆ closedBall (0 : Space) R) :
    map s a ⁻¹' S ⊆ closedBall a (R/s) := by
  intro x hx
  have h := hS hx
  simp only [mem_closedBall, dist_zero_right, map, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at h
  simp only [mem_closedBall, dist_eq_norm]
  exact (le_div_iff₀ hs).mpr (by nlinarith)

/-- A physical open ball pulls back to the correctly scaled and translated ball. -/
theorem preimage_ball (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ) :
    map s a ⁻¹' ball c r = ball (place s a c) (r/s) := by
  ext x
  simp only [mem_preimage, mem_ball, map, place, dist_eq_norm]
  have hd : s • (x-a) - c = s • (x-(s⁻¹ • c+a)) := by
    simp [smul_sub, smul_add, smul_smul, hs.ne']
    module
  rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  constructor
  · intro h
    exact (lt_div_iff₀ hs).mpr (by nlinarith)
  · intro h
    have hh := (lt_div_iff₀ hs).mp h
    nlinarith

end OQ14.Packet07AffineGeometry
#print axioms OQ14.Packet07AffineGeometry.map_place
#print axioms OQ14.Packet07AffineGeometry.map_continuous
#print axioms OQ14.Packet07AffineGeometry.preimage_open
#print axioms OQ14.Packet07AffineGeometry.preimage_nonempty
#print axioms OQ14.Packet07AffineGeometry.preimage_disjoint
#print axioms OQ14.Packet07AffineGeometry.placed_center

#print axioms OQ14.Packet07AffineGeometry.preimage_enclosed

#print axioms OQ14.Packet07AffineGeometry.preimage_ball
