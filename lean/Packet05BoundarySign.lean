import Packet05ActualModePhaseBranches

/-! A local continuous sign chart vanishes at every actual boundary point. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05BoundarySign
open Set Filter
open scoped Topology

theorem frontier_sign_zero (B : Set Maxwell.Space) (x : Maxwell.Space) (hx : x ∈ frontier B)
    (f : Maxwell.Space → ℝ) (hf : ContinuousAt f x)
    (hside : ∀ᶠ y in 𝓝 x, (y ∈ B ↔ 0 < f y)) : f x = 0 := by
  have hfront : x ∈ (interior B)ᶜ ∩ (interior Bᶜ)ᶜ := by
    simpa only [frontier_eq_inter_compl_interior] using hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with hn | hp
  · have hev : ∀ᶠ y in 𝓝 x, y ∈ Bᶜ := by
      filter_upwards [hside,hf.eventually_lt continuousAt_const hn] with y hs hy
      exact fun hb => not_lt_of_ge hy.le (hs.mp hb)
    exact hfront.2 (mem_interior_iff_mem_nhds.mpr hev)
  · have hev : ∀ᶠ y in 𝓝 x, y ∈ B := by
      filter_upwards [hside,continuousAt_const.eventually_lt hf hp] with y hs hy
      exact hs.mpr hy
    exact hfront.1 (mem_interior_iff_mem_nhds.mpr hev)

end OQ14.Packet05BoundarySign
#print axioms OQ14.Packet05BoundarySign.frontier_sign_zero
