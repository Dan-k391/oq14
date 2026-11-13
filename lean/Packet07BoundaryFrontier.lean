import Packet07BoundaryOrientedActual

/-! Local phase descriptions force the actual interface into the graph. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryFrontier
open Filter Set
open scoped Topology

theorem frontier_level_local (B O : Set Maxwell.Space) (f : Maxwell.Space → ℝ)
    (hO : IsOpen O) (hf : ContinuousOn f O)
    (hB : ∀ y ∈ O, (y ∈ B ↔ 0 < f y)) :
    ∀ y ∈ frontier B ∩ O, f y = 0 := by
  classical
  intro y hy
  have hyO := hy.2
  have hcont : ContinuousAt f y := hf.continuousAt (hO.mem_nhds hyO)
  have hclosures : y ∈ closure B ∧ y ∈ closure Bᶜ := by
    simpa only [frontier_eq_closure_inter_closure, mem_inter_iff] using hy.1
  by_contra hn
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have he : ∀ᶠ z in 𝓝 y, z ∉ B := by
      filter_upwards [hO.mem_nhds hyO, hcont.eventually (Iio_mem_nhds hneg)] with z hz hnegz
      intro hzB
      have := (hB z hz).mp hzB
      linarith
    obtain ⟨z,hz,hzB⟩ := mem_closure_iff_nhds.mp hclosures.1 _ he
    exact hz hzB
  · have he : ∀ᶠ z in 𝓝 y, z ∈ B := by
      filter_upwards [hO.mem_nhds hyO, hcont.eventually (Ioi_mem_nhds hpos)] with z hz hposz
      exact (hB z hz).mpr hposz
    obtain ⟨z,hz,hzB⟩ := mem_closure_iff_nhds.mp hclosures.2 _ he
    exact hzB hz

end OQ14.Packet07BoundaryFrontier
#print axioms OQ14.Packet07BoundaryFrontier.frontier_level_local
