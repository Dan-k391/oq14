import Packet05GraphCompactExtension

/-! Smooth compact graph extensions have globally bounded directional
coefficient derivatives on the chart plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05CompactGraphBounds
open Set OQ14.ConicalSmoothJunction
open scoped Topology

theorem compact_continuous_norm_bound (f : Plane → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B := by
  have hcomp : IsCompact (f '' tsupport f) := hc.isCompact.image hf
  obtain ⟨B,hB⟩ := hcomp.isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport f
  · exact (hB (f x) ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  · have hz : f x = 0 := image_eq_zero_of_nmem_tsupport hx
    simp [hz, le_max_right]

theorem compact_graph_derivative_bound (g : Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (v : Plane) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖fderiv ℝ g x v‖ ≤ B := by
  have hgc : ContDiff ℝ 1 g := hg
  have hd : Continuous (fun x => fderiv ℝ g x v) :=
    (hgc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact compact_continuous_norm_bound _ hd (hc.fderiv_apply ℝ v)

theorem compact_graph_second_derivative_bound (g : Plane → ℝ) (hg : ContDiff ℝ 3 g)
    (hc : HasCompactSupport g) (v w : Plane) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖fderiv ℝ (fun y => fderiv ℝ g y v) x w‖ ≤ B := by
  have hd : ContDiff ℝ 2 (fun x => fderiv ℝ g x v) :=
    (hg.contDiff_fderiv_apply (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  have hc' := hc.fderiv_apply ℝ v
  exact compact_graph_derivative_bound _ (hd.of_le (by decide)) hc' w

end OQ14.Packet05CompactGraphBounds
#print axioms OQ14.Packet05CompactGraphBounds.compact_continuous_norm_bound
#print axioms OQ14.Packet05CompactGraphBounds.compact_graph_derivative_bound
#print axioms OQ14.Packet05CompactGraphBounds.compact_graph_second_derivative_bound
