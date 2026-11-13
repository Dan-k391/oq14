import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! Attainment for finitely many continuous material-side branches. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05FiniteBranchMaximum
open Set

theorem finite_closed_branches_attain_max
    {X J : Type*} [TopologicalSpace X] [Fintype J]
    (K : Set X) (hK : IsCompact K) (hne : K.Nonempty)
    (D : J → Set X) (hclosed : ∀ j, IsClosed (D j))
    (hcover : K ⊆ ⋃ j, D j)
    (amp : J → X → ℝ)
    (hcont : ∀ j, ContinuousOn (amp j) (K ∩ D j)) :
    ∃ j x, x ∈ K ∩ D j ∧
      ∀ j' y, y ∈ K ∩ D j' → amp j' y ≤ amp j x := by
  let values : J → Set ℝ := fun j => amp j '' (K ∩ D j)
  have hc : IsCompact (⋃ j, values j) := by
    apply isCompact_iUnion
    intro j
    exact (hK.inter_right (hclosed j)).image_of_continuousOn (hcont j)
  have hv : (⋃ j, values j).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    exact ⟨amp j x, mem_iUnion.mpr ⟨j, ⟨x, ⟨hx, hj⟩, rfl⟩⟩⟩
  obtain ⟨m, hm, hmax⟩ := hc.exists_isMaxOn hv continuousOn_id
  obtain ⟨j, x, hx, rfl⟩ := mem_iUnion.mp hm
  refine ⟨j, x, hx, ?_⟩
  intro j' y hy
  exact hmax (mem_iUnion.mpr ⟨j', ⟨y, hy, rfl⟩⟩)

end OQ14.Packet05FiniteBranchMaximum
#print axioms OQ14.Packet05FiniteBranchMaximum.finite_closed_branches_attain_max
