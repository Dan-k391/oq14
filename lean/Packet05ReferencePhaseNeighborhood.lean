import Packet05FixedHomogeneousChart

/-! Every non-interface collar point has a fixed open reference phase. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ReferencePhaseNeighborhood
open Set Maxwell
open scoped Topology

theorem phase_neighborhood (body Ω : Set Space) (hΩ : IsOpen Ω) (x : Space)
    (hx : x ∈ Ω) (hfront : x ∉ frontier body) :
    ∃ (U : Set Space) (inside : Prop), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∀ y ∈ U, y ∈ body ↔ inside := by
  classical
  by_cases hcl : x ∈ closure body
  · have hi : x ∈ interior body := by
      have hh := hcl
      rw [closure_eq_interior_union_frontier] at hh
      exact hh.resolve_right hfront
    refine ⟨Ω ∩ interior body,True,hΩ.inter isOpen_interior,⟨hx,hi⟩,inter_subset_left,?_⟩
    intro y hy
    simp [interior_subset hy.2]
  · refine ⟨Ω ∩ (closure body)ᶜ,False,hΩ.inter isClosed_closure.isOpen_compl,⟨hx,hcl⟩,inter_subset_left,?_⟩
    intro y hy
    have hn : y ∉ body := fun h => hy.2 (subset_closure h)
    simp [hn]

end OQ14.Packet05ReferencePhaseNeighborhood
#print axioms OQ14.Packet05ReferencePhaseNeighborhood.phase_neighborhood
