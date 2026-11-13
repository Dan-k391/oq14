import Packet07LobesEventually

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07ComponentPartition
open Set

/-- A disjoint open connected cover is exactly the connected-component partition. -/
theorem component_eq_piece {α ι : Type*} [TopologicalSpace α] [DecidableEq ι]
    (L : ι → Set α) (ho : ∀ i, IsOpen (L i))
    (hc : ∀ i, IsPreconnected (L i))
    (hd : ∀ i j, i ≠ j → Disjoint (L i) (L j))
    (i : ι) (x : α) (hx : x ∈ L i) :
    connectedComponentIn (⋃ j, L j) x = L i := by
  let U : Set α := ⋃ j : {j // j ≠ i}, L j.1
  have hopen : IsOpen U := isOpen_iUnion fun j => ho j.1
  have hdis : Disjoint (L i) U := by
    apply Set.disjoint_left.mpr
    intro y hy hU
    obtain ⟨j,hj⟩ := mem_iUnion.mp hU
    exact (Set.disjoint_left.mp (hd i j.1 (Ne.symm j.2))) hy hj
  have hcover : (⋃ j, L j) ⊆ L i ∪ U := by
    intro y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    by_cases h : j = i
    · subst j; exact Or.inl hj
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j,h⟩,hj⟩)
  have hxall : x ∈ ⋃ j, L j := mem_iUnion.mpr ⟨i,hx⟩
  apply subset_antisymm
  · apply isPreconnected_connectedComponentIn.subset_left_of_subset_union (ho i) hopen hdis
    · exact (connectedComponentIn_subset _ _).trans hcover
    · exact ⟨x, mem_connectedComponentIn hxall, hx⟩
  · exact (hc i).subset_connectedComponentIn hx (subset_iUnion L i)

theorem every_component_unique_piece {α ι : Type*} [TopologicalSpace α] [DecidableEq ι]
    (L : ι → Set α) (ho : ∀ i, IsOpen (L i))
    (hc : ∀ i, IsPreconnected (L i))
    (hd : ∀ i j, i ≠ j → Disjoint (L i) (L j))
    (hne : ∀ i, (L i).Nonempty) (x : α) (hx : x ∈ ⋃ j, L j) :
    ∃! i, connectedComponentIn (⋃ j, L j) x = L i := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  refine ⟨i, component_eq_piece L ho hc hd i x hi, ?_⟩
  intro j hj
  by_contra hji
  have heq : L i = L j := (component_eq_piece L ho hc hd i x hi).symm.trans hj
  obtain ⟨y,hy⟩ := hne i
  exact (Set.disjoint_left.mp (hd i j (Ne.symm hji))) hy (heq ▸ hy)

end OQ14.Packet07ComponentPartition
#print axioms OQ14.Packet07ComponentPartition.component_eq_piece
#print axioms OQ14.Packet07ComponentPartition.every_component_unique_piece
