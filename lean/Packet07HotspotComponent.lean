import Packet07MeridionalMaximum

/-! A low boundary collar traps the full connected superlevel region of a peak. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07HotspotComponent
open Set Metric Maxwell

theorem connected_set_inside_of_no_sphere (S : Set Space) (hS : IsPreconnected S)
    (c x : Space) (r : ℝ) (hx : x ∈ S) (hxr : x ∈ ball c r)
    (hbarrier : ∀ y ∈ S, dist y c ≠ r) : S ⊆ ball c r := by
  intro y hy
  by_contra hn
  have hyr : r ≤ dist y c := not_lt.mp hn
  have hmem : r ∈ (fun q : Space => dist q c) '' S :=
    hS.intermediate_value hx hy (continuous_id.dist continuous_const).continuousOn
      ⟨hxr.le,hyr⟩
  obtain ⟨q,hq,heq⟩ := hmem
  exact hbarrier q hq heq

theorem closed_component (S : Set Space) (hS : IsClosed S) (x : Space) :
    IsClosed (connectedComponentIn S x) := by
  by_cases hx : x ∈ S
  · rw [connectedComponentIn_eq_image hx]
    exact hS.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

theorem compact_component_inside (S : Set Space) (hS : IsClosed S)
    (c x : Space) (r : ℝ) (hx : x ∈ S) (hxr : x ∈ ball c r)
    (hbarrier : ∀ y ∈ S, dist y c ≠ r) :
    x ∈ connectedComponentIn S x ∧ IsConnected (connectedComponentIn S x) ∧
      IsCompact (connectedComponentIn S x) ∧ connectedComponentIn S x ⊆ ball c r := by
  have hmem := mem_connectedComponentIn hx
  have hinside := connected_set_inside_of_no_sphere (connectedComponentIn S x)
    isPreconnected_connectedComponentIn c x r hmem hxr
    (fun y hy => hbarrier y (connectedComponentIn_subset S x hy))
  refine ⟨hmem,⟨⟨x,hmem⟩,isPreconnected_connectedComponentIn⟩,?_,hinside⟩
  exact (isCompact_closedBall c r).of_isClosed_subset (closed_component S hS x)
    (hinside.trans ball_subset_closedBall)

theorem locally_closed_component_inside (S : Set Space) (c x : Space) (r : ℝ)
    (hclosed : IsClosed (S ∩ closedBall c r)) (hx : x ∈ S) (hxr : x ∈ ball c r)
    (hbarrier : ∀ y ∈ S, dist y c ≠ r) :
    IsCompact (connectedComponentIn S x) ∧ connectedComponentIn S x ⊆ ball c r := by
  have hmem := mem_connectedComponentIn hx
  have hinside := connected_set_inside_of_no_sphere (connectedComponentIn S x)
    isPreconnected_connectedComponentIn c x r hmem hxr
    (fun y hy => hbarrier y (connectedComponentIn_subset S x hy))
  have he : connectedComponentIn S x=connectedComponentIn (S ∩ closedBall c r) x := by
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hmem
        (fun y hy => ⟨connectedComponentIn_subset S x hy,ball_subset_closedBall (hinside hy)⟩)
    · exact connectedComponentIn_mono x inter_subset_left
  refine ⟨?_,hinside⟩
  apply (isCompact_closedBall c r).of_isClosed_subset
  · rw [he]
    exact closed_component _ hclosed x
  · exact hinside.trans ball_subset_closedBall

def branchSuperlevel {J : Type*} (D : J → Set Space) (amp : J → Space → ℝ) (t : ℝ) : Set Space :=
  ⋃ j, D j ∩ {x | t ≤ amp j x}

theorem branch_superlevel_closed {J : Type*} [Finite J]
    (D : J → Set Space) (amp : J → Space → ℝ) (t : ℝ)
    (hD : ∀ j, IsClosed (D j)) (hcont : ∀ j, ContinuousOn (amp j) (D j)) :
    IsClosed (branchSuperlevel D amp t) := by
  apply isClosed_iUnion_of_finite
  intro j
  exact (hD j).isClosed_le continuousOn_const (hcont j)

theorem branch_peak_component {J : Type*} [Finite J]
    (D : J → Set Space) (amp : J → Space → ℝ)
    (hD : ∀ j, IsClosed (D j)) (hcont : ∀ j, ContinuousOn (amp j) (D j))
    (c x : Space) (r t : ℝ) (j : J) (hx : x ∈ D j)
    (hxr : x ∈ ball c r) (hpeak : t ≤ amp j x)
    (hcollar : ∀ k y, y ∈ D k → dist y c=r → amp k y<t) :
    x ∈ connectedComponentIn (branchSuperlevel D amp t) x ∧
      IsConnected (connectedComponentIn (branchSuperlevel D amp t) x) ∧
      IsCompact (connectedComponentIn (branchSuperlevel D amp t) x) ∧
      connectedComponentIn (branchSuperlevel D amp t) x ⊆ ball c r := by
  apply compact_component_inside _ (branch_superlevel_closed D amp t hD hcont) c x r
    (mem_iUnion.mpr ⟨j,hx,hpeak⟩) hxr
  intro y hy he
  obtain ⟨k,hk,hlevel⟩ := mem_iUnion.mp hy
  exact (not_le.mpr (hcollar k y hk he)) hlevel

end OQ14.Packet07HotspotComponent
#print axioms OQ14.Packet07HotspotComponent.connected_set_inside_of_no_sphere
#print axioms OQ14.Packet07HotspotComponent.closed_component
#print axioms OQ14.Packet07HotspotComponent.compact_component_inside
#print axioms OQ14.Packet07HotspotComponent.locally_closed_component_inside
#print axioms OQ14.Packet07HotspotComponent.branch_superlevel_closed
#print axioms OQ14.Packet07HotspotComponent.branch_peak_component
