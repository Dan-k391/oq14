import Packet07BoundaryRotatedNull

/-! Compact regular binary interfaces have zero physical volume. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryNull
open MeasureTheory Filter Set Packet07BoundaryCoordinates
open scoped Topology

theorem regular_boundary_locally_null (B : Set Space) (x : Space)
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ B ↔ 0 < F y)) :
    ∃ W : Set Space, IsOpen W ∧ x ∈ W ∧ volume (frontier B ∩ W) = 0 := by
  obtain ⟨F,i,g,V,W,hi,hV,hxV,hg,hW,hxW,hFs,h0,hD,hlocal⟩ :=
    Packet07BoundaryNormalRefined.chart_of_regular_boundary B x hcert
  have hfront : ∀ y ∈ frontier B ∩ W, F y = 0 :=
    Packet07BoundaryFrontier.frontier_level_local B W F hW hFs.continuousOn (fun y hy => (hlocal y hy).1)
  have hgraph : ∀ y ∈ frontier B ∩ W, (chart i y).2 = g (chart i y).1 := by
    intro y hy
    exact ((hlocal y hy.2).2).mp (hfront y hy)
  have hmeas : MeasurableSet (frontier B ∩ W) := isClosed_frontier.measurableSet.inter hW.measurableSet
  exact ⟨W,hW,hxW,Packet07BoundaryRotatedNull.measurable_chart_graph_null _ hmeas i g hgraph⟩

theorem compact_regular_boundary_null (B : Set Space) (hcompact : IsCompact (frontier B))
    (hcert : ∀ x ∈ frontier B, ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ B ↔ 0 < F y)) : volume (frontier B) = 0 := by
  apply hcompact.measure_zero_of_nhdsWithin
  intro x hx
  obtain ⟨W,hW,hxW,hzero⟩ := regular_boundary_locally_null B x (hcert x hx)
  exact ⟨frontier B ∩ W, inter_mem_nhdsWithin _ (hW.mem_nhds hxW), hzero⟩

/-- The exact boundedness and regular-boundary clauses carried by the
    fixed-frequency physical witness imply zero boundary volume. -/
theorem bounded_regular_body_boundary_null (B : Set Space) (c : Space) (R : ℝ)
    (hbound : B ⊆ Metric.closedBall c R)
    (hcert : ∀ x ∈ frontier B, ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ B ↔ 0 < F y)) : volume (frontier B) = 0 := by
  have hsub : frontier B ⊆ Metric.closedBall c R :=
    frontier_subset_closure.trans (closure_minimal hbound Metric.isClosed_closedBall)
  have hc : IsCompact (frontier B) :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_frontier hsub
  exact compact_regular_boundary_null B hc hcert
end OQ14.Packet07BoundaryNull
#print axioms OQ14.Packet07BoundaryNull.regular_boundary_locally_null
#print axioms OQ14.Packet07BoundaryNull.compact_regular_boundary_null
#print axioms OQ14.Packet07BoundaryNull.bounded_regular_body_boundary_null
