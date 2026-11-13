import Packet07BoundaryCoordinates

/-! Every actual regular level has a local Cartesian graph chart. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryChart
open Filter Set Packet07BoundaryCoordinates
open scoped Topology

theorem regular_level_cartesian_graph (F : Space → ℝ) (x : Space)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F x) (hzero : F x = 0)
    (hD : fderiv ℝ F x ≠ 0) :
    ∃ (i : Fin 3) (g : Plane → ℝ), ContinuousAt g (chart i x).1 ∧
      (∀ᶠ y in 𝓝 x, F y = 0 ↔ (chart i y).2 = g (chart i y).1) := by
  obtain ⟨i,hi⟩ := Packet07BoundaryNormal.nonzero_coordinate (fderiv ℝ F x) hD
  let q := chart i x
  let H : Point → ℝ := fun p => F (unchart i p)
  have hq : unchart i q = x := unchart_chart i x
  have hc : ContinuousAt (unchart i) q := (unchartCLM i).continuous.continuousAt
  have hH : ContDiffAt ℝ (⊤ : ℕ∞) H q := by
    change ContDiffAt ℝ (⊤ : ℕ∞) (F ∘ unchart i) q
    apply ContDiffAt.comp q
    · simpa [hq] using hF
    · exact (unchartCLM i).contDiff.contDiffAt
  have hd : fderiv ℝ H q = (fderiv ℝ F x).comp (unchartCLM i) := by
    have hf' : HasFDerivAt F (fderiv ℝ F x) (unchart i q) := by
      rw [hq]
      exact (hF.differentiableAt (by simp)).hasFDerivAt
    have hh := hf'.comp q ((unchartCLM i).hasFDerivAt)
    change HasFDerivAt H ((fderiv ℝ F x).comp (unchartCLM i)) q at hh
    exact hh.fderiv
  have hv : fderiv ℝ H q (0,1) ≠ 0 := by
    rw [hd]
    change fderiv ℝ F x (unchart i (0,1)) ≠ 0
    rwa [unchart_vertical]
  obtain ⟨g,hg,hgraph⟩ := Packet07BoundaryGraph.regular_level_graph H q hH (by simpa [H,hq] using hzero) hv
  have hchart : ContinuousAt (chart i) x :=
    ConicalJunctionPhysical.split_continuous.continuousAt.comp (swapCLM i).continuous.continuousAt
  refine ⟨i,g,hg,?_⟩
  have hh := hchart.tendsto.eventually hgraph
  filter_upwards [hh] with y hy
  simpa only [H, unchart_chart] using hy

end OQ14.Packet07BoundaryChart
#print axioms OQ14.Packet07BoundaryChart.regular_level_cartesian_graph
