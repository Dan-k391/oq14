import Packet05BoundarySign
import Packet05ActualGraphExtensionC4
import Packet05ChartOrientationMeasure

/-! Every actual smooth regular boundary admits a compact global oriented C⁴
graph agreeing with its physical material side on a neighborhood. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05ActualOrientedGraph
open Set Filter Metric OQ14.Maxwell OQ14.ConicalJunctionPhysical OQ14.Packet07BoundaryCoordinates
  OQ14.Packet05ChartOrientation OQ14.Packet05ChartOrientationMeasure OQ14.Packet05ChartLinearEquiv
  OQ14.Packet05ActualGraphExtensionC4 OQ14.Packet05BoundarySign
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem chart_oriented_horizontal (up : Bool) (i : Fin 3) (x : Maxwell.Space) :
    horizontal (orientedLinear up i x) = (chart i x).1 := by
  change horizontal (reflectNormal up (swap i x)) = _
  rw [reflect_horizontal]
  rfl

theorem actual_oriented_graph (body : Set Maxwell.Space) (x : Maxwell.Space) (hx : x ∈ frontier body)
    (hcert : ∃ F : Maxwell.Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Maxwell.Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ body ↔ 0 < F y)) :
    ∃ (up : Bool) (i : Fin 3) (G : Plane → ℝ), ContDiff ℝ 4 G ∧ HasCompactSupport G ∧
      (orientedLinear up i x) 2 = G (horizontal (orientedLinear up i x)) ∧
      (∀ᶠ y in 𝓝 x, y ∈ body ↔ G (horizontal (orientedLinear up i y)) < (orientedLinear up i y) 2) := by
  obtain ⟨i,g,V,up,hV,hxV,hg,hside⟩ :=
    Packet07BoundaryC4Oriented.oriented_chart_of_regular_boundary body x hcert
  obtain ⟨r,hr,G0,hG0,hG0c,hG0eq,_⟩ :=
    extend_actual_graph_c4 V hV (chart i x).1 hxV g hg
  let G := orientedGraph up G0
  have hGreg : ContDiff ℝ 4 G := oriented_graph_regular up G0 hG0
  have hGc : HasCompactSupport G := oriented_graph_compact up G0 hG0c
  have hhorizontal : Continuous (fun y : Maxwell.Space => horizontal (orientedLinear up i y)) :=
    horizontalLinear.toContinuousLinearMap.continuous.comp (orientedLinear up i).toContinuousLinearMap.continuous
  have hnear : ∀ᶠ y in 𝓝 x, horizontal (orientedLinear up i y) ∈ ball (chart i x).1 r := by
    apply hhorizontal.continuousAt.tendsto.eventually
    rw [chart_oriented_horizontal]
    exact Metric.ball_mem_nhds _ hr
  have hlocal : ∀ᶠ y in 𝓝 x, y ∈ body ↔ G (horizontal (orientedLinear up i y)) < (orientedLinear up i y) 2 := by
    filter_upwards [hside,hnear] with y hs hy
    have ho := chart_orientation up g i y
    have he : G0 (horizontal (orientedLinear up i y)) = g (horizontal (orientedLinear up i y)) := hG0eq _ hy
    have hGe : G (horizontal (orientedLinear up i y)) = orientedGraph up g (horizontal (orientedLinear up i y)) := by
      cases up <;> simp [G,orientedGraph,he]
    change (chart i y).1 ∈ V ∧ _ at hs
    rw [hs.2,ho]
    change orientedGraph up g (horizontal (orientedLinear up i y)) < (orientedLinear up i y) 2 ↔
      G (horizontal (orientedLinear up i y)) < (orientedLinear up i y) 2
    rw [← hGe]
  let f : Maxwell.Space → ℝ := fun y => (orientedLinear up i y) 2 - G (horizontal (orientedLinear up i y))
  have hf : ContinuousAt f x := by
    exact (((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp
      (orientedLinear up i).toContinuousLinearMap.continuous).sub (hGreg.continuous.comp hhorizontal)).continuousAt
  have hsign : ∀ᶠ y in 𝓝 x, y ∈ body ↔ 0 < f y := by
    filter_upwards [hlocal] with y hy
    simpa [f,sub_pos] using hy
  have hz := frontier_sign_zero body x hx f hf hsign
  refine ⟨up,i,G,hGreg,hGc,?_,hlocal⟩
  dsimp [f] at hz
  linarith

end OQ14.Packet05ActualOrientedGraph
#print axioms OQ14.Packet05ActualOrientedGraph.chart_oriented_horizontal
#print axioms OQ14.Packet05ActualOrientedGraph.actual_oriented_graph
