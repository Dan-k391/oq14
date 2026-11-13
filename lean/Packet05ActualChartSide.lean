import Packet05ChartBinaryMatch

/-! The oriented actual graph side becomes the positive flat half-space
under the reflected/swap coordinates followed by the graph shear. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ActualChartSide
open Set OQ14.Maxwell OQ14.ConicalJunctionPhysical OQ14.Packet07BoundaryCoordinates
  OQ14.Packet05ChartOrientation OQ14.Packet05ChartBasis OQ14.Packet05GraphChartMap
  OQ14.Packet05GraphChartHomeomorph OQ14.Packet05PhysicalGraphChart
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_chart_side (B : Set Maxwell.Space) (up : Bool) (i : Fin 3)
    (g G : Plane → ℝ) (W : Set Maxwell.Space)
    (hG : ∀ x ∈ W, G (horizontal x) = orientedGraph up g (horizontal x))
    (hside : ∀ x ∈ W,
      let y := inverseOriented up i (graphMap (liftedHeight G) x)
      y ∈ B ↔ (if up then g (chart i y).1 < (chart i y).2 else (chart i y).2 < g (chart i y).1)) :
    ∀ x ∈ W, inverseOriented up i (graphMap (liftedHeight G) x) ∈ B ↔ 0 < x 2 := by
  intro x hx
  let y := inverseOriented up i (graphMap (liftedHeight G) x)
  have horient := chart_orientation up g i y
  have hy : reflectNormal up (swap i y) = graphMap (liftedHeight G) x := inverse_oriented_right up i _
  have hh : horizontal (graphMap (liftedHeight G) x) = horizontal x := by
    exact horizontal_normal_invariant x (liftedHeight G x)
  have hheight := graph_map_height (liftedHeight G) (liftedHeight_normal_invariant G) x
  have hgx := hG x hx
  have hs := hside x hx
  change y ∈ B ↔ (if up then g (chart i y).1 < (chart i y).2 else (chart i y).2 < g (chart i y).1) at hs
  change y ∈ B ↔ 0 < x 2
  rw [hs,horient,hy,hh,← hgx]
  have hhG : liftedHeight G (graphMap (liftedHeight G) x) = G (horizontal x) := by
    simp only [liftedHeight,hh]
  rw [hhG] at hheight
  constructor <;> intro h <;> linarith

end OQ14.Packet05ActualChartSide
#print axioms OQ14.Packet05ActualChartSide.actual_chart_side
