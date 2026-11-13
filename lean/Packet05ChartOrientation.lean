import Packet07BoundaryC4Oriented
import Packet05RegionalBootstrappedScalar

/-! A single orthogonal normal reflection converts either actual graph-side
orientation into the upper-half-space convention used by scalar estimates. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace OQ14.Packet05ChartOrientation
open OQ14.Maxwell OQ14.ConicalJunctionPhysical OQ14.Packet07BoundaryCoordinates
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def reflectNormal (up : Bool) (x : Maxwell.Space) : Maxwell.Space :=
  if up then x else x - (2*x 2) • basis 2

def orientedGraph (up : Bool) (g : Plane → ℝ) : Plane → ℝ :=
  if up then g else -g

theorem reflect_horizontal (up : Bool) (x : Maxwell.Space) : horizontal (reflectNormal up x) = horizontal x := by
  cases up <;> ext i <;> fin_cases i <;>
    simp [reflectNormal,horizontal,basis,EuclideanSpace.single_apply,PiLp.sub_apply,PiLp.smul_apply]

theorem reflect_height (up : Bool) (x : Maxwell.Space) :
    (reflectNormal up x) 2 = if up then x 2 else -x 2 := by
  cases up <;> simp [reflectNormal,basis,EuclideanSpace.single_apply,PiLp.sub_apply,PiLp.smul_apply] <;> ring

theorem chart_orientation (up : Bool) (g : Plane → ℝ) (i : Fin 3) (x : Maxwell.Space) :
    (if up then g (chart i x).1 < (chart i x).2 else (chart i x).2 < g (chart i x).1) ↔
      orientedGraph up g (horizontal (reflectNormal up (swap i x))) < (reflectNormal up (swap i x)) 2 := by
  rw [reflect_horizontal,reflect_height]
  cases up <;> simp [orientedGraph,chart,split,horizontal] <;> linarith

theorem oriented_graph_regular (up : Bool) (g : Plane → ℝ) {n : WithTop ℕ∞}
    (hg : ContDiff ℝ n g) : ContDiff ℝ n (orientedGraph up g) := by
  cases up
  · exact hg.neg
  · exact hg

theorem oriented_graph_compact (up : Bool) (g : Plane → ℝ) (hg : HasCompactSupport g) :
    HasCompactSupport (orientedGraph up g) := by
  cases up <;> simp [orientedGraph,hg,hg.neg']

end OQ14.Packet05ChartOrientation
#print axioms OQ14.Packet05ChartOrientation.reflect_horizontal
#print axioms OQ14.Packet05ChartOrientation.reflect_height
#print axioms OQ14.Packet05ChartOrientation.chart_orientation
#print axioms OQ14.Packet05ChartOrientation.oriented_graph_regular
#print axioms OQ14.Packet05ChartOrientation.oriented_graph_compact
