import Packet05OpenModeChart
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05HomogeneousChartGeometry
open MeasureTheory Metric Set Maxwell Packet05ChartBasis Packet05ChartOrientation
  Packet05ChartLinearEquiv Packet05GraphChartMap Packet05PhysicalGraphChart
  Packet05PhysicalChartBranches Packet05GraphSmooth Packet07BoundaryCoordinates
  ConicalJunctionPhysical
open scoped Topology
abbrev Plane := ConicalSmoothJunction.Plane

/-- An artificial compact graph can be placed strictly below any prescribed point. -/
theorem graph_below (x : Maxwell.Space) :
    ∃ g : Plane → ℝ, ContDiff ℝ 4 g ∧ HasCompactSupport g ∧
      0 < physicalFlatMap true 2 g x 2 := by
  let b : ContDiffBump (horizontal x) := ⟨1,2,by norm_num,by norm_num⟩
  let g : Plane → ℝ := fun y => (x 2 - 1) * b y
  have hb : b (horizontal x) = 1 := b.one_of_mem_closedBall (by simp [b])
  have ho : orientedLinear true 2 x = x := by
    ext j
    fin_cases j <;> simp [orientedLinear,Packet05ChartOrientationMeasure.reflectLinear,
      reflectNormal, swapLinear,swap,Equiv.swap_apply_def]
  refine ⟨g,?_,?_,?_⟩
  · exact contDiff_const.mul (b.contDiff : ContDiff ℝ 4 b)
  · exact b.hasCompactSupport.mul_left
  · simp only [physicalFlatMap,ho,inverseGraphMap,liftedHeight,g,hb,mul_one,
      PiLp.sub_apply,PiLp.smul_apply,basis,EuclideanSpace.single_apply,ite_true,smul_eq_mul]
    linarith

theorem flat_inverse (g : Plane → ℝ) (y : Maxwell.Space) :
    inverseOriented true 2 (graphMap (liftedHeight g) (physicalFlatMap true 2 g y)) = y := by
  change inverseOriented true 2 (graphMap (liftedHeight g)
    (inverseGraphMap (liftedHeight g) (orientedLinear true 2 y))) = y
  rw [graph_map_right_inverse _ (liftedHeight_normal_invariant g)]
  exact inverse_oriented_left true 2 y

theorem flat_forward (g : Plane → ℝ) (y : Maxwell.Space) :
    physicalFlatMap true 2 g (inverseOriented true 2 (graphMap (liftedHeight g) y)) = y := by
  change inverseGraphMap (liftedHeight g)
    (orientedLinear true 2 (inverseOriented true 2 (graphMap (liftedHeight g) y))) = y
  change inverseGraphMap (liftedHeight g)
    (reflectNormal true (swap 2 (inverseOriented true 2 (graphMap (liftedHeight g) y)))) = y
  rw [inverse_oriented_right true 2]
  exact graph_map_left_inverse _ (liftedHeight_normal_invariant g) y

#print axioms OQ14.Packet05HomogeneousChartGeometry.graph_below
#print axioms OQ14.Packet05HomogeneousChartGeometry.flat_inverse
#print axioms OQ14.Packet05HomogeneousChartGeometry.flat_forward
end OQ14.Packet05HomogeneousChartGeometry
