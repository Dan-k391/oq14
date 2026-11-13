import Packet05GraphSlopeMultiplier
import Packet05GraphNormalWeakDerivative

/-! The normal derivative of a slope-weighted inverse-chart test contains
only the derivative of the test, because graph slopes are constant vertically. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphSlopeTest
open OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap
  OQ14.Packet05GraphNormalWeakDerivative OQ14.Packet05GraphSlope
  OQ14.Packet05GraphSlopeMultiplier
open OQ14.Maxwell (basis dcoord partial_mul)
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def slopeTest (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3) (φ : Test) : Test :=
  smoothProductTest (inverseTest g (hg.of_le (by norm_num)) φ) (slopeC g i) (slopeC_contDiff g hg i)

theorem slopeC_graph_invariant (g : Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (i : Fin 3) (x : Space) : slopeC g i (graphMap (liftedHeight g) x) = slopeC g i x := by
  change (OQ14.Packet05GraphSlope.slope g i (x + liftedHeight g x • basis 2) : ℂ) = _
  rw [slope_normal_invariant g hg]
  rfl

theorem slopeTest_normal (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    (φ : Test) (x : Space) :
    dcoord (slopeTest g hg i φ).function x 2 =
      slopeC g i x * dcoord (inverseTest g (hg.of_le (by norm_num)) φ).function x 2 := by
  unfold slopeTest
  change dcoord (fun y => (inverseTest g (hg.of_le (by norm_num)) φ).function y * slopeC g i y) x 2 = _
  rw [partial_mul ((inverseTest g (hg.of_le (by norm_num)) φ).regular.differentiable (by norm_num) x)
    ((slopeC_contDiff g hg i).differentiable (by norm_num) x), slopeC_normal_derivative g hg i x]
  simp [mul_comm]

end OQ14.Packet05GraphSlopeTest
#print axioms OQ14.Packet05GraphSlopeTest.slopeC_graph_invariant
#print axioms OQ14.Packet05GraphSlopeTest.slopeTest_normal
