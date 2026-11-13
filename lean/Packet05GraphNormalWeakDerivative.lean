import Packet05GraphSmooth
import WeakPoynting.DivCurlCompact

/-! The actual normal weak L² derivative commutes with a smooth graph shear.
The proof pulls compact tests through the inverse chart and changes variables. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphNormalWeakDerivative
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphChartMap OQ14.Packet05GraphPullback OQ14.Packet05GraphSmooth
open OQ14.Maxwell (basis dcoord)

def inverseTest (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (φ : Test) : Test where
  function := φ.function ∘ inverseGraphMap (liftedHeight g)
  regular := φ.regular.comp (inverseGraphMap_contDiff g hg)
  compact := φ.compact.comp_homeomorph (physicalGraphHomeomorph g hg.continuous).symm

theorem inverseTest_normal (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (φ : Test) (x : Space) :
    dcoord (inverseTest g hg φ).function x 2 =
      dcoord φ.function (inverseGraphMap (liftedHeight g) x) 2 := by
  change fderiv ℝ (φ.function ∘ inverseGraphMap (liftedHeight g)) x (basis 2) = _
  rw [fderiv_comp x (φ.regular.differentiable (by norm_num) _)
    ((inverseGraphMap_contDiff g hg).differentiable (by norm_num) x)]
  simp [inverseGraphMap_normal_derivative g hg x, dcoord]

theorem pullback_normal_weak_partial (g : Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (u v : L2Scalar) (hu : HasWeakPartial u v 2) :
    HasWeakPartial (pullback g hg.continuous u) (pullback g hg.continuous v) 2 := by
  intro φ
  have ht := hu (inverseTest g hg φ)
  simp only [valuePair, derivativePair, testPair_integral] at ht ⊢
  have hv : (∫ x, pullback g hg.continuous v x * φ.function x) =
      ∫ y, v y * (inverseTest g hg φ).function y := by
    rw [← graph_change_of_variables g hg.continuous (fun y => v y * (inverseTest g hg φ).function y)]
    apply integral_congr_ae
    filter_upwards [pullback_ae g hg.continuous v] with x hx
    rw [hx]
    simp [inverseTest, graph_map_left_inverse _ (liftedHeight_normal_invariant g)]
  have hu' : (∫ x, pullback g hg.continuous u x * dcoord φ.function x 2) =
      ∫ y, u y * dcoord (inverseTest g hg φ).function y 2 := by
    rw [← graph_change_of_variables g hg.continuous (fun y => u y * dcoord (inverseTest g hg φ).function y 2)]
    apply integral_congr_ae
    filter_upwards [pullback_ae g hg.continuous u] with x hx
    rw [hx, inverseTest_normal, graph_map_left_inverse _ (liftedHeight_normal_invariant g)]
  rw [hv, hu']
  exact ht

end OQ14.Packet05GraphNormalWeakDerivative
#print axioms OQ14.Packet05GraphNormalWeakDerivative.inverseTest_normal
#print axioms OQ14.Packet05GraphNormalWeakDerivative.pullback_normal_weak_partial
