import Packet05GraphSlopeTest
import Packet05GraphPullback
import WeakPoynting.DivCurlCompact

/-! Actual tangential weak derivative under a smooth graph shear. The slope
term is an L² multiplier and is derived from the transformed compact tests. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05GraphTangentialWeakDerivative
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphChartMap OQ14.Packet05GraphPullback OQ14.Packet05GraphSmooth
  OQ14.Packet05GraphNormalWeakDerivative OQ14.Packet05GraphTestChain
  OQ14.Packet05GraphSlope OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphSlopeTest
open OQ14.Maxwell (basis dcoord partial_continuous)
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem pullback_tangential_weak_partial (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (u vi vn : L2Scalar) (i : Fin 3) (hvi : HasWeakPartial u vi i)
    (hvn : HasWeakPartial u vn 2) (B : ℝ) (hB : ∀ x, ‖slopeC g i x‖ ≤ B) :
    HasWeakPartial (pullback g hg.continuous u)
      (pullback g hg.continuous vi + slopeMul g hg i B hB (pullback g hg.continuous vn)) i := by
  intro φ
  let hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  let ψ := inverseTest g hg1 φ
  let θ := slopeTest g hg i φ
  have hi := hvi ψ
  have hn := hvn θ
  simp only [valuePair, derivativePair, testPair_integral] at hi hn ⊢
  have hv : (∫ x, (pullback g hg.continuous vi + slopeMul g hg i B hB (pullback g hg.continuous vn)) x * φ.function x) =
      (∫ y, vi y * ψ.function y) + ∫ y, vn y * θ.function y := by
    have h₁ : (∫ x, pullback g hg.continuous vi x * φ.function x) = ∫ y, vi y * ψ.function y := by
      rw [← graph_change_of_variables g hg.continuous (fun y => vi y * ψ.function y)]
      apply integral_congr_ae
      filter_upwards [pullback_ae g hg.continuous vi] with x hx
      rw [hx]
      simp [ψ, inverseTest, graph_map_left_inverse _ (liftedHeight_normal_invariant g)]
    have h₂ : (∫ x, slopeMul g hg i B hB (pullback g hg.continuous vn) x * φ.function x) =
        ∫ y, vn y * θ.function y := by
      rw [← graph_change_of_variables g hg.continuous (fun y => vn y * θ.function y)]
      apply integral_congr_ae
      filter_upwards [slopeMul_ae g hg i B hB (pullback g hg.continuous vn),
        pullback_ae g hg.continuous vn] with x hs hx
      rw [hs,hx]
      simp only [θ, slopeTest, smoothProductTest, inverseTest, Function.comp_apply,
        graph_map_left_inverse _ (liftedHeight_normal_invariant g), slopeC_graph_invariant g hg1]
      ring
    have ia := testPair_integrable φ.function φ.regular.continuous φ.compact (pullback g hg.continuous vi)
    have ib := testPair_integrable φ.function φ.regular.continuous φ.compact
      (slopeMul g hg i B hB (pullback g hg.continuous vn))
    rw [← h₁, ← h₂, ← integral_add ia ib]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (pullback g hg.continuous vi)
      (slopeMul g hg i B hB (pullback g hg.continuous vn))] with x hx
    rw [hx]
    simp only [Pi.add_apply, add_mul]
  have hd : (∫ x, pullback g hg.continuous u x * dcoord φ.function x i) =
      (∫ y, u y * dcoord ψ.function y i) + ∫ y, u y * dcoord θ.function y 2 := by
    have ia := testPair_integrable (fun y => dcoord ψ.function y i)
      (partial_continuous ψ.regular i) (ψ.compact.fderiv_apply ℝ (basis i)) u
    have ib := testPair_integrable (fun y => dcoord θ.function y 2)
      (partial_continuous θ.regular 2) (θ.compact.fderiv_apply ℝ (basis 2)) u
    rw [← integral_add ia ib]
    rw [← graph_change_of_variables g hg.continuous
      (fun y => u y * dcoord ψ.function y i + u y * dcoord θ.function y 2)]
    apply integral_congr_ae
    filter_upwards [pullback_ae g hg.continuous u] with x hx
    rw [hx]
    change _ = u (graphMap (liftedHeight g) x) * dcoord (inverseTest g hg1 φ).function (graphMap (liftedHeight g) x) i +
      u (graphMap (liftedHeight g) x) * dcoord (slopeTest g hg i φ).function (graphMap (liftedHeight g) x) 2
    rw [inverseTest_partial, slopeTest_normal, inverseTest_normal,
      graph_map_left_inverse _ (liftedHeight_normal_invariant g), slopeC_graph_invariant g hg1]
    change _ = u _ * (dcoord φ.function x i - slopeC g i (graphMap (liftedHeight g) x) * dcoord φ.function x 2) +
      u _ * (slopeC g i x * dcoord φ.function x 2)
    rw [slopeC_graph_invariant g hg1]
    ring
  rw [hv, hd]
  linear_combination hi + hn

end OQ14.Packet05GraphTangentialWeakDerivative
#print axioms OQ14.Packet05GraphTangentialWeakDerivative.pullback_tangential_weak_partial
