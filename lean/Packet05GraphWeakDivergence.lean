import Packet05GraphTangentialWeakDerivative

/-! Piola transformation of actual weak L² divergence through a graph shear. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05GraphWeakDivergence
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphChartMap OQ14.Packet05GraphPullback
  OQ14.Packet05GraphNormalWeakDerivative OQ14.Packet05GraphTestChain
  OQ14.Packet05GraphSlope OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphSlopeTest
open OQ14.Maxwell (basis dcoord partial_continuous)
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem inverseTest_derivative_pair (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (φ : Test) (u : L2Scalar) (i : Fin 3) (B : ℝ)
    (hB : ∀ x, ‖slopeC g i x‖ ≤ B) :
    derivativePair (inverseTest g (hg.of_le (by norm_num)) φ) i u =
      derivativePair φ i (pullback g hg.continuous u) -
        derivativePair φ 2 (slopeMul g hg i B hB (pullback g hg.continuous u)) := by
  let hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  simp only [derivativePair, testPair_integral]
  have ia := testPair_integrable (fun x => dcoord φ.function x i)
    (partial_continuous φ.regular i) (φ.compact.fderiv_apply ℝ (basis i)) (pullback g hg.continuous u)
  have ib := testPair_integrable (fun x => dcoord φ.function x 2)
    (partial_continuous φ.regular 2) (φ.compact.fderiv_apply ℝ (basis 2))
    (slopeMul g hg i B hB (pullback g hg.continuous u))
  rw [← integral_sub ia ib]
  rw [← graph_change_of_variables g hg.continuous
    (fun y => u y * dcoord (inverseTest g hg1 φ).function y i)]
  apply integral_congr_ae
  filter_upwards [pullback_ae g hg.continuous u,
    slopeMul_ae g hg i B hB (pullback g hg.continuous u)] with x hu hs
  rw [hs, hu, inverseTest_partial, graph_map_left_inverse _ (liftedHeight_normal_invariant g)]
  change u _ * (dcoord φ.function x i - slopeC g i (graphMap (liftedHeight g) x) * dcoord φ.function x 2) = _
  rw [slopeC_graph_invariant g hg1]
  ring

theorem inverseTest_value_pair (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (φ : Test) (u : L2Scalar) :
    valuePair (inverseTest g (hg.of_le (by norm_num)) φ) u =
      valuePair φ (pullback g hg.continuous u) := by
  simp only [valuePair, testPair_integral]
  rw [← graph_change_of_variables g hg.continuous
    (fun y => u y * (inverseTest g (hg.of_le (by norm_num)) φ).function y)]
  apply integral_congr_ae
  filter_upwards [pullback_ae g hg.continuous u] with x hx
  rw [hx]
  simp [inverseTest, graph_map_left_inverse _ (liftedHeight_normal_invariant g)]

def transformedFlux (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (P : L2Vector)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) : L2Vector := fun j =>
  if j = 2 then pullback g hg.continuous (P 2) -
    slopeMul g hg 0 (B 0) (hB 0) (pullback g hg.continuous (P 0)) -
    slopeMul g hg 1 (B 1) (hB 1) (pullback g hg.continuous (P 1)) -
    slopeMul g hg 2 (B 2) (hB 2) (pullback g hg.continuous (P 2))
  else pullback g hg.continuous (P j)

theorem graph_pullback_weak_divergence (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (P : L2Vector) (D : L2Scalar) (hdiv : HasWeakDivergence P D)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) :
    HasWeakDivergence (transformedFlux g hg P B hB) (pullback g hg.continuous D) := by
  intro φ
  have ht := hdiv (inverseTest g (hg.of_le (by norm_num)) φ)
  rw [inverseTest_value_pair g hg φ D] at ht
  rw [inverseTest_derivative_pair g hg φ (P 0) 0 (B 0) (hB 0),
    inverseTest_derivative_pair g hg φ (P 1) 1 (B 1) (hB 1),
    inverseTest_derivative_pair g hg φ (P 2) 2 (B 2) (hB 2)] at ht
  simp [transformedFlux, map_sub]
  linear_combination ht

end OQ14.Packet05GraphWeakDivergence
#print axioms OQ14.Packet05GraphWeakDivergence.inverseTest_derivative_pair
#print axioms OQ14.Packet05GraphWeakDivergence.inverseTest_value_pair
#print axioms OQ14.Packet05GraphWeakDivergence.graph_pullback_weak_divergence
