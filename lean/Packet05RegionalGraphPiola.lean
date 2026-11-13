import Packet05ActualNormalFluxContinuous
import Packet05GraphWeakDivergence

/-! Piola transport of a regional weak divergence equation through the actual
graph homeomorphism. No material equality outside the chart is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RegionalGraphPiola
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.ConicalJunctionPhysical OQ14.Packet05RegionalDivergence
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap OQ14.Packet05GraphSmooth
  OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeakDivergence
  OQ14.Packet05GraphNormalWeakDerivative
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem inverse_test_support (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (φ : Test)
    (W V : Set Maxwell.Space) (hφ : tsupport φ.function ⊆ W)
    (hmap : ∀ x ∈ W, graphMap (liftedHeight g) x ∈ V) :
    tsupport (inverseTest g hg φ).function ⊆ V := by
  have hs : tsupport (inverseTest g hg φ).function ⊆
      (inverseGraphMap (liftedHeight g)) ⁻¹' tsupport φ.function := by
    apply closure_minimal
    · intro y hy
      exact subset_tsupport _ hy
    · exact (isClosed_tsupport φ.function).preimage (inverseGraphMap_contDiff g hg).continuous
  intro y hy
  have hx : inverseGraphMap (liftedHeight g) y ∈ W := hφ (hs hy)
  have hm := hmap _ hx
  simpa only [graph_map_right_inverse _ (liftedHeight_normal_invariant g)] using hm

theorem regional_graph_piola (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (V W : Set Maxwell.Space) (P : L2Vector) (D : L2Scalar)
    (hdiv : HasDivergenceOn V P D)
    (hmap : ∀ x ∈ W, graphMap (liftedHeight g) x ∈ V)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) :
    HasDivergenceOn W (transformedFlux g hg P B hB) (pullback g hg.continuous D) := by
  intro φ hφ
  have ht := hdiv (inverseTest g (hg.of_le (by decide)) φ)
    (inverse_test_support g (hg.of_le (by decide)) φ W V hφ hmap)
  rw [inverseTest_value_pair g hg φ D] at ht
  rw [inverseTest_derivative_pair g hg φ (P 0) 0 (B 0) (hB 0),
    inverseTest_derivative_pair g hg φ (P 1) 1 (B 1) (hB 1),
    inverseTest_derivative_pair g hg φ (P 2) 2 (B 2) (hB 2)] at ht
  simp [transformedFlux, map_sub]
  linear_combination ht

end OQ14.Packet05RegionalGraphPiola
#print axioms OQ14.Packet05RegionalGraphPiola.inverse_test_support
#print axioms OQ14.Packet05RegionalGraphPiola.regional_graph_piola
