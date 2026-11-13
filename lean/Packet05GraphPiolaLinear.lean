import Packet05GraphL2Constitutive

/-! Linearity of the graph Piola transform, allowing a genuine L² forcing
field to remain explicit in the transformed scalar transmission equation. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphPiolaLinear
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap
  OQ14.Packet05GraphPullback OQ14.Packet05GraphVolume
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeakDivergence
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem pullback_add (g : Plane → ℝ) (hg : Continuous g) (u v : L2Scalar) :
    pullback g hg (u+v) = pullback g hg u + pullback g hg v := by
  exact map_add (Lp.compMeasurePreserving (graphMap (liftedHeight g)) (graph_map_volume_preserving g hg)) u v

theorem slopeMul_add (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    (B : ℝ) (hB : ∀ x, ‖slopeC g i x‖ ≤ B) (u v : L2Scalar) :
    slopeMul g hg i B hB (u+v) = slopeMul g hg i B hB u + slopeMul g hg i B hB v := by
  apply Lp.ext
  filter_upwards [slopeMul_ae g hg i B hB (u+v), slopeMul_ae g hg i B hB u,
    slopeMul_ae g hg i B hB v, Lp.coeFn_add u v,
    Lp.coeFn_add (slopeMul g hg i B hB u) (slopeMul g hg i B hB v)] with x h0 h1 h2 ha hb
  rw [h0,ha,hb]
  simp only [Pi.add_apply]
  rw [h1,h2,mul_add]

theorem transformedFlux_add (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (P Q : L2Vector) (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) (j : Fin 3) :
    transformedFlux g hg (fun i => P i + Q i) B hB j =
      transformedFlux g hg P B hB j + transformedFlux g hg Q B hB j := by
  fin_cases j <;> simp [transformedFlux, pullback_add, slopeMul_add]
  <;> abel

end OQ14.Packet05GraphPiolaLinear
#print axioms OQ14.Packet05GraphPiolaLinear.pullback_add
#print axioms OQ14.Packet05GraphPiolaLinear.slopeMul_add
#print axioms OQ14.Packet05GraphPiolaLinear.transformedFlux_add
