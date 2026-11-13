import Packet05BinaryForcingTangential

/-! Compact support is preserved by the actual graph pullback and Piola map. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphPiolaCompact
open MeasureTheory Set OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap
  OQ14.Packet05GraphVolume OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_pullback_compact (g : Plane → ℝ) (hg : Continuous g) (u : L2Scalar)
    (hu : CompactRepresentative u) : CompactRepresentative (pullback g hg u) := by
  obtain ⟨f,hfc,huf⟩ := hu
  let e := physicalGraphHomeomorph g hg
  refine ⟨fun x => f (graphMap (liftedHeight g) x), ?_, ?_⟩
  · exact hfc.comp_homeomorph e
  · have he := (graph_map_volume_preserving g hg).quasiMeasurePreserving.ae huf
    filter_upwards [pullback_ae g hg u, he] with x hx hy
    exact hx.trans hy

theorem slope_mul_compact (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    (B : ℝ) (hB : ∀ x, ‖slopeC g i x‖ ≤ B) (u : L2Scalar) (hu : CompactRepresentative u) :
    CompactRepresentative (slopeMul g hg i B hB u) := by
  obtain ⟨f,hfc,huf⟩ := hu
  refine ⟨fun x => slopeC g i x * f x, hfc.mul_left, ?_⟩
  filter_upwards [slopeMul_ae g hg i B hB u, huf] with x hx hy
  rw [hx,hy]

theorem compact_sub (u v : L2Scalar) (hu : CompactRepresentative u) (hv : CompactRepresentative v) :
    CompactRepresentative (u-v) := by
  obtain ⟨f,hf,huf⟩ := hu
  obtain ⟨g,hg,hvg⟩ := hv
  refine ⟨f-g, ?_, ?_⟩
  · simpa only [sub_eq_add_neg] using hf.add hg.neg'
  · filter_upwards [Lp.coeFn_sub u v,huf,hvg] with x hx hy hz
    simp only [hx, Pi.sub_apply, hy, hz]

theorem graph_piola_compact (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (P : L2Vector)
    (hP : ∀ i, CompactRepresentative (P i)) (B : Fin 3 → ℝ)
    (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) :
    ∀ j, CompactRepresentative (transformedFlux g hg P B hB j) := by
  have hp (i : Fin 3) := graph_pullback_compact g hg.continuous (P i) (hP i)
  have hm (i : Fin 3) := slope_mul_compact g hg i (B i) (hB i) _ (hp i)
  intro j
  by_cases hj : j = 2
  · simp only [transformedFlux, hj, ↓reduceIte]
    exact compact_sub _ _ (compact_sub _ _ (compact_sub _ _ (hp 2) (hm 0)) (hm 1)) (hm 2)
  · simpa only [transformedFlux, hj, ↓reduceIte] using hp j

end OQ14.Packet05GraphPiolaCompact
#print axioms OQ14.Packet05GraphPiolaCompact.graph_pullback_compact
#print axioms OQ14.Packet05GraphPiolaCompact.slope_mul_compact
#print axioms OQ14.Packet05GraphPiolaCompact.compact_sub
#print axioms OQ14.Packet05GraphPiolaCompact.graph_piola_compact
