import Packet05RegionalGraphPiola
import Packet05GraphL2Constitutive

/-! Regional constitutive identity in graph coordinates. The physical
dielectric is used only on the actual chart neighborhood. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RegionalGraphConstitutive
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.ConicalJunctionPhysical
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap OQ14.Packet05GraphPullback
  OQ14.Packet05GraphVolume OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphGradientValues
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05GraphL2Constitutive
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_graph_constitutive (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (V W : Set Maxwell.Space) (U P Q : L2Vector) (ε : Maxwell.Space → ℂ)
    (hP : ∀ j, ∀ᵐ y ∂volume, y ∈ V → P j y = ε y * (U j y + Q j y))
    (hmap : ∀ x ∈ W, graphMap (liftedHeight g) x ∈ V)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) (j : Fin 3) :
    ∀ᵐ x ∂volume, x ∈ W → transformedFlux g hg P B hB j x =
      ε (graphMap (liftedHeight g) x) *
        ((∑ i : Fin 3, (Packet05GraphChartMatrix.metric
          (Packet05GraphSlope.slope g 0 x) (Packet05GraphSlope.slope g 1 x) j i : ℂ) *
            Packet05GraphH1Pullback.pulledGradient g hg U B hB i x) +
          transformedFlux g hg Q B hB j x) := by
  have hp : ∀ᵐ x ∂volume, ∀ i, x ∈ W → pullback g hg.continuous (P i) x =
      ε (graphMap (liftedHeight g) x) *
        (pullback g hg.continuous (U i) x + pullback g hg.continuous (Q i) x) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [(graph_map_volume_preserving g hg.continuous).quasiMeasurePreserving.ae (hP i),
      pullback_ae g hg.continuous (P i), pullback_ae g hg.continuous (U i),
      pullback_ae g hg.continuous (Q i)] with x hp ha hb hc hx
    rw [ha,hb,hc]
    exact hp (hmap x hx)
  have hgrad : ∀ᵐ x ∂volume, ∀ i, Packet05GraphH1Pullback.pulledGradient g hg U B hB i x =
      Packet05GraphConstitutive.pulledGradient (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) (fun k => pullback g hg.continuous (U k) x) i :=
    ae_all_iff.mpr (fun i => pulledGradient_matches_chart g hg U B hB i)
  filter_upwards [transformedFlux_ae g hg P B hB j, transformedFlux_ae g hg Q B hB j,
    hp,hgrad] with x hp' hq hp hg' hx
  rw [hp',hq]
  simp only [hg']
  fin_cases j <;> simp [hp _ hx, slopeC, Packet05GraphChartMatrix.metric,
    Packet05GraphConstitutive.pulledGradient, Fin.sum_univ_three,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow] <;> ring_nf <;> simp

end OQ14.Packet05RegionalGraphConstitutive
#print axioms OQ14.Packet05RegionalGraphConstitutive.regional_graph_constitutive
