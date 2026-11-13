import Packet05GraphGradientValues
import Packet05GraphWeakDivergence

/-! Lift the graph-metric constitutive identity to actual L² equivalence
classes, with an arbitrary measurable physical coefficient. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05GraphL2Constitutive
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap
  OQ14.Packet05GraphPullback OQ14.Packet05GraphVolume
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphGradientValues
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05GraphConstitutive
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem pulled_constitutive_ae (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (U P : L2Vector) (ε : Space → ℂ)
    (hP : ∀ j, (fun y => P j y) =ᵐ[volume] fun y => ε y * U j y) (j : Fin 3) :
    (fun x => pullback g hg.continuous (P j) x) =ᵐ[volume]
      fun x => ε (graphMap (liftedHeight g) x) * pullback g hg.continuous (U j) x := by
  filter_upwards [(graph_map_volume_preserving g hg.continuous).quasiMeasurePreserving.ae (hP j),
    pullback_ae g hg.continuous (P j), pullback_ae g hg.continuous (U j)] with x hp hpa hua
  rw [hpa,hua,hp]

theorem transformedFlux_ae (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (P : L2Vector) (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) (j : Fin 3) :
    (fun x => transformedFlux g hg P B hB j x) =ᵐ[volume]
      fun x => if j = 2 then pullback g hg.continuous (P 2) x -
        slopeC g 0 x * pullback g hg.continuous (P 0) x -
        slopeC g 1 x * pullback g hg.continuous (P 1) x
      else pullback g hg.continuous (P j) x := by
  let R (i : Fin 3) := slopeMul g hg i (B i) (hB i) (pullback g hg.continuous (P i))
  have hR : ∀ᵐ x ∂volume, ∀ i, R i x = slopeC g i x * pullback g hg.continuous (P i) x :=
    ae_all_iff.mpr (fun i => slopeMul_ae g hg i (B i) (hB i) _)
  filter_upwards [hR, Lp.coeFn_sub (pullback g hg.continuous (P 2)) (R 0),
    Lp.coeFn_sub (pullback g hg.continuous (P 2) - R 0) (R 1),
    Lp.coeFn_sub (pullback g hg.continuous (P 2) - R 0 - R 1) (R 2)] with x hr h0 h1 h2
  fin_cases j <;> simp only [transformedFlux, Fin.isValue, reduceIte]
  · rfl
  · rfl
  · change (pullback g hg.continuous (P 2) - R 0 - R 1 - R 2 : L2Scalar) x = _
    rw [h2]
    simp only [Pi.sub_apply]
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h0]
    simp [hr, normal_slope_zero g hg x]

theorem graph_constitutive_l2 (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (U P : L2Vector) (ε : Space → ℂ)
    (hP : ∀ j, (fun y => P j y) =ᵐ[volume] fun y => ε y * U j y)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) (j : Fin 3) :
    (fun x => transformedFlux g hg P B hB j x) =ᵐ[volume]
      fun x => ε (graphMap (liftedHeight g) x) *
        ∑ i : Fin 3, (Packet05GraphChartMatrix.metric
          (Packet05GraphSlope.slope g 0 x) (Packet05GraphSlope.slope g 1 x) j i : ℂ) *
            Packet05GraphH1Pullback.pulledGradient g hg U B hB i x := by
  have hp : ∀ᵐ x ∂volume, ∀ i, pullback g hg.continuous (P i) x =
      ε (graphMap (liftedHeight g) x) * pullback g hg.continuous (U i) x :=
    ae_all_iff.mpr (fun i => pulled_constitutive_ae g hg U P ε hP i)
  have hgrad : ∀ᵐ x ∂volume, ∀ i, Packet05GraphH1Pullback.pulledGradient g hg U B hB i x =
      Packet05GraphConstitutive.pulledGradient (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) (fun k => pullback g hg.continuous (U k) x) i :=
    ae_all_iff.mpr (fun i => pulledGradient_matches_chart g hg U B hB i)
  filter_upwards [transformedFlux_ae g hg P B hB j, hp, hgrad] with x hf hp hg'
  rw [hf]
  simp only [hg']
  fin_cases j <;> simp [hp, slopeC, Packet05GraphChartMatrix.metric,
    Packet05GraphConstitutive.pulledGradient, Fin.sum_univ_three,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow] <;> ring_nf <;> simp

end OQ14.Packet05GraphL2Constitutive
#print axioms OQ14.Packet05GraphL2Constitutive.pulled_constitutive_ae
#print axioms OQ14.Packet05GraphL2Constitutive.transformedFlux_ae
#print axioms OQ14.Packet05GraphL2Constitutive.graph_constitutive_l2
