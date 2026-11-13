import Packet05GraphMetricFlux
import Packet05GraphChartMatrix

/-! The constructed L² graph flux has the expected pointwise metric-matrix
values, almost everywhere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace OQ14.Packet05GraphMetricFluxValues
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeightedCoercivity
  OQ14.Packet05GraphMetricFlux OQ14.Packet05GraphChartMatrix
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem metricSquare_ae (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (Q : L2Vector)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i) (i : Fin 2) :
    (fun x => metricSquare g hg Q B hB i.castSucc x) =ᵐ[volume]
      fun x => Q i.castSucc x - slopeC g i.castSucc x * Q 2 x := by
  fin_cases i <;> simp only [Fin.castSucc_zero, Fin.castSucc_one]
  · filter_upwards [Lp.coeFn_sub (Q 0) (slopeMul g hg 0 (B 0) (hB 0) (Q 2)),
      slopeMul_ae g hg 0 (B 0) (hB 0) (Q 2)] with x hs hm
    change (Q 0 - slopeMul g hg 0 (B 0) (hB 0) (Q 2) : L2Scalar) x = Q 0 x - slopeC g 0 x * Q 2 x
    rw [hs]
    simp only [Pi.sub_apply, hm]
  · filter_upwards [Lp.coeFn_sub (Q 1) (slopeMul g hg 1 (B 1) (hB 1) (Q 2)),
      slopeMul_ae g hg 1 (B 1) (hB 1) (Q 2)] with x hs hm
    change (Q 1 - slopeMul g hg 1 (B 1) (hB 1) (Q 2) : L2Scalar) x = Q 1 x - slopeC g 1 x * Q 2 x
    rw [hs]
    simp only [Pi.sub_apply, hm]

theorem metricFlux_ae (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (Q : L2Vector)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i) (j : Fin 3) :
    (fun x => metricFlux g hg Q B hB j x) =ᵐ[volume]
      fun x => ∑ i : Fin 3, (metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j i : ℂ) * Q i x := by
  let R0 := metricSquare g hg Q B hB 0
  let R1 := metricSquare g hg Q B hB 1
  let A := slopeMul g hg 0 (B 0) (hB 0) R0
  let Bv := slopeMul g hg 1 (B 1) (hB 1) R1
  filter_upwards [metricSquare_ae g hg Q B hB 0, metricSquare_ae g hg Q B hB 1,
    slopeMul_ae g hg 0 (B 0) (hB 0) R0, slopeMul_ae g hg 1 (B 1) (hB 1) R1,
    Lp.coeFn_sub (Q 2) A, Lp.coeFn_sub (Q 2 - A) Bv] with x h0 h1 ha hb hs1 hs2
  have hR0 : R0 x = Q 0 x - slopeC g 0 x * Q 2 x := h0
  have hR1 : R1 x = Q 1 x - slopeC g 1 x * Q 2 x := h1
  fin_cases j
  · change R0 x = _
    rw [hR0]
    simp [metric, Fin.sum_univ_three, slopeC]
    <;> ring
  · change R1 x = _
    rw [hR1]
    simp [metric, Fin.sum_univ_three, slopeC]
    <;> ring
  · change (Q 2 - A - Bv : L2Scalar) x = _
    rw [hs2]
    simp only [Pi.sub_apply]
    rw [hs1]
    simp only [Pi.sub_apply]
    change Q 2 x - slopeMul g hg 0 (B 0) (hB 0) R0 x -
      slopeMul g hg 1 (B 1) (hB 1) R1 x = _
    rw [ha,hb,hR0,hR1]
    simp [metric, Fin.sum_univ_three, slopeC, Complex.ofReal_add, Complex.ofReal_pow]
    <;> ring_nf <;> simp

end OQ14.Packet05GraphMetricFluxValues
#print axioms OQ14.Packet05GraphMetricFluxValues.metricSquare_ae
#print axioms OQ14.Packet05GraphMetricFluxValues.metricFlux_ae
