import Packet05GraphPrincipalCoercivity

/-! L² graph-metric flux and its exact quantitative principal coercivity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphMetricFlux
open OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakGreen OQ14.WeakPower
  OQ14.Packet05FlatWeight OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeightedCoercivity OQ14.Packet05GraphPrincipalCoercivity
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def metricFlux (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (Q : L2Vector)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i) : L2Vector := fun j =>
  if j = 0 then metricSquare g hg Q B hB 0
  else if j = 1 then metricSquare g hg Q B hB 1
  else Q 2 - slopeMul g hg 0 (B 0) (hB 0) (metricSquare g hg Q B hB 0) -
    slopeMul g hg 1 (B 1) (hB 1) (metricSquare g hg Q B hB 1)

theorem metric_flux_coercivity (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (Q : L2Vector) (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (d : ℝ) (hd : 0 ≤ d) :
    ‖Q 0‖^2 + ‖Q 1‖^2 + ‖Q 2‖^2 ≤ (2+4*M^2) *
      (∑ j : Fin 3, scalarProduct (mulWeight d hd (metricFlux g hg Q B hB j))
        (conjScalar (Q j))).re := by
  have h := graph_principal_coercive g hg Q M hM B hB d hd
  simpa [metricFlux, Fin.sum_univ_three] using h

end OQ14.Packet05GraphMetricFlux
#print axioms OQ14.Packet05GraphMetricFlux.metric_flux_coercivity
