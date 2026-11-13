import Packet05DielectricEnergy

/-! Quantitative coercivity of the graph-metric Hermitian energy with the
actual positive binary dielectric. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphWeightedCoercivity
open OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakGreen OQ14.WeakPower
  OQ14.Packet05FlatWeight OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphL2Coercivity
  OQ14.Packet05DielectricEnergy
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def metricSquare (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (Q : L2Vector)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i) : L2Vector := fun j =>
  if j = 0 then Q 0 - slopeMul g hg 0 (B 0) (hB 0) (Q 2)
  else if j = 1 then Q 1 - slopeMul g hg 1 (B 1) (hB 1) (Q 2)
  else Q 2

def graphWeightedEnergy (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (Q : L2Vector)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i) (d : ℝ) (hd : 0 ≤ d) : ℝ :=
  ∑ j : Fin 3, (scalarProduct (mulWeight d hd (metricSquare g hg Q B hB j))
    (conjScalar (metricSquare g hg Q B hB j))).re

theorem weighted_graph_energy_coercive (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (Q : L2Vector) (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (d : ℝ) (hd : 0 ≤ d) :
    ‖Q 0‖^2 + ‖Q 1‖^2 + ‖Q 2‖^2 ≤ (2+4*M^2) * graphWeightedEnergy g hg Q B hB d hd := by
  have hc := graph_metric_l2_coercive g hg Q M hM (B 0) (B 1) (hB 0) (hB 1)
  have h0 := dielectric_energy_lower d hd (metricSquare g hg Q B hB 0)
  have h1 := dielectric_energy_lower d hd (metricSquare g hg Q B hB 1)
  have h2 := dielectric_energy_lower d hd (metricSquare g hg Q B hB 2)
  have hp : 0 ≤ 2+4*M^2 := by positivity
  unfold graphWeightedEnergy
  simp [Fin.sum_univ_three, metricSquare] at h0 h1 h2 ⊢
  have hm := mul_nonneg hp (show 0 ≤
    (scalarProduct (mulWeight d hd (Q 0 - slopeMul g hg 0 (B 0) (hB 0) (Q 2)))
      (conjScalar (Q 0 - slopeMul g hg 0 (B 0) (hB 0) (Q 2)))).re +
    (scalarProduct (mulWeight d hd (Q 1 - slopeMul g hg 1 (B 1) (hB 1) (Q 2)))
      (conjScalar (Q 1 - slopeMul g hg 1 (B 1) (hB 1) (Q 2)))).re +
    (scalarProduct (mulWeight d hd (Q 2)) (conjScalar (Q 2))).re -
      (‖Q 0 - slopeMul g hg 0 (B 0) (hB 0) (Q 2)‖^2 +
       ‖Q 1 - slopeMul g hg 1 (B 1) (hB 1) (Q 2)‖^2 + ‖Q 2‖^2) by linarith)
  nlinarith

end OQ14.Packet05GraphWeightedCoercivity
#print axioms OQ14.Packet05GraphWeightedCoercivity.weighted_graph_energy_coercive
