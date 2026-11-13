import Packet05GraphPrincipalEnergy

/-! Coercivity of the exact graph-metric principal pairing on actual L²
fields with the positive binary material coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphPrincipalCoercivity
open OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakGreen OQ14.WeakPower
  OQ14.Packet05FlatWeight OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeightedCoercivity OQ14.Packet05GraphPrincipalEnergy
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_principal_coercive (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (Q : L2Vector) (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (d : ℝ) (hd : 0 ≤ d) :
    let R0 := metricSquare g hg Q B hB 0
    let R1 := metricSquare g hg Q B hB 1
    ‖Q 0‖^2 + ‖Q 1‖^2 + ‖Q 2‖^2 ≤ (2+4*M^2) *
      (scalarProduct (mulWeight d hd R0) (conjScalar (Q 0)) +
       scalarProduct (mulWeight d hd R1) (conjScalar (Q 1)) +
       scalarProduct (mulWeight d hd (Q 2 - slopeMul g hg 0 (B 0) (hB 0) R0 -
         slopeMul g hg 1 (B 1) (hB 1) R1)) (conjScalar (Q 2))).re := by
  dsimp only
  have he := graph_principal_square_identity g hg Q B hB d hd
  have hc := weighted_graph_energy_coercive g hg Q M hM B hB d hd
  rw [he]
  simpa [graphWeightedEnergy, Fin.sum_univ_three, metricSquare, Complex.add_re] using hc

end OQ14.Packet05GraphPrincipalCoercivity
#print axioms OQ14.Packet05GraphPrincipalCoercivity.graph_principal_coercive
