import Packet05GraphPairingAlgebra

/-! Exact positive-square identity for the graph-metric principal pairing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphPrincipalEnergy
open OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakGreen OQ14.WeakPower
  OQ14.Packet05FlatWeight OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeightedCoercivity OQ14.Packet05GraphWeightedPairing
  OQ14.Packet05GraphPairingAlgebra
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_principal_square_identity (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (Q : L2Vector) (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (d : ℝ) (hd : 0 ≤ d) :
    let R0 := metricSquare g hg Q B hB 0
    let R1 := metricSquare g hg Q B hB 1
    scalarProduct (mulWeight d hd R0) (conjScalar (Q 0)) +
    scalarProduct (mulWeight d hd R1) (conjScalar (Q 1)) +
    scalarProduct (mulWeight d hd (Q 2 - slopeMul g hg 0 (B 0) (hB 0) R0 -
      slopeMul g hg 1 (B 1) (hB 1) R1)) (conjScalar (Q 2)) =
    scalarProduct (mulWeight d hd R0) (conjScalar R0) +
    scalarProduct (mulWeight d hd R1) (conjScalar R1) +
    scalarProduct (mulWeight d hd (Q 2)) (conjScalar (Q 2)) := by
  dsimp only
  simp only [metricSquare, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true]
  let R0 := Q 0 - slopeMul g hg 0 (B 0) (hB 0) (Q 2)
  let R1 := Q 1 - slopeMul g hg 1 (B 1) (hB 1) (Q 2)
  change scalarProduct (mulWeight d hd R0) (conjScalar (Q 0)) +
    scalarProduct (mulWeight d hd R1) (conjScalar (Q 1)) +
    scalarProduct (mulWeight d hd (Q 2 - slopeMul g hg 0 (B 0) (hB 0) R0 -
      slopeMul g hg 1 (B 1) (hB 1) R1)) (conjScalar (Q 2)) =
    scalarProduct (mulWeight d hd R0) (conjScalar R0) +
    scalarProduct (mulWeight d hd R1) (conjScalar R1) +
    scalarProduct (mulWeight d hd (Q 2)) (conjScalar (Q 2))
  have e0 : scalarProduct (mulWeight d hd R0) (conjScalar (Q 0)) -
      scalarProduct (mulWeight d hd (slopeMul g hg 0 (B 0) (hB 0) R0)) (conjScalar (Q 2)) =
      scalarProduct (mulWeight d hd R0) (conjScalar R0) := by
    rw [← slope_weighted_pairing g hg 0 (B 0) (hB 0) d hd R0 (Q 2)]
    change _ = scalarProduct (mulWeight d hd R0) (conjScalar (Q 0 - slopeMul g hg 0 (B 0) (hB 0) (Q 2)))
    rw [conjugate_sub, map_sub]
  have e1 : scalarProduct (mulWeight d hd R1) (conjScalar (Q 1)) -
      scalarProduct (mulWeight d hd (slopeMul g hg 1 (B 1) (hB 1) R1)) (conjScalar (Q 2)) =
      scalarProduct (mulWeight d hd R1) (conjScalar R1) := by
    rw [← slope_weighted_pairing g hg 1 (B 1) (hB 1) d hd R1 (Q 2)]
    change _ = scalarProduct (mulWeight d hd R1) (conjScalar (Q 1 - slopeMul g hg 1 (B 1) (hB 1) (Q 2)))
    rw [conjugate_sub, map_sub]
  have hf : mulWeight d hd (Q 2 - slopeMul g hg 0 (B 0) (hB 0) R0 - slopeMul g hg 1 (B 1) (hB 1) R1) =
      mulWeight d hd (Q 2) - mulWeight d hd (slopeMul g hg 0 (B 0) (hB 0) R0) -
        mulWeight d hd (slopeMul g hg 1 (B 1) (hB 1) R1) := by
    rw [mulWeight_sub, mulWeight_sub]
  rw [hf, scalarProduct_sub_left, scalarProduct_sub_left]
  linear_combination e0 + e1

end OQ14.Packet05GraphPrincipalEnergy
#print axioms OQ14.Packet05GraphPrincipalEnergy.graph_principal_square_identity
