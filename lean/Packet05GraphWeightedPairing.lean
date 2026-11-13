import Packet05GraphWeightedCoercivity

/-! Bounded real graph slopes transfer between the two factors of the actual
binary-weighted Hermitian L² pairing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphWeightedPairing
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakGreen OQ14.WeakPower
  OQ14.Packet05FlatWeight OQ14.Packet05GraphSlopeMultiplier
open scoped ComplexConjugate
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem slope_weighted_pairing (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    (B : ℝ) (hB : ∀ x, ‖slopeC g i x‖ ≤ B) (d : ℝ) (hd : 0 ≤ d) (u v : L2Scalar) :
    scalarProduct (mulWeight d hd u) (conjScalar (slopeMul g hg i B hB v)) =
      scalarProduct (mulWeight d hd (slopeMul g hg i B hB u)) (conjScalar v) := by
  rw [scalarProduct_integral, scalarProduct_integral]
  apply integral_congr_ae
  filter_upwards [mulWeight_ae d hd u, mulWeight_ae d hd (slopeMul g hg i B hB u),
    slopeMul_ae g hg i B hB u, slopeMul_ae g hg i B hB v,
    conjScalar_ae (slopeMul g hg i B hB v), conjScalar_ae v] with x hw hwu hsu hsv hcv hcu
  rw [hw,hwu,hsu,hcv,hcu,hsv]
  simp only [map_mul, slopeC, Complex.conj_ofReal]
  ring

end OQ14.Packet05GraphWeightedPairing
#print axioms OQ14.Packet05GraphWeightedPairing.slope_weighted_pairing
