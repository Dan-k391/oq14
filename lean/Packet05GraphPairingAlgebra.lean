import Packet05GraphWeightedPairing
import Packet05ScalarEnergyIdentity

/-! Algebra of actual L² weighted Hermitian pairings needed to identify the
graph-metric principal term with its positive square decomposition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphPairingAlgebra
open MeasureTheory OQ14.WeakCurl OQ14.WeakGreen OQ14.WeakPower OQ14.Packet05FlatWeight
open scoped ComplexConjugate

theorem conjugate_sub (u v : L2Scalar) : conjScalar (u-v) = conjScalar u-conjScalar v := by
  apply Lp.ext
  filter_upwards [conjScalar_ae (u-v), conjScalar_ae u, conjScalar_ae v,
    Lp.coeFn_sub u v, Lp.coeFn_sub (conjScalar u) (conjScalar v)] with x h0 h1 h2 ha hb
  rw [h0,ha,hb]
  simp only [Pi.sub_apply, h1, h2, map_sub]

theorem mulWeight_sub (d : ℝ) (hd : 0 ≤ d) (u v : L2Scalar) :
    mulWeight d hd (u-v) = mulWeight d hd u - mulWeight d hd v := by
  apply Lp.ext
  filter_upwards [mulWeight_ae d hd (u-v), mulWeight_ae d hd u, mulWeight_ae d hd v,
    Lp.coeFn_sub u v, Lp.coeFn_sub (mulWeight d hd u) (mulWeight d hd v)] with x h0 h1 h2 ha hb
  rw [h0,ha,hb]
  simp only [Pi.sub_apply, h1, h2, mul_sub]

theorem scalarProduct_sub_left (u v w : L2Scalar) :
    scalarProduct (u-v) w = scalarProduct u w - scalarProduct v w := by
  simp only [scalarProduct_integral]
  rw [← integral_sub (scalarProduct_integrable u w) (scalarProduct_integrable v w)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v] with x hx
  rw [hx]
  simp only [Pi.sub_apply, sub_mul]

end OQ14.Packet05GraphPairingAlgebra
#print axioms OQ14.Packet05GraphPairingAlgebra.conjugate_sub
#print axioms OQ14.Packet05GraphPairingAlgebra.mulWeight_sub
#print axioms OQ14.Packet05GraphPairingAlgebra.scalarProduct_sub_left
