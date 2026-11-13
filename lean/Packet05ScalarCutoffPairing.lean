import Packet05ScalarSquareCutoff

/-! Split the square-cutoff weak-test pairing into localized gradient and
localized cutoff-gradient terms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarCutoffPairing
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakPower OQ14.WeakConservation OQ14.WeakEnergy
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarCutoffTesting OQ14.Packet05ScalarSquareCutoff
open scoped ComplexConjugate

theorem conjScalar_add (u v : L2Scalar) : conjScalar (u+v) = conjScalar u + conjScalar v := by
  apply Lp.ext
  filter_upwards [conjScalar_ae (u+v), conjScalar_ae u, conjScalar_ae v,
    Lp.coeFn_add u v, Lp.coeFn_add (conjScalar u) (conjScalar v)] with x h0 h1 h2 ha hb
  rw [h0,ha,hb]
  simp only [Pi.add_apply, h1, h2, map_add]

theorem conjScalar_two (u : L2Scalar) : conjScalar ((2 : ℂ) • u) = (2 : ℂ) • conjScalar u := by
  apply Lp.ext
  filter_upwards [conjScalar_ae ((2 : ℂ) • u), conjScalar_ae u,
    Lp.coeFn_smul (2 : ℂ) u, Lp.coeFn_smul (2 : ℂ) (conjScalar u)] with x h0 h1 ha hb
  rw [h0,ha,hb]
  simp only [Pi.smul_apply, smul_eq_mul, h1, map_mul, map_ofNat]

theorem square_cutoff_test_pairing (ζ : RealTest Set.univ) (u w : L2Scalar)
    (Q : Fin 3 → L2Scalar) (i : Fin 3) :
    scalarProduct u (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest w Q i)) =
      scalarProduct (cutScalar ζ u) (conjScalar (cutScalar ζ (Q i))) +
        (2 : ℂ) * scalarProduct (cutScalar ζ u) (conjScalar (cutoffGradient ζ w i)) := by
  rw [square_cutoff_derivative, conjScalar_add, conjScalar_two, map_add, map_smul]
  simp only [smul_eq_mul]
  rw [real_cutoff_pairing ζ u (cutScalar ζ (Q i)), real_cutoff_pairing ζ u (cutoffGradient ζ w i)]

end OQ14.Packet05ScalarCutoffPairing
#print axioms OQ14.Packet05ScalarCutoffPairing.conjScalar_add
#print axioms OQ14.Packet05ScalarCutoffPairing.conjScalar_two
#print axioms OQ14.Packet05ScalarCutoffPairing.square_cutoff_test_pairing
