import Packet05ScalarPrincipalLocalization
import Packet05GraphPairingAlgebra

/-! Move a real compact cutoff across the weighted Hermitian pairing and
through the graph's matrix field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarCutoffTransfer
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakPower OQ14.WeakConservation OQ14.Packet05FlatWeight
  OQ14.Packet05TensorCommutator OQ14.Packet05GraphFluxExtension OQ14.Packet05ScalarPrincipalLocalization
open scoped ComplexConjugate

def cutScalar (ζ : RealTest Set.univ) (u : L2Scalar) : L2Scalar :=
  scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact u

theorem cutScalar_ae (ζ : RealTest Set.univ) (u : L2Scalar) :
    (fun x => cutScalar ζ u x) =ᵐ[volume] fun x => (ζ.function x : ℂ) * u x :=
  scaleL2_ae ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact u

theorem real_cutoff_pairing (ζ : RealTest Set.univ) (u v : L2Scalar) :
    scalarProduct u (conjScalar (cutScalar ζ v)) = scalarProduct (cutScalar ζ u) (conjScalar v) := by
  rw [scalarProduct_integral, scalarProduct_integral]
  apply integral_congr_ae
  filter_upwards [conjScalar_ae (cutScalar ζ v), conjScalar_ae v,
    cutScalar_ae ζ u, cutScalar_ae ζ v] with x hc1 hc2 hu hv
  rw [hc1,hc2,hu,hv]
  simp only [map_mul, Complex.conj_ofReal]
  ring

theorem cutoff_weight_commute (ζ : RealTest Set.univ) (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar) :
    cutScalar ζ (mulWeight d hd u) = mulWeight d hd (cutScalar ζ u) := by
  apply Lp.ext
  filter_upwards [cutScalar_ae ζ (mulWeight d hd u), cutScalar_ae ζ u,
    mulWeight_ae d hd u, mulWeight_ae d hd (cutScalar ζ u)] with x h1 h2 h3 h4
  rw [h1,h3,h4,h2]
  ring

theorem cutoff_matrix_commute (ζ : RealTest Set.univ) (A : Fin 3 → Fin 3 → Test)
    (Q : L2Vector) (j : Fin 3) :
    cutScalar ζ (matrixField A Q j) = matrixField A (cutVector ζ Q) j := by
  apply Lp.ext
  have hQ : ∀ᵐ x ∂volume, ∀ i, cutVector ζ Q i x = (ζ.function x : ℂ) * Q i x :=
    ae_all_iff.mpr (fun i => cutVector_ae ζ Q i)
  filter_upwards [cutScalar_ae ζ (matrixField A Q j), matrixField_ae A Q j,
    matrixField_ae A (cutVector ζ Q) j, hQ] with x h0 h1 h2 hq
  rw [h0,h1,h2]
  simp only [hq, Fin.sum_univ_three]
  ring

end OQ14.Packet05ScalarCutoffTransfer
#print axioms OQ14.Packet05ScalarCutoffTransfer.cutScalar_ae
#print axioms OQ14.Packet05ScalarCutoffTransfer.real_cutoff_pairing
#print axioms OQ14.Packet05ScalarCutoffTransfer.cutoff_weight_commute
#print axioms OQ14.Packet05ScalarCutoffTransfer.cutoff_matrix_commute
