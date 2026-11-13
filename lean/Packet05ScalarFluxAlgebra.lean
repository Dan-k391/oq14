import Packet05RegionalFluxCutoff
import Packet05ScalarCutoffTransfer
import Packet05ScalarEnergyIdentity
import Packet05GraphPairingAlgebra
import Packet05ScalarDielectricFlux

/-! Linear and cutoff algebra for localizing the actual scalar flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarFluxAlgebra
open MeasureTheory Set OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator OQ14.Packet05GraphFluxExtension
  OQ14.Packet05GraphPairingAlgebra OQ14.Packet05ScalarEnergyIdentity
  OQ14.Packet05ScalarPrincipalLocalization OQ14.Packet05ScalarCutoffTransfer
  OQ14.Packet05ScalarDielectricFlux

theorem cutScalar_sub (ζ : RealTest Set.univ) (u v : L2Scalar) :
    cutScalar ζ (u-v) = cutScalar ζ u-cutScalar ζ v := by
  apply Lp.ext
  filter_upwards [cutScalar_ae ζ (u-v), cutScalar_ae ζ u, cutScalar_ae ζ v,
    Lp.coeFn_sub u v, Lp.coeFn_sub (cutScalar ζ u) (cutScalar ζ v)] with x h0 h1 h2 ha hb
  rw [h0,ha,hb]
  simp only [Pi.sub_apply, h1, h2, mul_sub]

theorem matrixField_add (A : Fin 3 → Fin 3 → Test) (C G : L2Vector) (j : Fin 3) :
    matrixField A (fun k => C k+G k) j = matrixField A C j+matrixField A G j := by
  apply Lp.ext
  have hCG : ∀ᵐ x ∂volume, ∀ k, (C k+G k : L2Scalar) x = C k x + G k x :=
    ae_all_iff.mpr (fun k => by filter_upwards [Lp.coeFn_add (C k) (G k)] with x hx; simpa using hx)
  filter_upwards [matrixField_ae A (fun k => C k+G k) j, matrixField_ae A C j,
    matrixField_ae A G j, Lp.coeFn_add (matrixField A C j) (matrixField A G j), hCG] with x h0 h1 h2 ha hc
  rw [h0,ha]
  simp only [Pi.add_apply, h1, h2, hc, Fin.sum_univ_three]
  ring

theorem flux_add (A : Fin 3 → Fin 3 → Test) (C G : L2Vector) (d : ℝ) (hd : 0 ≤ d) (j : Fin 3) :
    flux A (fun k => C k+G k) d hd j = flux A C d hd j+flux A G d hd j := by
  simp only [flux, matrixField_add, mulWeight_add]

theorem cutoff_flux_commute (ζ : RealTest Set.univ) (A : Fin 3 → Fin 3 → Test)
    (C : L2Vector) (d : ℝ) (hd : 0 ≤ d) (j : Fin 3) :
    cutScalar ζ (flux A C d hd j) = flux A (cutVector ζ C) d hd j := by
  rw [show flux A C d hd j = mulWeight d hd (matrixField A C j) from rfl,
    cutoff_weight_commute, cutoff_matrix_commute]
  rfl

end OQ14.Packet05ScalarFluxAlgebra
#print axioms OQ14.Packet05ScalarFluxAlgebra.cutScalar_sub
#print axioms OQ14.Packet05ScalarFluxAlgebra.matrixField_add
#print axioms OQ14.Packet05ScalarFluxAlgebra.flux_add
#print axioms OQ14.Packet05ScalarFluxAlgebra.cutoff_flux_commute
