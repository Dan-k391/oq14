import Packet05GraphFluxExtension
import Packet05FlatWeight
import WeakPoynting.Energy
import WeakPoynting.Poynting

/-! Exact localization of the binary-weighted principal pairing with a real
square cutoff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
namespace OQ14.Packet05ScalarPrincipalLocalization
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakPower OQ14.WeakConservation OQ14.WeakEnergy OQ14.Packet05FlatWeight
  OQ14.Packet05TensorCommutator OQ14.Packet05GraphFluxExtension
open scoped ComplexConjugate

def cutVector (ζ : RealTest Set.univ) (Q : L2Vector) : L2Vector := fun j =>
  scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact (Q j)

theorem cutVector_ae (ζ : RealTest Set.univ) (Q : L2Vector) (j : Fin 3) :
    (fun x => cutVector ζ Q j x) =ᵐ[volume] fun x => (ζ.function x : ℂ) * Q j x :=
  scaleL2_ae ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact (Q j)

theorem square_cutoff_principal_pairing (ζ : RealTest Set.univ)
    (A : Fin 3 → Fin 3 → Test) (Q : L2Vector) (d : ℝ) (hd : 0 ≤ d) (j : Fin 3) :
    scalarProduct (mulWeight d hd (matrixField A Q j))
      (conjScalar (scaleL2 (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
        (squareTest ζ).complexTest.compact (Q j))) =
    scalarProduct (mulWeight d hd (matrixField A (cutVector ζ Q) j)) (conjScalar (cutVector ζ Q j)) := by
  rw [scalarProduct_integral, scalarProduct_integral]
  apply integral_congr_ae
  have hQ : ∀ᵐ x ∂volume, ∀ i, cutVector ζ Q i x = (ζ.function x : ℂ) * Q i x :=
    ae_all_iff.mpr (fun i => cutVector_ae ζ Q i)
  filter_upwards [mulWeight_ae d hd (matrixField A Q j), mulWeight_ae d hd (matrixField A (cutVector ζ Q) j),
    matrixField_ae A Q j, matrixField_ae A (cutVector ζ Q) j,
    conjScalar_ae (scaleL2 (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
      (squareTest ζ).complexTest.compact (Q j)),
    scaleL2_ae (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
      (squareTest ζ).complexTest.compact (Q j),
    conjScalar_ae (cutVector ζ Q j), hQ] with x hw1 hw2 hA1 hA2 hc1 hs1 hc2 hq
  rw [hw1,hw2,hA1,hA2,hc1,hs1,hc2]
  simp only [hq]
  simp only [Fin.sum_univ_three, RealTest.complexTest, squareTest, Complex.ofReal_pow,
    map_mul, map_pow, Complex.conj_ofReal]
  ring

end OQ14.Packet05ScalarPrincipalLocalization
#print axioms OQ14.Packet05ScalarPrincipalLocalization.cutVector_ae
#print axioms OQ14.Packet05ScalarPrincipalLocalization.square_cutoff_principal_pairing
