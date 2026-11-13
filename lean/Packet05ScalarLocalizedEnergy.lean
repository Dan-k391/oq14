import Packet05ScalarVectorBounds
import Packet05ScalarLocalizedCoercivity

/-! Exact localized energy balance for the genuine difference quotient,
with cutoff and source terms kept separately. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05ScalarLocalizedEnergy
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakPower
  OQ14.DivCurlCompact OQ14.WeakConservation OQ14.WeakEnergy OQ14.Packet05FlatWeight
  OQ14.MaxwellDifferenceQuotient OQ14.Packet05TensorCommutator
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05ScalarSquareCutoff OQ14.Packet05ScalarCutoffPairing
  OQ14.Packet05ScalarTransmissionCommutator OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarEnergyIdentity

def localizedMatrixFlux (ζ : RealTest Set.univ) (A : Fin 3 → Fin 3 → Test)
    (Q : L2Vector) (d : ℝ) (hd : 0 ≤ d) : L2Vector := fun j =>
  mulWeight d hd (matrixField A (cutVector ζ Q) j)

def localizedResidual (ζ : RealTest Set.univ) (A : Fin 3 → Fin 3 → Test)
    (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) : L2Vector := fun j =>
  cutScalar ζ (mulWeight d hd (matrixResidual A C i j h hh b hb) - quotient (F j) i h)

def localizedCutoffGradient (ζ : RealTest Set.univ) (w : L2Scalar) : L2Vector :=
  fun j => cutoffGradient ζ w j

theorem localized_difference_energy_identity
    (A : Fin 3 → Fin 3 → Test) (u : L2Scalar) (C F : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) 0)
    (ζ : RealTest Set.univ) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    let Q : L2Vector := fun j => quotient (C j) i h
    let L := localizedMatrixFlux ζ A Q d hd
    let Z := cutVector ζ Q
    let R := localizedResidual ζ A C F d hd i h hh b hb
    let T := localizedCutoffGradient ζ (quotient u i h)
    (∑ j : Fin 3, scalarProduct (L j) (conjScalar (Z j))) +
      (2 : ℂ) * (∑ j : Fin 3, scalarProduct (L j) (conjScalar (T j))) +
      (∑ j : Fin 3, scalarProduct (R j) (conjScalar (Z j))) +
      (2 : ℂ) * (∑ j : Fin 3, scalarProduct (R j) (conjScalar (T j))) = 0 := by
  dsimp only
  have he := principal_energy_balance A u C F d hd hC hdiv (squareTest ζ).complexTest.toTest i hi h hh b hb
  simp_rw [square_cutoff_test_pairing] at he
  simp_rw [cutoff_weight_commute, cutoff_matrix_commute] at he
  simp only [Fin.sum_univ_three] at he ⊢
  change _ at he
  simp only [cutVector, cutScalar] at he
  simp only [localizedMatrixFlux, localizedResidual, localizedCutoffGradient, cutVector, cutScalar] at ⊢
  linear_combination he

end OQ14.Packet05ScalarLocalizedEnergy
#print axioms OQ14.Packet05ScalarLocalizedEnergy.localized_difference_energy_identity
