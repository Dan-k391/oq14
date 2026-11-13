import Packet05RegionalScalarFluxTest
import Packet05ScalarLocalizedEnergy

/-! The localized scalar quotient energy identity with an arbitrary global
source that vanishes near the two translated inner supports. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RegionalScalarEnergy
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakPower
  OQ14.DivCurlCompact OQ14.WeakConservation OQ14.WeakEnergy OQ14.Packet05FlatWeight
  OQ14.MaxwellDifferenceQuotient OQ14.Packet05TensorCommutator
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05ScalarSquareCutoff OQ14.Packet05ScalarCutoffPairing
  OQ14.Packet05ScalarTransmissionCommutator OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarEnergyIdentity OQ14.Packet05ScalarLocalizedEnergy OQ14.Packet05RegionalScalarFluxTest OQ14.Packet05RegionalDivergence

theorem regional_difference_energy_identity
    (A : Fin 3 → Fin 3 → Test) (u : L2Scalar) (C F : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (V S : Set Space) (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (θ : Test) (hθV : tsupport θ.function ⊆ V)
    (hθS : ∀ x ∈ S, θ.function =ᶠ[nhds x] (fun _ => (1 : ℂ)))
    (ζ : RealTest Set.univ) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (hζS : ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis i ∈ S)
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
  have ht := regional_differentiated_flux_test V S A u C F d hd hC hdiv θ hθV hθS ζ i hi h hh hζS b hb
  simp_rw [differentiatedFlux_split, scalarProduct_add_left, square_cutoff_test_pairing,
    cutoff_weight_commute, cutoff_matrix_commute] at ht
  simp only [Fin.sum_univ_three, cutVector, cutScalar] at ht
  simp only [Fin.sum_univ_three, localizedMatrixFlux, localizedResidual, localizedCutoffGradient,
    cutVector, cutScalar]
  linear_combination ht

end OQ14.Packet05RegionalScalarEnergy
#print axioms OQ14.Packet05RegionalScalarEnergy.regional_difference_energy_identity
