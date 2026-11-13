import Packet05ScalarLocalDivergence
import Packet05ScalarTransmissionTest

/-! The actual differentiated scalar-flux test with an outer-localization
source that vanishes near both translated test supports. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarLocalFluxTest
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakPower OQ14.WeakConservation OQ14.WeakEnergy OQ14.DivCurlCompact
  OQ14.MaxwellDifferenceQuotient OQ14.Packet05ScalarCutoffTesting
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarTransmissionTest
  OQ14.Packet05ScalarLocalDivergence

theorem local_differentiated_flux_test (A : Fin 3 → Fin 3 → Test) (u D : L2Scalar)
    (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) D)
    (ζ : RealTest Set.univ) (S : Set Space) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (hD : ∀ᵐ x ∂volume, x ∈ S → D x = 0)
    (hζS : ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis i ∈ S)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    ∑ j : Fin 3, scalarProduct (differentiatedFlux A C F d hd i j h hh b hb)
      (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest (quotient u i h)
        (fun k => quotient (C k) i h) j)) = 0 := by
  have ht := localized_difference_divergence_test ζ (fun j => flux A C d hd j - F j) D u C hdiv hC S i h hD hζS
  have he (j : Fin 3) : quotient (flux A C d hd j - F j) i h =
      differentiatedFlux A C F d hd i j h hh b hb := by
    rw [MaxwellCurlCutoffSource.quotient_sub, dielectric_flux_quotient A C d hd i j hi h hh b hb]
    rfl
  simpa only [Fin.sum_univ_three, he] using ht

end OQ14.Packet05ScalarLocalFluxTest
#print axioms OQ14.Packet05ScalarLocalFluxTest.local_differentiated_flux_test
