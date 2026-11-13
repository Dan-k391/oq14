import Packet05RegionalDifferenceTest
import Packet05ScalarTransmissionTest

/-! Actual scalar flux difference test on a regional chart. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05RegionalScalarFluxTest
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakPower
  OQ14.WeakConservation OQ14.WeakEnergy OQ14.DivCurlCompact OQ14.MaxwellDifferenceQuotient
  OQ14.Packet05RegionalDivergence OQ14.Packet05RegionalDifferenceTest
  OQ14.Packet05ScalarCutoffTesting OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarTransmissionTest

theorem regional_differentiated_flux_test (V S : Set Space) (A : Fin 3 → Fin 3 → Test)
    (u : L2Scalar) (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (θ : Test) (hθV : tsupport θ.function ⊆ V)
    (hθS : ∀ x ∈ S, θ.function =ᶠ[nhds x] (fun _ => (1 : ℂ)))
    (ζ : RealTest univ) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (hζS : ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x+h • basis i ∈ S)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    ∑ j : Fin 3, scalarProduct (differentiatedFlux A C F d hd i j h hh b hb)
      (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest (quotient u i h)
        (fun k => quotient (C k) i h) j)) = 0 := by
  have ht := regional_difference_divergence_test V S (fun j => flux A C d hd j-F j)
    hdiv θ hθV hθS u C hC ζ i h hζS
  have he (j : Fin 3) : quotient (flux A C d hd j-F j) i h =
      differentiatedFlux A C F d hd i j h hh b hb := by
    rw [OQ14.MaxwellCurlCutoffSource.quotient_sub, dielectric_flux_quotient A C d hd i j hi h hh b hb]
    rfl
  simpa only [he] using ht

end OQ14.Packet05RegionalScalarFluxTest
#print axioms OQ14.Packet05RegionalScalarFluxTest.regional_differentiated_flux_test
