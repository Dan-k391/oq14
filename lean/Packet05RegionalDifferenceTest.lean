import Packet05LocalizedForcingBootstrap
import Packet05ScalarLocalDivergence
import Packet05RegionalFluxCutoff

/-! The localized difference-quotient energy test follows directly from a
regional divergence equation by a plateau cutoff on the flux alone. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RegionalDifferenceTest
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.WeakPower OQ14.WeakEnergy OQ14.DivCurlCompact OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCutoffCommutator
  OQ14.Packet05RegionalDivergence OQ14.Packet05RegionalFluxCutoff
  OQ14.Packet05ScalarLocalDivergence OQ14.Packet05ScalarCutoffTesting
  OQ14.Packet05ScalarSquareCutoff OQ14.Packet05ScalarCutoffTransfer
open scoped Topology

theorem regional_difference_divergence_test (V S : Set Space) (P : L2Vector)
    (hdiv : HasDivergenceOn V P 0) (θ : Test) (hθV : tsupport θ.function ⊆ V)
    (hθS : ∀ x ∈ S, θ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (u : L2Scalar) (G : L2Vector) (hG : ∀ i, HasWeakPartial u (G i) i)
    (ζ : RealTest Set.univ) (i : Fin 3) (h : ℝ)
    (hζS : ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x+h • basis i ∈ S) :
    ∑ j : Fin 3, scalarProduct (quotient (P j) i h)
      (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest (quotient u i h)
        (fun k => quotient (G k) i h) j)) = 0 := by
  let P' := cutFlux θ P
  let D := cutFluxSource θ P
  have hglobal : HasWeakDivergence P' D := regional_flux_cutoff_divergence V P hdiv θ hθV
  have hzero := cutoff_source_vanishes_on θ P S hθS
  have ht := localized_difference_divergence_test ζ P' D u G hglobal hG S i h hzero hζS
  have hp (j : Fin 3) : ∀ᵐ x ∂volume, ζ.function x ≠ 0 →
      quotient (P' j) i h x = quotient (P j) i h x := by
    have hc := scaleL2_ae θ.function θ.regular.continuous θ.compact (P j)
    have hct := (measurePreserving_add_right (volume : Measure Space) (h • basis i)).quasiMeasurePreserving.ae hc
    filter_upwards [quotient_ae (P' j) i h, quotient_ae (P j) i h, hc,hct] with x hq hq' hc0 hc1 hz
    obtain ⟨hx0,hx1⟩ := hζS x (subset_tsupport _ hz)
    have ht0 := (hθS x hx0).self_of_nhds
    have ht1 := (hθS (x+h • basis i) hx1).self_of_nhds
    rw [hq,hq']
    change _ * ((P' j) (x+h • basis i) - (P' j) x) = _
    change _ * (scaleL2 θ.function θ.regular.continuous θ.compact (P j) (x+h • basis i) -
      scaleL2 θ.function θ.regular.continuous θ.compact (P j) x) = _
    rw [hc0,hc1,ht0,ht1]
    simp
  have he (j : Fin 3) : scalarProduct (quotient (P' j) i h)
      (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest (quotient u i h)
        (fun k => quotient (G k) i h) j)) =
    scalarProduct (quotient (P j) i h)
      (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest (quotient u i h)
        (fun k => quotient (G k) i h) j)) := by
    rw [scalarProduct_integral,scalarProduct_integral]
    have hsq := square_cutoff_derivative ζ (quotient u i h) (fun k => quotient (G k) i h) j
    apply integral_congr_ae
    filter_upwards [hp j,conjScalar_ae (cutoffDerivative (squareTest ζ).complexTest.toTest (quotient u i h)
        (fun k => quotient (G k) i h) j),
      Lp.coeFn_add (cutScalar ζ (cutScalar ζ (quotient (G j) i h)))
        ((2 : ℂ) • cutScalar ζ (cutoffGradient ζ (quotient u i h) j)),
      cutScalar_ae ζ (cutScalar ζ (quotient (G j) i h)),
      Lp.coeFn_smul (2 : ℂ) (cutScalar ζ (cutoffGradient ζ (quotient u i h) j)),
      cutScalar_ae ζ (cutoffGradient ζ (quotient u i h) j)] with x hp hc ha hb hs hd
    by_cases hz : ζ.function x = 0
    · rw [hc,hsq,ha]
      simp only [Pi.add_apply]
      rw [hb,hs]
      simp only [Pi.smul_apply,smul_eq_mul]
      rw [hd]
      simp [hz]
    · rw [hp hz]
  simp only [Fin.sum_univ_three, ← he 0, ← he 1, ← he 2]
  exact ht

end OQ14.Packet05RegionalDifferenceTest
#print axioms OQ14.Packet05RegionalDifferenceTest.regional_difference_divergence_test
