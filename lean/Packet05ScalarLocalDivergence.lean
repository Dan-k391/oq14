import Packet05ScalarCutoffTesting
import Packet05ScalarSquareCutoff
import MaxwellCutoffCommutator

/-! A localized test does not see a divergence source supported away from
both endpoints of the difference quotient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarLocalDivergence
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakPower OQ14.WeakConservation OQ14.WeakEnergy OQ14.DivCurlCompact
  OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCutoffCommutator
  OQ14.Packet05ScalarCutoffTesting
open scoped ComplexConjugate

theorem localized_quotient_source_zero (ζ : RealTest Set.univ) (D : L2Scalar)
    (S : Set Space) (i : Fin 3) (h : ℝ)
    (hD : ∀ᵐ x ∂volume, x ∈ S → D x = 0)
    (hζS : ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis i ∈ S) :
    ∀ᵐ x ∂volume, ζ.function x ≠ 0 → quotient D i h x = 0 := by
  have ht := (measurePreserving_add_right (volume : Measure Space) (h • basis i)).quasiMeasurePreserving.ae hD
  filter_upwards [hD, ht, quotient_ae D i h] with x hd ht hq hn
  have hx : x ∈ tsupport ζ.function := subset_closure hn
  obtain ⟨hxs,hxt⟩ := hζS x hx
  rw [hq, hd hxs, ht hxt]
  simp

theorem localized_source_test_zero (ζ : RealTest Set.univ) (D w : L2Scalar)
    (S : Set Space) (i : Fin 3) (h : ℝ)
    (hD : ∀ᵐ x ∂volume, x ∈ S → D x = 0)
    (hζS : ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis i ∈ S) :
    scalarProduct (quotient D i h)
      (conjScalar (scaleL2 (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
        (squareTest ζ).complexTest.compact w)) = 0 := by
  rw [scalarProduct_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [localized_quotient_source_zero ζ D S i h hD hζS,
    conjScalar_ae (scaleL2 (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
      (squareTest ζ).complexTest.compact w),
    scaleL2_ae (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
      (squareTest ζ).complexTest.compact w] with x hz hc hs
  rw [hc,hs]
  by_cases hzero : ζ.function x = 0
  · simp [squareTest, RealTest.complexTest, hzero]
  · rw [hz hzero, zero_mul]
    rfl

theorem localized_difference_divergence_test (ζ : RealTest Set.univ)
    (E : L2Vector) (D u : L2Scalar) (G : Fin 3 → L2Scalar)
    (hdiv : HasWeakDivergence E D) (hG : ∀ i, HasWeakPartial u (G i) i)
    (S : Set Space) (i : Fin 3) (h : ℝ)
    (hD : ∀ᵐ x ∂volume, x ∈ S → D x = 0)
    (hζS : ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis i ∈ S) :
    scalarProduct (quotient (E 0) i h) (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest
      (quotient u i h) (fun j => quotient (G j) i h) 0)) +
    scalarProduct (quotient (E 1) i h) (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest
      (quotient u i h) (fun j => quotient (G j) i h) 1)) +
    scalarProduct (quotient (E 2) i h) (conjScalar (cutoffDerivative (squareTest ζ).complexTest.toTest
      (quotient u i h) (fun j => quotient (G j) i h) 2)) = 0 := by
  have ht := differentiated_divergence_cutoff_test E D u G hdiv hG (squareTest ζ).complexTest.toTest i h
  rw [localized_source_test_zero ζ D (quotient u i h) S i h hD hζS, zero_add] at ht
  exact ht

end OQ14.Packet05ScalarLocalDivergence
#print axioms OQ14.Packet05ScalarLocalDivergence.localized_quotient_source_zero
#print axioms OQ14.Packet05ScalarLocalDivergence.localized_source_test_zero
#print axioms OQ14.Packet05ScalarLocalDivergence.localized_difference_divergence_test
