import Packet05ScalarDielectricFlux

/-! The weak scalar transmission equation tested with its actual localized
scalar difference quotient, including coefficient and forcing residuals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarTransmissionTest
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.WeakPower
  OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient
  OQ14.Packet05ScalarCutoffTesting OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarTransmissionCommutator OQ14.Packet05TensorCommutator
  OQ14.Packet05FlatWeight

def differentiatedFlux (A : Fin 3 → Fin 3 → Test) (C F : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) : L2Scalar :=
  mulWeight d hd (matrixField A (fun l => quotient (C l) i h) j +
    matrixResidual A C i j h hh b hb) - quotient (F j) i h

theorem differentiated_flux_test (A : Fin 3 → Fin 3 → Test) (u : L2Scalar)
    (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) 0)
    (χ : Test) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    scalarProduct (differentiatedFlux A C F d hd i 0 h hh b hb)
      (conjScalar (cutoffDerivative χ (quotient u i h) (fun j => quotient (C j) i h) 0)) +
    scalarProduct (differentiatedFlux A C F d hd i 1 h hh b hb)
      (conjScalar (cutoffDerivative χ (quotient u i h) (fun j => quotient (C j) i h) 1)) +
    scalarProduct (differentiatedFlux A C F d hd i 2 h hh b hb)
      (conjScalar (cutoffDerivative χ (quotient u i h) (fun j => quotient (C j) i h) 2)) = 0 := by
  have ht := differentiated_divergence_cutoff_test (fun j => flux A C d hd j - F j)
    0 u C hdiv hC χ i h
  have he (j : Fin 3) : quotient (flux A C d hd j - F j) i h =
      differentiatedFlux A C F d hd i j h hh b hb := by
    rw [MaxwellCurlCutoffSource.quotient_sub, dielectric_flux_quotient A C d hd i j hi h hh b hb]
    rfl
  have hz : quotient (0 : L2Scalar) i h = 0 := by
    have hq := quotient_add (0 : L2Scalar) 0 i h
    simp only [zero_add] at hq
    apply add_left_cancel (a := quotient (0 : L2Scalar) i h)
    simpa only [add_zero] using hq.symm
  have hs : scalarProduct (0 : L2Scalar) = 0 := by
    ext v
    rw [scalarProduct_integral]
    simp
  simpa only [he, hz, hs, ContinuousLinearMap.zero_apply, zero_add] using ht

end OQ14.Packet05ScalarTransmissionTest
#print axioms OQ14.Packet05ScalarTransmissionTest.differentiated_flux_test
