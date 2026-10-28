import SmoothLocalRepresentative
import OneDimensionalGreen

/-! Identifying a locally integrable weak derivative with an actual classical derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.WeakDerivativeIdentification
open MeasureTheory Set OQ14.SmoothWeakDerivative OQ14.OneDimensionalGreen

theorem classical (Ω : Set ℝ) (hΩ : IsOpen Ω) (f df g : ℝ → ℂ)
    (hf : ∀ x ∈ Ω, HasDerivAt f (df x) x) (hdf : ContinuousOn df Ω)
    (hg : LocallyIntegrableOn g Ω) (hw : WeakDerivative Ω f g) :
    g =ᵐ[volume.restrict Ω] df := by
  have hdfi : LocallyIntegrableOn df Ω := hdf.locallyIntegrableOn hΩ.measurableSet
  have ha : ∀ᵐ x : ℝ, x ∈ Ω → g x - df x = 0 :=
    hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg.sub hdfi) (by
      intro η hη hc hs
      have hψ (x : ℝ) : HasDerivAt (fun t => (η t : ℂ)) ((deriv η x : ℝ) : ℂ) x :=
        ((hη.differentiable (by simp) x).hasDerivAt).ofReal_comp
      have hcs : HasCompactSupport (fun t => (η t : ℂ)) :=
        hc.comp_left (by simp : Complex.ofReal 0 = 0)
      have hss : tsupport (fun t => (η t : ℂ)) ⊆ Ω := by
        have heq : tsupport (fun t => (η t : ℂ)) = tsupport η := by
          apply congrArg closure
          ext x
          exact not_congr Complex.ofReal_eq_zero
        rwa [heq]
      have hp := integral_mul_test_deriv Ω hΩ f df (fun t => (η t : ℂ))
        (fun t => ((deriv η t : ℝ) : ℂ)) hf hdf hψ
        (Complex.continuous_ofReal.comp (hη.continuous_deriv (by simp))) hcs hss
      have hp' : (∫ x, ((deriv η x : ℝ) : ℂ) * f x) = -(∫ x, (η x : ℂ) * df x) := by
        simpa only [mul_comm] using hp
      have h := hw η hη hc hs
      rw [hp'] at h
      have hi1 := SmoothLocalRepresentative.cutoff_integrable Ω g hg η hη.continuous hc hs
      have hi2 := SmoothLocalRepresentative.cutoff_integrable Ω df hdfi η hη.continuous hc hs
      simp only [Complex.real_smul, mul_sub]
      rw [integral_sub hi1 hi2]
      linear_combination h)
  filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mpr ha] with x hx
  exact sub_eq_zero.mp hx

end OQ14.WeakDerivativeIdentification
#print axioms OQ14.WeakDerivativeIdentification.classical
