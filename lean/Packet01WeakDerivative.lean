import WeakDerivativeIdentification
import RadialOriginSelection

/-! Local representative transport for the Packet 01 coefficient proof. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.Packet01WeakDerivative
open Complex MeasureTheory Set Filter OQ14.SmoothWeakDerivative
open scoped Topology

theorem of_complex_tests (Ω : Set ℝ) (f g : ℝ → ℂ)
    (hw : ∀ ψ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω →
      (∫ r : ℝ, deriv ψ r * f r) + (∫ r : ℝ, ψ r * g r) = 0) :
    WeakDerivative Ω f g := by
  intro η hη hc hs
  have hcast : ContDiff ℝ (⊤ : ℕ∞) (fun r => (η r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hη
  have hc' : HasCompactSupport (fun r => (η r : ℂ)) :=
    hc.comp_left (by simp : Complex.ofReal 0 = 0)
  have hs' : tsupport (fun r => (η r : ℂ)) ⊆ Ω := by
    have he : tsupport (fun r => (η r : ℂ)) = tsupport η := by
      apply congrArg closure
      ext r
      exact not_congr Complex.ofReal_eq_zero
    rwa [he]
  have hd (r : ℝ) : deriv (fun r => (η r : ℂ)) r = ((deriv η r : ℝ) : ℂ) :=
    (((hη.differentiable (by simp) r).hasDerivAt).ofReal_comp).deriv
  simpa only [hd] using hw (fun r => (η r : ℂ)) hcast hc' hs'

theorem congr_left (Ω : Set ℝ) (hΩ : MeasurableSet Ω)
    (f₁ f₂ g : ℝ → ℂ) (he : f₁ =ᵐ[volume.restrict Ω] f₂)
    (hw : WeakDerivative Ω f₁ g) : WeakDerivative Ω f₂ g := by
  intro η hη hc hs
  have he' : ∀ᵐ x : ℝ, x ∈ Ω → f₁ x = f₂ x :=
    (ae_restrict_iff' hΩ).mp he
  have htest : (∫ x : ℝ, ((deriv η x : ℝ) : ℂ) * f₁ x) =
      ∫ x : ℝ, ((deriv η x : ℝ) : ℂ) * f₂ x := by
    apply integral_congr_ae
    filter_upwards [he'] with x hx
    by_cases hmem : x ∈ Ω
    · rw [hx hmem]
    · have hz : deriv η x = 0 := by
        by_contra hne
        exact hmem (hs (support_deriv_subset hne))
      simp only [hz, Complex.ofReal_zero, zero_mul]
  rw [← htest]
  exact hw η hη hc hs

theorem regularD_continuousOn (l : ℕ) (k : ℂ) (hk : k ≠ 0) :
    ContinuousOn (RadialOriginSelection.regularD l k) (Ioi (0 : ℝ)) := by
  intro r hr
  exact (RadialOriginSelection.regularD_hasDerivAt l k hk r hr.ne').continuousAt.continuousWithinAt

theorem identify_regular_derivative (l : ℕ) (k c : ℂ) (hk : k ≠ 0)
    (f g : ℝ → ℂ)
    (he : f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun r => c * RadialOriginSelection.regular l k r))
    (hg : LocallyIntegrableOn g (Ioo (0 : ℝ) 1))
    (hw : WeakDerivative (Ioo (0 : ℝ) 1) f g) :
    g =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun r => c * RadialOriginSelection.regularD l k r) := by
  apply WeakDerivativeIdentification.classical (Ioo (0 : ℝ) 1) isOpen_Ioo
    (fun r => c * RadialOriginSelection.regular l k r)
    (fun r => c * RadialOriginSelection.regularD l k r) g
  · intro r _
    exact (RadialOriginSelection.regular_hasDerivAt l k r).const_mul c
  · exact continuousOn_const.mul ((regularD_continuousOn l k hk).mono (fun _ hr => hr.1))
  · exact hg
  · exact congr_left _ measurableSet_Ioo f _ g he hw

end OQ14.Packet01WeakDerivative
#print axioms OQ14.Packet01WeakDerivative.of_complex_tests
#print axioms OQ14.Packet01WeakDerivative.congr_left
#print axioms OQ14.Packet01WeakDerivative.regularD_continuousOn
#print axioms OQ14.Packet01WeakDerivative.identify_regular_derivative
