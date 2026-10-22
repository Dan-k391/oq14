import SmoothWeakDerivative

/-! Actual local representatives from locally integrable complex weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.SmoothLocalRepresentative
open MeasureTheory Set Filter OQ14.SmoothWeakDerivative
open scoped Topology Manifold

theorem exists_cutoff {Ω K : Set ℝ} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ κ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ Ω ∧
      ∀ x ∈ K,κ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨V,hV,hKV,hVΩ,hcV⟩ := exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨f,hf1,hf0,_⟩ := exists_smooth_one_nhds_of_subset_interior
    (𝓘(ℝ,ℝ)) (t := V) hK.isClosed (by simpa [hV.interior_eq] using hKV)
  have hs : Function.support f ⊆ V := by
    intro x hx
    by_contra hn
    exact hx (hf0 x hn)
  have ht : tsupport f ⊆ closure V := closure_mono hs
  refine ⟨f,f.contMDiff.contDiff,hcV.of_isClosed_subset isClosed_closure ht,ht.trans hVΩ,?_⟩
  intro x hx
  exact hf1.filter_mono (nhds_le_nhdsSet hx)

theorem cutoff_integrable (Ω : Set ℝ) (f : ℝ → ℂ) (hf : LocallyIntegrableOn f Ω)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hc : HasCompactSupport κ) (hs : tsupport κ ⊆ Ω) :
    Integrable (fun x => (κ x : ℂ)*f x) := by
  have hi := (hf.integrableOn_compact_subset hs hc).bdd_mul
    (Complex.continuous_ofReal.comp hκ).aestronglyMeasurable.restrict
    ((Complex.continuous_ofReal.comp hκ).bounded_above_of_compact_support
      (hc.comp_left (g := Complex.ofReal) (by simp)))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  apply subset_tsupport κ
  intro hz
  exact hx (by simp [hz])

theorem cutoff_weak_derivative (Ω : Set ℝ) (f g : ℝ → ℂ)
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω) (hw : WeakDerivative Ω f g)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ) (hs : tsupport κ ⊆ Ω) :
    WeakDerivative univ (fun x => (κ x : ℂ)*f x)
      (fun x => (κ x : ℂ)*g x+((deriv κ x : ℝ) : ℂ)*f x) := by
  have hfκ := cutoff_integrable Ω f hf κ hκ.continuous hc hs
  have hgκ := cutoff_integrable Ω g hg κ hκ.continuous hc hs
  have hfd := cutoff_integrable Ω f hf (deriv κ) (hκ.continuous_deriv (by simp)) hc.deriv
    ((closure_mono support_deriv_subset).trans (by simpa only [(isClosed_tsupport κ).closure_eq] using hs))
  intro η hη hηc _
  have he := hw (fun x => κ x*η x) (hκ.mul hη) (hc.mul_right) (tsupport_mul_subset_left.trans hs)
  have h₁ := test_product_integrable _ hfκ (deriv η) (hη.continuous_deriv (by simp)) hηc.deriv
  have h₂ := test_product_integrable _ hgκ η hη.continuous hηc
  have h₃ := test_product_integrable _ hfd η hη.continuous hηc
  have hfirst : (fun x => ((deriv (fun y => κ y*η y) x : ℝ) : ℂ)*f x)=
      (fun x => (η x : ℂ)*((deriv κ x : ℝ) : ℂ)*f x)+
      (fun x => ((deriv η x : ℝ) : ℂ)*((κ x : ℂ)*f x)) := by
    funext x
    simp only [Pi.add_apply]
    rw [deriv_mul (hκ.differentiable (by simp) x) (hη.differentiable (by simp) x)]
    push_cast
    ring
  have h₃' : Integrable (fun x => (η x : ℂ)*((deriv κ x : ℝ) : ℂ)*f x) := by
    simpa only [mul_assoc] using h₃
  rw [hfirst] at he
  change (∫ x,(η x : ℂ)*((deriv κ x : ℝ) : ℂ)*f x+
    ((deriv η x : ℝ) : ℂ)*((κ x : ℂ)*f x))+
    (∫ x,((κ x*η x : ℝ) : ℂ)*g x)=0 at he
  rw [integral_add h₃' h₁] at he
  have hsecond : (fun x => ((κ x*η x : ℝ) : ℂ)*g x)=
      fun x => (η x : ℂ)*((κ x : ℂ)*g x) := by funext x; push_cast; ring
  rw [hsecond] at he
  simp only [mul_add]
  rw [integral_add h₂ h₃]
  have he₃ : (∫ x,(η x : ℂ)*((deriv κ x : ℝ) : ℂ)*f x)=
      ∫ x,(η x : ℂ)*(((deriv κ x : ℝ) : ℂ)*f x) := by simp only [mul_assoc]
  rw [he₃] at he
  linear_combination he

theorem local_representative {Ω : Set ℝ} (hΩ : IsOpen Ω) (f g : ℝ → ℂ)
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω) (hw : WeakDerivative Ω f g)
    {a b : ℝ} (hab : Icc a b ⊆ Ω) :
    ∃ F : ℝ → ℂ, Continuous F ∧ f =ᵐ[volume.restrict (Icc a b)] F ∧
      ∀ c ∈ Icc a b,∀ d ∈ Icc a b,F d-F c=∫ x in c..d,g x := by
  obtain ⟨κ,hκ,hc,hs,h1⟩ := exists_cutoff hΩ isCompact_Icc hab
  have hfκ := cutoff_integrable Ω f hf κ hκ.continuous hc hs
  have hgκ := cutoff_integrable Ω g hg κ hκ.continuous hc hs
  have hfd := cutoff_integrable Ω f hf (deriv κ) (hκ.continuous_deriv (by simp)) hc.deriv
    ((closure_mono support_deriv_subset).trans (by simpa only [(isClosed_tsupport κ).closure_eq] using hs))
  obtain ⟨F,hF,hae,hinc⟩ := complex_representative _ _ hfκ (hgκ.add hfd)
    (cutoff_weak_derivative Ω f g hf hg hw κ hκ hc hs)
  refine ⟨F,hF,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hae,ae_restrict_mem measurableSet_Icc] with x hx hm
    simpa only [(h1 x hm).eq_of_nhds,Complex.ofReal_one,one_mul] using hx
  · intro c hc d hd
    rw [hinc]
    apply intervalIntegral.integral_congr
    intro x hx
    have he := h1 x (uIcc_subset_Icc hc hd hx)
    have hder : deriv κ x=0 := by simpa using he.deriv_eq
    simp only [Pi.add_apply]
    rw [he.eq_of_nhds,hder]
    simp

end OQ14.SmoothLocalRepresentative

#print axioms OQ14.SmoothLocalRepresentative.exists_cutoff
#print axioms OQ14.SmoothLocalRepresentative.cutoff_integrable
#print axioms OQ14.SmoothLocalRepresentative.cutoff_weak_derivative
#print axioms OQ14.SmoothLocalRepresentative.local_representative
