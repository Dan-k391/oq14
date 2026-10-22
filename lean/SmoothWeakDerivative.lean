import WeakPoynting.Representative

/-! Genuine continuous representatives using only smooth compact test functions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.SmoothWeakDerivative
open MeasureTheory Set Filter OQ14.FluxSlices OQ14.FluxRepresentative
open scoped Topology Convolution Manifold

theorem real_ae_constant (f : ℝ → ℝ) (hf : LocallyIntegrable f)
    (hz : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x, f x*deriv η x)=0) : ∃ c : ℝ, f =ᵐ[volume] (fun _ => c) := by
  have hs (φ : ContDiffBump (0 : ℝ)) (x y : ℝ) : smooth f φ x=smooth f φ y := by
    apply is_const_of_deriv_eq_zero
    · exact (φ.hasCompactSupport_normed.contDiff_convolution_right
        (ContinuousLinearMap.mul ℝ ℝ) hf (φ.contDiff_normed (n := (1 : ℕ∞)))).differentiable le_rfl
    · intro z
      have hh := hz (reflectedTest φ z).function
        (φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)) (reflectedTest φ z).compact
      simp only [reflectedTest_deriv,mul_neg,integral_neg,neg_eq_zero] at hh
      rw [smooth_deriv f hf φ z]
      exact hh
  have ha := smooth_ae_tendsto f hf
  obtain ⟨x₀,hx₀⟩ := ha.exists
  refine ⟨f x₀,?_⟩
  filter_upwards [ha] with x hx
  have he : (fun n => smooth f (shrinkingBump n) x)=(fun n => smooth f (shrinkingBump n) x₀) :=
    funext (fun n => hs _ x x₀)
  rw [he] at hx
  exact tendsto_nhds_unique hx hx₀

theorem real_representative (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x, deriv η x*f x)+(∫ x,η x*g x)=0) :
    ∃ F : ℝ → ℝ, Continuous F ∧ f =ᵐ[volume] F ∧
      ∀ a b, F b-F a=∫ x in a..b,g x := by
  have hp := primitive_continuous g hg
  have hz : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x,(f x-primitive g x)*deriv η x)=0 := by
    intro η hη hc
    let θ : LineTest univ := ⟨η,hη.of_le (by simp),hc,subset_univ _⟩
    have hd := hη.continuous_deriv (by simp)
    have hfd : Integrable (fun x => f x*deriv η x) := by
      simpa only [mul_comm] using hf.bdd_mul hd.aestronglyMeasurable
        (hd.bounded_above_of_compact_support hc.deriv)
    have hpd : Integrable (fun x => primitive g x*deriv η x) :=
      (hp.mul hd).integrable_of_hasCompactSupport hc.deriv.mul_left
    simp only [sub_mul]
    rw [integral_sub hfd hpd,primitive_test_identity g hg θ]
    simpa only [θ,mul_comm,sub_neg_eq_add] using hw η hη hc
  obtain ⟨c,hc⟩ := real_ae_constant (fun x => f x-primitive g x)
    (hf.locallyIntegrable.sub hp.locallyIntegrable) hz
  refine ⟨fun x => c+primitive g x,continuous_const.add hp,?_,?_⟩
  · filter_upwards [hc] with x hx
    linarith
  · intro a b
    rw [add_sub_add_left_eq_sub,primitive_increment g hg a b]

def WeakDerivative (Ω : Set ℝ) (f g : ℝ → ℂ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ Ω →
    (∫ x,((deriv η x : ℝ) : ℂ)*f x)+(∫ x,(η x : ℂ)*g x)=0

theorem test_product_integrable (f : ℝ → ℂ) (hf : Integrable f)
    (η : ℝ → ℝ) (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun x => (η x : ℂ)*f x) :=
  hf.bdd_mul (Complex.continuous_ofReal.comp hη).aestronglyMeasurable
    ((Complex.continuous_ofReal.comp hη).bounded_above_of_compact_support
      (hc.comp_left (g := Complex.ofReal) (by simp)))

theorem complex_representative (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (hw : WeakDerivative univ f g) :
    ∃ F : ℝ → ℂ, Continuous F ∧ f =ᵐ[volume] F ∧
      ∀ a b,F b-F a=∫ x in a..b,g x := by
  have hwr : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x,deriv η x*(f x).re)+(∫ x,η x*(g x).re)=0 := by
    intro η hη hc
    have he := congrArg Complex.re (hw η hη hc (subset_univ _))
    have h₁ := Complex.reCLM.integral_comp_comm (test_product_integrable f hf (deriv η)
      (hη.continuous_deriv (by simp)) hc.deriv)
    have h₂ := Complex.reCLM.integral_comp_comm (test_product_integrable g hg η hη.continuous hc)
    simp only [Complex.reCLM_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h₁ h₂
    rw [Complex.add_re,← h₁,← h₂] at he
    exact he
  have hwi : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ x,deriv η x*(f x).im)+(∫ x,η x*(g x).im)=0 := by
    intro η hη hc
    have he := congrArg Complex.im (hw η hη hc (subset_univ _))
    have h₁ := Complex.imCLM.integral_comp_comm (test_product_integrable f hf (deriv η)
      (hη.continuous_deriv (by simp)) hc.deriv)
    have h₂ := Complex.imCLM.integral_comp_comm (test_product_integrable g hg η hη.continuous hc)
    simp only [Complex.imCLM_apply,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] at h₁ h₂
    rw [Complex.add_im,← h₁,← h₂] at he
    exact he
  obtain ⟨Fr,hFr,her,hir⟩ := real_representative (fun x => (f x).re) (fun x => (g x).re) hf.re hg.re hwr
  obtain ⟨Fi,hFi,hei,hii⟩ := real_representative (fun x => (f x).im) (fun x => (g x).im) hf.im hg.im hwi
  refine ⟨fun x => (Fr x : ℂ)+(Fi x : ℂ)*Complex.I,
    (Complex.continuous_ofReal.comp hFr).add ((Complex.continuous_ofReal.comp hFi).mul continuous_const),?_,?_⟩
  · filter_upwards [her,hei] with x hr hi
    apply Complex.ext <;> simp [hr,hi]
  · intro a b
    apply Complex.ext
    · simpa [Complex.sub_re,hir] using (Complex.reCLM.intervalIntegral_comp_comm (hg.intervalIntegrable (a := a) (b := b)))
    · simpa [Complex.sub_im,hii] using (Complex.imCLM.intervalIntegral_comp_comm (hg.intervalIntegrable (a := a) (b := b)))

end OQ14.SmoothWeakDerivative

#print axioms OQ14.SmoothWeakDerivative.real_ae_constant
#print axioms OQ14.SmoothWeakDerivative.real_representative
#print axioms OQ14.SmoothWeakDerivative.test_product_integrable
#print axioms OQ14.SmoothWeakDerivative.complex_representative
