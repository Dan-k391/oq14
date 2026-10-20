import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Actual compact-test integration by parts on an open real set -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.OneDimensionalGreen

open MeasureTheory Filter Set Function
open scoped Topology

theorem localized_mul_continuous (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (a ψ : ℝ → ℂ) (ha : ContinuousOn a Ω) (hψ : Continuous ψ)
    (hs : tsupport ψ ⊆ Ω) : Continuous (fun x => a x*ψ x) :=
  (ha.mul hψ.continuousOn).continuous_of_tsupport_subset hΩ
    (tsupport_mul_subset_right.trans hs)

theorem localized_mul_integrable (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (a ψ : ℝ → ℂ) (ha : ContinuousOn a Ω) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    Integrable (fun x => a x*ψ x) :=
  (localized_mul_continuous Ω hΩ a ψ ha hψ hs).integrable_of_hasCompactSupport hc.mul_left

theorem test_derivative_support (ψ dψ : ℝ → ℂ)
    (hψ : ∀ x, HasDerivAt ψ (dψ x) x) : tsupport dψ ⊆ tsupport ψ := by
  have heq : dψ = deriv ψ := funext (fun x => (hψ x).deriv.symm)
  rw [heq]
  exact closure_minimal support_deriv_subset isClosed_closure

theorem localized_product_hasDerivAt (Ω : Set ℝ) (_hΩ : IsOpen Ω)
    (a da ψ dψ : ℝ → ℂ)
    (ha : ∀ x ∈ Ω, HasDerivAt a (da x) x)
    (hψ : ∀ x, HasDerivAt ψ (dψ x) x)
    (hs : tsupport ψ ⊆ Ω) (x : ℝ) :
    HasDerivAt (fun t => a t*ψ t) (da x*ψ x+a x*dψ x) x := by
  by_cases hx : x ∈ Ω
  · exact (ha x hx).mul (hψ x)
  · have hns : x ∉ tsupport ψ := fun h => hx (hs h)
    have hev : ψ =ᶠ[𝓝 x] 0 := not_mem_tsupport_iff_eventuallyEq.mp hns
    have hp : ψ x = 0 := hev.eq_of_nhds
    have hdp : dψ x = 0 := by
      have hz := hev.deriv_eq
      simpa only [(hψ x).deriv, deriv_zero] using hz
    have hprod : (fun t => a t*ψ t) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hev] with t ht
      simp [ht]
    simpa only [hp, hdp, mul_zero, add_zero] using
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hprod

theorem integral_mul_test_deriv (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (a da ψ dψ : ℝ → ℂ)
    (ha : ∀ x ∈ Ω, HasDerivAt a (da x) x)
    (hda : ContinuousOn da Ω) (hψ : ∀ x, HasDerivAt ψ (dψ x) x)
    (hdψ : Continuous dψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    (∫ x : ℝ, a x*dψ x) = -(∫ x : ℝ, da x*ψ x) := by
  have hac : ContinuousOn a Ω := fun x hx => (ha x hx).continuousAt.continuousWithinAt
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr (fun x => (hψ x).continuousAt)
  have heq : dψ = deriv ψ := funext (fun x => (hψ x).deriv.symm)
  have hdc : HasCompactSupport dψ := heq ▸ hc.deriv
  have hds : tsupport dψ ⊆ Ω := (test_derivative_support ψ dψ hψ).trans hs
  have hi₁ := localized_mul_integrable Ω hΩ da ψ hda hψc hc hs
  have hi₂ := localized_mul_integrable Ω hΩ a dψ hac hdψ hdc hds
  have hi₀ := localized_mul_integrable Ω hΩ a ψ hac hψc hc hs
  have hi := integral_eq_zero_of_hasDerivAt_of_integrable
    (localized_product_hasDerivAt Ω hΩ a da ψ dψ ha hψ hs) (hi₁.add hi₂) hi₀
  rw [integral_add hi₁ hi₂] at hi
  exact eq_neg_of_add_eq_zero_right hi

theorem integral_mul_test_second_deriv (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (a da dda ψ dψ ddψ : ℝ → ℂ)
    (ha : ∀ x ∈ Ω, HasDerivAt a (da x) x)
    (hda : ∀ x ∈ Ω, HasDerivAt da (dda x) x) (hdda : ContinuousOn dda Ω)
    (hψ : ∀ x, HasDerivAt ψ (dψ x) x)
    (hdψ : ∀ x, HasDerivAt dψ (ddψ x) x) (hddψ : Continuous ddψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    (∫ x : ℝ, a x*ddψ x) = ∫ x : ℝ, dda x*ψ x := by
  have hdac : ContinuousOn da Ω := fun x hx => (hda x hx).continuousAt.continuousWithinAt
  have hdψc : Continuous dψ := continuous_iff_continuousAt.mpr (fun x => (hdψ x).continuousAt)
  have heq : dψ = deriv ψ := funext (fun x => (hψ x).deriv.symm)
  have hdc : HasCompactSupport dψ := heq ▸ hc.deriv
  have hds : tsupport dψ ⊆ Ω := (test_derivative_support ψ dψ hψ).trans hs
  rw [integral_mul_test_deriv Ω hΩ a da dψ ddψ ha hdac hdψ hddψ hdc hds,
    integral_mul_test_deriv Ω hΩ da dda ψ dψ hda hdda hψ hdψc hc hs, neg_neg]

theorem integral_green_identity (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (a da dda b db c ψ dψ ddψ : ℝ → ℂ)
    (ha : ∀ x ∈ Ω, HasDerivAt a (da x) x)
    (hda : ∀ x ∈ Ω, HasDerivAt da (dda x) x)
    (hb : ∀ x ∈ Ω, HasDerivAt b (db x) x)
    (hdda : ContinuousOn dda Ω) (hdb : ContinuousOn db Ω) (hc : ContinuousOn c Ω)
    (hψ : ∀ x, HasDerivAt ψ (dψ x) x)
    (hdψ : ∀ x, HasDerivAt dψ (ddψ x) x) (hddψ : Continuous ddψ)
    (hcomp : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ω) :
    (∫ x : ℝ, a x*ddψ x+b x*dψ x+c x*ψ x) =
      ∫ x : ℝ, (dda x-db x+c x)*ψ x := by
  have hac : ContinuousOn a Ω := fun x hx => (ha x hx).continuousAt.continuousWithinAt
  have hbc : ContinuousOn b Ω := fun x hx => (hb x hx).continuousAt.continuousWithinAt
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr (fun x => (hψ x).continuousAt)
  have hdψc : Continuous dψ := continuous_iff_continuousAt.mpr (fun x => (hdψ x).continuousAt)
  have hdc : HasCompactSupport dψ := by
    have heq : dψ = deriv ψ := funext (fun x => (hψ x).deriv.symm)
    exact heq ▸ hcomp.deriv
  have hddc : HasCompactSupport ddψ := by
    have heq : ddψ = deriv dψ := funext (fun x => (hdψ x).deriv.symm)
    exact heq ▸ hdc.deriv
  have hds : tsupport dψ ⊆ Ω := (test_derivative_support ψ dψ hψ).trans hs
  have hdds : tsupport ddψ ⊆ Ω := (test_derivative_support dψ ddψ hdψ).trans hds
  have hia := localized_mul_integrable Ω hΩ a ddψ hac hddψ hddc hdds
  have hib := localized_mul_integrable Ω hΩ b dψ hbc hdψc hdc hds
  have hic := localized_mul_integrable Ω hΩ c ψ hc hψc hcomp hs
  have hida := localized_mul_integrable Ω hΩ dda ψ hdda hψc hcomp hs
  have hidb := localized_mul_integrable Ω hΩ db ψ hdb hψc hcomp hs
  calc
    _ = (∫ x : ℝ, a x*ddψ x)+(∫ x : ℝ, b x*dψ x)+(∫ x : ℝ, c x*ψ x) := by
      simpa only [Pi.add_apply] using (integral_add (hia.add hib) hic).trans
        (congrArg (fun z => z+(∫ x : ℝ, c x*ψ x)) (integral_add hia hib))
    _ = (∫ x : ℝ, dda x*ψ x)-(∫ x : ℝ, db x*ψ x)+(∫ x : ℝ, c x*ψ x) := by
      rw [integral_mul_test_second_deriv Ω hΩ a da dda ψ dψ ddψ ha hda hdda
        hψ hdψ hddψ hcomp hs,
        integral_mul_test_deriv Ω hΩ b db ψ dψ hb hdb hψ hdψc hcomp hs]
      rfl
    _ = _ := by
      calc
        _ = (∫ x : ℝ, dda x*ψ x-db x*ψ x)+(∫ x : ℝ, c x*ψ x) := by
          simpa only [Pi.sub_apply] using
            congrArg (fun z => z+(∫ x : ℝ, c x*ψ x)) (integral_sub hida hidb).symm
        _ = ∫ x : ℝ, dda x*ψ x-db x*ψ x+c x*ψ x := by
          simpa only [Pi.sub_apply] using (integral_add (hida.sub hidb) hic).symm
        _ = _ := integral_congr_ae (Eventually.of_forall (fun x => by ring))

theorem fundamental_lemma_continuous (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (f : ℝ → ℂ) (hf : ContinuousOn f Ω)
    (htest : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ Ω →
      (∫ x : ℝ, f x*(η x : ℂ)) = 0) : ∀ x ∈ Ω, f x = 0 := by
  have hae : ∀ᵐ x : ℝ, x ∈ Ω → f x = 0 :=
    hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn hΩ.measurableSet) (fun η hη hc hs => by
        simpa only [Complex.real_smul, mul_comm] using htest η hη hc hs)
  have hae' : f =ᵐ[volume.restrict Ω] 0 := (ae_restrict_iff' hΩ.measurableSet).mpr hae
  exact Measure.eqOn_open_of_ae_eq hae' hΩ hf continuousOn_const

theorem real_test_green_identity (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (a da dda b db c : ℝ → ℂ)
    (ha : ∀ x ∈ Ω, HasDerivAt a (da x) x)
    (hda : ∀ x ∈ Ω, HasDerivAt da (dda x) x)
    (hb : ∀ x ∈ Ω, HasDerivAt b (db x) x)
    (hdda : ContinuousOn dda Ω) (hdb : ContinuousOn db Ω) (hc : ContinuousOn c Ω)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcomp : HasCompactSupport η) (hs : tsupport η ⊆ Ω) :
    (∫ x : ℝ, a x*((deriv (deriv η) x : ℝ) : ℂ)+b x*((deriv η x : ℝ) : ℂ)+c x*(η x : ℂ)) =
      ∫ x : ℝ, (dda x-db x+c x)*(η x : ℂ) := by
  have hdη := (contDiff_infty_iff_deriv.mp hη).2
  have hddη := (contDiff_infty_iff_deriv.mp hdη).2
  have hψ : ∀ x, HasDerivAt (fun t => (η t : ℂ)) ((deriv η x : ℝ) : ℂ) x :=
    fun x => ((hη.differentiable (by simp) x).hasDerivAt).ofReal_comp
  have hdψ : ∀ x, HasDerivAt (fun t => ((deriv η t : ℝ) : ℂ)) ((deriv (deriv η) x : ℝ) : ℂ) x :=
    fun x => ((hdη.differentiable (by simp) x).hasDerivAt).ofReal_comp
  have hcs : HasCompactSupport (fun t => (η t : ℂ)) :=
    hcomp.comp_left (by simp : Complex.ofReal 0 = 0)
  have hss : tsupport (fun t => (η t : ℂ)) ⊆ Ω := by
    have heq : tsupport (fun t => (η t : ℂ)) = tsupport η := by
      apply congrArg closure
      ext x
      exact not_congr Complex.ofReal_eq_zero
    rwa [heq]
  exact integral_green_identity Ω hΩ a da dda b db c
    (fun t => (η t : ℂ)) (fun t => ((deriv η t : ℝ) : ℂ))
    (fun t => ((deriv (deriv η) t : ℝ) : ℂ)) ha hda hb hdda hdb hc hψ hdψ
    (Complex.continuous_ofReal.comp hddη.continuous) hcs hss

theorem weak_green_pointwise (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (a da dda b db c : ℝ → ℂ)
    (ha : ∀ x ∈ Ω, HasDerivAt a (da x) x)
    (hda : ∀ x ∈ Ω, HasDerivAt da (dda x) x)
    (hb : ∀ x ∈ Ω, HasDerivAt b (db x) x)
    (hdda : ContinuousOn dda Ω) (hdb : ContinuousOn db Ω) (hc : ContinuousOn c Ω)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ Ω →
      (∫ x : ℝ, a x*((deriv (deriv η) x : ℝ) : ℂ)+b x*((deriv η x : ℝ) : ℂ)+c x*(η x : ℂ)) = 0) :
    ∀ x ∈ Ω, dda x-db x+c x = 0 := by
  apply fundamental_lemma_continuous Ω hΩ (fun x => dda x-db x+c x) ((hdda.sub hdb).add hc)
  intro η hη hcomp hs
  rw [← real_test_green_identity Ω hΩ a da dda b db c ha hda hb hdda hdb hc η hη hcomp hs]
  exact hweak η hη hcomp hs

theorem weak_green_pointwise_deriv (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (a b c : ℝ → ℂ) (ha : ContDiffOn ℝ 2 a Ω) (hb : ContDiffOn ℝ 1 b Ω)
    (hc : ContinuousOn c Ω)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ Ω →
      (∫ x : ℝ, a x*((deriv (deriv η) x : ℝ) : ℂ)+b x*((deriv η x : ℝ) : ℂ)+c x*(η x : ℂ)) = 0) :
    ∀ x ∈ Ω, deriv (deriv a) x-deriv b x+c x = 0 := by
  have had : ContDiffOn ℝ 1 (deriv a) Ω := ha.deriv_of_isOpen hΩ (by norm_num)
  exact weak_green_pointwise Ω hΩ a (deriv a) (deriv (deriv a)) b (deriv b) c
    (fun x hx => ((ha.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt)
    (fun x hx => ((had.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt)
    (fun x hx => ((hb.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt)
    (had.continuousOn_deriv_of_isOpen hΩ (by norm_num))
    (hb.continuousOn_deriv_of_isOpen hΩ (by norm_num)) hc hweak

end OQ14.OneDimensionalGreen

#print axioms OQ14.OneDimensionalGreen.localized_mul_continuous
#print axioms OQ14.OneDimensionalGreen.localized_mul_integrable
#print axioms OQ14.OneDimensionalGreen.test_derivative_support
#print axioms OQ14.OneDimensionalGreen.localized_product_hasDerivAt
#print axioms OQ14.OneDimensionalGreen.integral_mul_test_deriv
#print axioms OQ14.OneDimensionalGreen.integral_mul_test_second_deriv
#print axioms OQ14.OneDimensionalGreen.integral_green_identity
#print axioms OQ14.OneDimensionalGreen.fundamental_lemma_continuous
#print axioms OQ14.OneDimensionalGreen.real_test_green_identity
#print axioms OQ14.OneDimensionalGreen.weak_green_pointwise
#print axioms OQ14.OneDimensionalGreen.weak_green_pointwise_deriv
