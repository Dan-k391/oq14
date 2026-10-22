import OneDimensionalGreen
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Actual compact-test concomitants and one-dimensional point-source jumps. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.OneDimensionalJump

open MeasureTheory Filter Set Metric OQ14.OneDimensionalGreen
open scoped Topology

theorem localized_mul_smooth (Ω : Set ℝ) (hΩ : IsOpen Ω) (a η : ℝ → ℂ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a Ω) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : tsupport η ⊆ Ω) : ContDiff ℝ (⊤ : ℕ∞) (fun r => a r*η r) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r ∈ Ω
  · exact (ha.contDiffAt (hΩ.mem_nhds hr)).mul hη.contDiffAt
  · have hn : r ∉ tsupport η := fun h => hr (hs h)
    have he : (fun t => a t*η t) =ᶠ[𝓝 r] (fun _ => (0 : ℂ)) := by
      filter_upwards [not_mem_tsupport_iff_eventuallyEq.mp hn] with t ht
      simp only [ht,Pi.zero_apply,mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he

def concomitant (a da b η : ℝ → ℂ) (r : ℝ) : ℂ :=
  a r*deriv η r+(b r-da r)*η r

theorem concomitant_smooth (Ω : Set ℝ) (hΩ : IsOpen Ω) (a da b η : ℝ → ℂ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a Ω) (hda : ContDiffOn ℝ (⊤ : ℕ∞) da Ω)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b Ω) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : tsupport η ⊆ Ω) : ContDiff ℝ (⊤ : ℕ∞) (concomitant a da b η) := by
  have hη' : ContDiff ℝ (⊤ : ℕ∞) (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  exact (localized_mul_smooth Ω hΩ a (deriv η) ha hη' ((test_derivative_support η (deriv η) (fun r => (hη.differentiable (by simp) r).hasDerivAt)).trans hs)).add
    (localized_mul_smooth Ω hΩ (fun r => b r-da r) η (hb.sub hda) hη hs)

theorem concomitant_compact (a da b η : ℝ → ℂ) (hc : HasCompactSupport η) :
    HasCompactSupport (concomitant a da b η) := hc.deriv.mul_left.add hc.mul_left

theorem concomitant_hasDerivAt (Ω : Set ℝ) (hΩ : IsOpen Ω) (a da dda b db η : ℝ → ℂ)
    (ha : ∀ r ∈ Ω,HasDerivAt a (da r) r) (hda : ∀ r ∈ Ω,HasDerivAt da (dda r) r)
    (hb : ∀ r ∈ Ω,HasDerivAt b (db r) r) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : tsupport η ⊆ Ω) (r : ℝ) :
    HasDerivAt (concomitant a da b η)
      (a r*deriv (deriv η) r+b r*deriv η r+(db r-dda r)*η r) r := by
  have hη' : ContDiff ℝ (⊤ : ℕ∞) (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have hd1 := localized_product_hasDerivAt Ω hΩ a da (deriv η) (deriv (deriv η)) ha
    (fun r => (hη'.differentiable (by simp) r).hasDerivAt) ((test_derivative_support η (deriv η) (fun r => (hη.differentiable (by simp) r).hasDerivAt)).trans hs) r
  have hd2 := localized_product_hasDerivAt Ω hΩ (fun r => b r-da r) (fun r => db r-dda r)
    η (deriv η) (fun r hr => (hb r hr).sub (hda r hr))
    (fun r => (hη.differentiable (by simp) r).hasDerivAt) hs r
  convert hd1.add hd2 using 1
  ring

theorem integral_piecewise_deriv (f g : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (s : ℝ) :
    (∫ r : ℝ,if r ≤ s then deriv f r else deriv g r)=f s-g s := by
  have hfi : Integrable (deriv f) (volume : Measure ℝ) := (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hfc.deriv
  have hgi : Integrable (deriv g) (volume : Measure ℝ) := (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hgc.deriv
  change (∫ r : ℝ,(Iic s).piecewise (deriv f) (deriv g) r)=_
  rw [integral_piecewise measurableSet_Iic hfi.integrableOn hgi.integrableOn,compl_Iic,
    HasCompactSupport.integral_Iic_deriv_eq hf hfc s,HasCompactSupport.integral_Ioi_deriv_eq hg hgc s]
  ring

theorem integral_concomitant_jump (Ω : Set ℝ) (hΩ : IsOpen Ω)
    (am dam ddam bm dbm ap dap ddap bp dbp η : ℝ → ℂ)
    (ham : ContDiffOn ℝ (⊤ : ℕ∞) am Ω) (hdam : ContDiffOn ℝ (⊤ : ℕ∞) dam Ω)
    (hbm : ContDiffOn ℝ (⊤ : ℕ∞) bm Ω)
    (hap : ContDiffOn ℝ (⊤ : ℕ∞) ap Ω) (hdap : ContDiffOn ℝ (⊤ : ℕ∞) dap Ω)
    (hbp : ContDiffOn ℝ (⊤ : ℕ∞) bp Ω)
    (hadm : ∀ r ∈ Ω,HasDerivAt am (dam r) r)
    (haddm : ∀ r ∈ Ω,HasDerivAt dam (ddam r) r)
    (hbdm : ∀ r ∈ Ω,HasDerivAt bm (dbm r) r)
    (hadp : ∀ r ∈ Ω,HasDerivAt ap (dap r) r)
    (haddp : ∀ r ∈ Ω,HasDerivAt dap (ddap r) r)
    (hbdp : ∀ r ∈ Ω,HasDerivAt bp (dbp r) r)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ω) (s : ℝ) :
    (∫ r : ℝ,if r ≤ s then am r*deriv (deriv η) r+bm r*deriv η r+(dbm r-ddam r)*η r
      else ap r*deriv (deriv η) r+bp r*deriv η r+(dbp r-ddap r)*η r)=
      (am s-ap s)*deriv η s+((bm s-dam s)-(bp s-dap s))*η s := by
  have hm := concomitant_smooth Ω hΩ am dam bm η ham hdam hbm hη hs
  have hp := concomitant_smooth Ω hΩ ap dap bp η hap hdap hbp hη hs
  have heqm (r : ℝ) : deriv (concomitant am dam bm η) r=
      am r*deriv (deriv η) r+bm r*deriv η r+(dbm r-ddam r)*η r :=
    (concomitant_hasDerivAt Ω hΩ am dam ddam bm dbm η hadm haddm hbdm hη hs r).deriv
  have heqp (r : ℝ) : deriv (concomitant ap dap bp η) r=
      ap r*deriv (deriv η) r+bp r*deriv η r+(dbp r-ddap r)*η r :=
    (concomitant_hasDerivAt Ω hΩ ap dap ddap bp dbp η hadp haddp hbdp hη hs r).deriv
  simp_rw [← heqm,← heqp]
  rw [integral_piecewise_deriv _ _ (hm.of_le (by simp)) (hp.of_le (by simp))
    (concomitant_compact am dam bm η hc) (concomitant_compact ap dap bp η hc) s]
  unfold concomitant
  ring

theorem compact_test_jets (s : ℝ) (hs : 0 < s) (A B : ℂ) :
    ∃ η : ℝ → ℂ,ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioi (0 : ℝ) ∧ η s=A ∧ deriv η s=B := by
  let β : ContDiffBump s := ⟨s/4,s/2,by positivity,by linarith⟩
  let η : ℝ → ℂ := fun r => (β r : ℂ)*(A+B*((r : ℂ)-(s : ℂ)))
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun r => (β r : ℂ)) := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := hβ.mul
    (contDiff_const.add (contDiff_const.mul (Complex.ofRealCLM.contDiff.sub contDiff_const)))
  have hcβ : HasCompactSupport (fun r => (β r : ℂ)) := β.hasCompactSupport.comp_left (by simp : Complex.ofReal 0=0)
  have hsupport : tsupport (fun r => (β r : ℂ))=tsupport β := by
    apply congrArg closure
    ext r
    exact not_congr Complex.ofReal_eq_zero
  have hsub : tsupport η ⊆ Ioi (0 : ℝ) := by
    intro r hr
    have hrβ := (show tsupport η ⊆ tsupport (fun r => (β r : ℂ)) from tsupport_mul_subset_left) hr
    rw [hsupport,β.tsupport_eq] at hrβ
    change dist r s ≤ s/2 at hrβ
    rw [Real.dist_eq] at hrβ
    change 0 < r
    linarith [neg_abs_le (r-s)]
  have he : η =ᶠ[𝓝 s] fun r : ℝ => A+B*((r : ℂ)-(s : ℂ)) := by
    filter_upwards [β.eventuallyEq_one] with r hr
    simp [η,hr]
  have hv : η s=A := by simpa only [sub_self,mul_zero,add_zero] using he.eq_of_nhds
  have hd0 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hd : HasDerivAt η B s := by
    simpa only [mul_one] using (((hd0.sub_const (s : ℂ)).const_mul B).const_add A).congr_of_eventuallyEq he
  exact ⟨η,hη,hcβ.mul_right,hsub,hv,hd.deriv⟩

theorem test_jet_separation (s : ℝ) (hs : 0 < s) (A B C : ℂ)
    (h : ∀ η : ℝ → ℂ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioi (0 : ℝ) → A*deriv η s+B*η s=C*η s) : A=0 ∧ B=C := by
  obtain ⟨η₀,hη₀,hc₀,hs₀,hv₀,hd₀⟩ := compact_test_jets s hs 0 1
  obtain ⟨η₁,hη₁,hc₁,hs₁,hv₁,hd₁⟩ := compact_test_jets s hs 1 0
  have h₀ := h η₀ hη₀ hc₀ hs₀
  have h₁ := h η₁ hη₁ hc₁ hs₁
  simp only [hv₀,hd₀,mul_one,mul_zero,add_zero] at h₀
  simp only [hv₁,hd₁,mul_one,mul_zero,zero_add] at h₁
  exact ⟨h₀,h₁⟩

theorem point_source_jump (s : ℝ) (hs : 0 < s) (S : ℂ)
    (am dam ddam bm dbm ap dap ddap bp dbp : ℝ → ℂ)
    (ham : ContDiffOn ℝ (⊤ : ℕ∞) am (Ioi 0)) (hdam : ContDiffOn ℝ (⊤ : ℕ∞) dam (Ioi 0))
    (hbm : ContDiffOn ℝ (⊤ : ℕ∞) bm (Ioi 0))
    (hap : ContDiffOn ℝ (⊤ : ℕ∞) ap (Ioi 0)) (hdap : ContDiffOn ℝ (⊤ : ℕ∞) dap (Ioi 0))
    (hbp : ContDiffOn ℝ (⊤ : ℕ∞) bp (Ioi 0))
    (hadm : ∀ r ∈ Ioi 0,HasDerivAt am (dam r) r)
    (haddm : ∀ r ∈ Ioi 0,HasDerivAt dam (ddam r) r)
    (hbdm : ∀ r ∈ Ioi 0,HasDerivAt bm (dbm r) r)
    (hadp : ∀ r ∈ Ioi 0,HasDerivAt ap (dap r) r)
    (haddp : ∀ r ∈ Ioi 0,HasDerivAt dap (ddap r) r)
    (hbdp : ∀ r ∈ Ioi 0,HasDerivAt bp (dbp r) r)
    (hweak : ∀ η : ℝ → ℂ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioi (0 : ℝ) →
      (∫ r : ℝ,if r ≤ s then am r*deriv (deriv η) r+bm r*deriv η r+(dbm r-ddam r)*η r
        else ap r*deriv (deriv η) r+bp r*deriv η r+(dbp r-ddap r)*η r)= -S*η s) :
    ap s=am s ∧ bp s-dap s=bm s-dam s+S := by
  have hbal (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
      (hsub : tsupport η ⊆ Ioi (0 : ℝ)) :
      (am s-ap s)*deriv η s+((bm s-dam s)-(bp s-dap s))*η s= -S*η s := by
    exact (integral_concomitant_jump (Ioi 0) isOpen_Ioi am dam ddam bm dbm ap dap ddap bp dbp η
      ham hdam hbm hap hdap hbp hadm haddm hbdm hadp haddp hbdp hη hc hsub s).symm.trans
      (hweak η hη hc hsub)
  obtain ⟨ha,hb⟩ := test_jet_separation s hs (am s-ap s) ((bm s-dam s)-(bp s-dap s)) (-S) hbal
  refine ⟨(sub_eq_zero.mp ha).symm,?_⟩
  linear_combination -hb

end OQ14.OneDimensionalJump

#print axioms OQ14.OneDimensionalJump.localized_mul_smooth
#print axioms OQ14.OneDimensionalJump.concomitant_smooth
#print axioms OQ14.OneDimensionalJump.concomitant_compact
#print axioms OQ14.OneDimensionalJump.concomitant_hasDerivAt
#print axioms OQ14.OneDimensionalJump.integral_piecewise_deriv
#print axioms OQ14.OneDimensionalJump.integral_concomitant_jump
#print axioms OQ14.OneDimensionalJump.compact_test_jets
#print axioms OQ14.OneDimensionalJump.test_jet_separation
#print axioms OQ14.OneDimensionalJump.point_source_jump
