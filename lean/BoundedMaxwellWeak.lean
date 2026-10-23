import DensityWeak
import MaterialMaxwell

/-! Weak Maxwell equations derived from actual globally bounded first derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BoundedMaxwellWeak
open MeasureTheory Maxwell MaterialMaxwell DynamicSource MagneticResponse
open WeakCurl (next previous)

theorem testMaxwell (k : ℝ) (E H : Field)
    (hE : ∀ x i, DifferentiableAt ℝ (fun z => E z i) x)
    (hH : ∀ x i, DifferentiableAt ℝ (fun z => H z i) x)
    (CE CH : ℝ) (hbE : ∀ x i, ‖fderiv ℝ (fun z => E z i) x‖ ≤ CE)
    (hbH : ∀ x i, ‖fderiv ℝ (fun z => H z i) x‖ ≤ CH)
    (hm : ∀ x, MaxwellAt k 1 1 E H x) : TestMaxwell k (fun _ => 1) E H := by
  have hcont (F : Field) (hd : ∀ x i, DifferentiableAt ℝ (fun z => F z i) x) (i : Fin 3) :
      Continuous (fun x => F x i) := continuous_iff_continuousAt.mpr (fun x => (hd x i).continuousAt)
  have hl (F : Field) (C : ℝ) (hb : ∀ x i, ‖fderiv ℝ (fun z => F z i) x‖ ≤ C) (a i : Fin 3) :
      LocallyIntegrable (fun x => pd F x a i) := by
    have hmeas : Measurable (fun x => pd F x a i) := measurable_fderiv_apply_const ℝ (fun x => F x i) (basis a)
    have hg : LocallyIntegrable (fun _ : Space => C) := continuous_const.locallyIntegrable
    apply hg.mono hmeas.aestronglyMeasurable
    filter_upwards with x
    have hp := (fderiv ℝ (fun z => F z i) x).le_opNorm (basis a)
    have hn : ‖basis a‖=1 := by simp [basis]
    rw [hn,mul_one] at hp
    exact (hp.trans (hb x i)).trans (by simpa only [Real.norm_eq_abs] using le_abs_self C)
  intro i f
  have he := RadialInterface.curl_integration_by_parts 1 E (hcont E hE) (fun x _ _ i => hE x i)
    (hl E CE hbE) f.val (f.val.smooth 1) f.property
  have hh := RadialInterface.curl_integration_by_parts 1 H (hcont H hH) (fun x _ _ i => hH x i)
    (hl H CH hbH) f.val (f.val.smooth 1) f.property
  have hp (F : Field) : weakCurlPairing F f.val i=curlPair (fieldPair F) i f := by
    fin_cases i <;> simp [weakCurlPairing,curlPair,fieldPair,next,previous,testPartial,GradientProjection.pderivative_apply]
  have he' := congrFun he i
  have hh' := congrFun hh i
  rw [hp] at he' hh'
  rw [← he',← hh']
  constructor
  · unfold fieldPair
    simp_rw [(hm _).1,Complex.ofReal_one,mul_one,mul_assoc,integral_const_mul]
  · simp_rw [(hm _).2,Complex.ofReal_one,mul_one,mul_assoc,integral_const_mul]
    simp only [fieldPair,Complex.ofReal_one,one_mul]
    ring

end OQ14.BoundedMaxwellWeak
#print axioms OQ14.BoundedMaxwellWeak.testMaxwell
