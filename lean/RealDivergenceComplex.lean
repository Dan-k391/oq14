import WeakDivergenceGraph
import ConicalComplexTests

/-! Real distributional divergence genuinely extends to complex L2 test graphs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.RealDivergenceComplex
open MeasureTheory Set Metric Filter OQ14.Maxwell
open scoped Topology

theorem of_real_tests (F : Fin 3 → Space → ℝ) (Q : Space → ℝ)
    (hF : ∀ i, MemLp (F i) 2 (volume : Measure Space)) (hQ : MemLp Q 2 (volume : Measure Space))
    (hreal : ∀ (ψ : Space → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x : Space, Q x*ψ x)+(∑ i : Fin 3, ∫ x : Space, F i x*fderiv ℝ ψ x (basis i))=0) :
    DivCurlCompact.HasWeakDivergence
      (fun i => ((hF i).ofReal).toLp (fun x => (F i x : ℂ)))
      (hQ.ofReal.toLp (fun x => (Q x : ℂ))) := by
  intro ψ
  simp only [WeakCurl.valuePair,WeakCurl.derivativePair,WeakCurl.testPair_integral]
  have hq : (∫ x : Space, hQ.ofReal.toLp (fun x => (Q x : ℂ)) x*ψ.function x)=
      ∫ x : Space, (Q x : ℂ)*ψ.function x := by
    apply integral_congr_ae
    filter_upwards [(hQ.ofReal : MemLp (fun x => (Q x : ℂ)) 2 volume).coeFn_toLp] with x hx
    exact congrArg (fun z : ℂ => z*ψ.function x) hx
  have hf (i : Fin 3) : (∫ x : Space, ((hF i).ofReal).toLp (fun x => (F i x : ℂ)) x*dcoord ψ.function x i)=
      ∫ x : Space, (F i x : ℂ)*dcoord ψ.function x i := by
    apply integral_congr_ae
    filter_upwards [((hF i).ofReal : MemLp (fun x => (F i x : ℂ)) 2 volume).coeFn_toLp] with x hx
    exact congrArg (fun z : ℂ => z*dcoord ψ.function x i) hx
  rw [hq,hf 0,hf 1,hf 2]
  have hiQ : Integrable (fun x : Space => (Q x : ℂ)*ψ.function x) := by
    simpa only [Complex.real_smul] using (hQ.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      ψ.regular.continuous ψ.compact
  have hiF (i : Fin 3) : Integrable (fun x : Space => (F i x : ℂ)*dcoord ψ.function x i) := by
    simpa only [Complex.real_smul,dcoord] using ((hF i).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      ((ψ.regular.continuous_fderiv le_rfl).clm_apply continuous_const) (ψ.compact.fderiv_apply ℝ (basis i))
  have hReFD (x v : Space) : fderiv ℝ (fun y => (ψ.function y).re) x v=(fderiv ℝ ψ.function x v).re :=
    ConicalComplexTests.projection_fderiv Complex.reCLM ψ.function (ψ.regular.differentiable le_rfl) x v
  have hImFD (x v : Space) : fderiv ℝ (fun y => (ψ.function y).im) x v=(fderiv ℝ ψ.function x v).im :=
    ConicalComplexTests.projection_fderiv Complex.imCLM ψ.function (ψ.regular.differentiable le_rfl) x v
  have hre := hreal (fun x => (ψ.function x).re) (Complex.reCLM.contDiff.comp ψ.regular)
    (ψ.compact.comp_left (g := Complex.re) rfl)
  have him := hreal (fun x => (ψ.function x).im) (Complex.imCLM.contDiff.comp ψ.regular)
    (ψ.compact.comp_left (g := Complex.im) rfl)
  simp_rw [hReFD] at hre
  simp_rw [hImFD] at him
  have hRe (g : Space → ℂ) (hg : Integrable g) : (∫ x : Space, g x).re=∫ x : Space, (g x).re := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hg).symm
  have hIm (g : Space → ℂ) (hg : Integrable g) : (∫ x : Space, g x).im=∫ x : Space, (g x).im := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hg).symm
  apply Complex.ext
  · simp only [Complex.add_re,Complex.zero_re]
    rw [hRe _ hiQ,hRe _ (hiF 0),hRe _ (hiF 1),hRe _ (hiF 2)]
    simpa only [Fin.sum_univ_three,dcoord,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,add_assoc] using hre
  · simp only [Complex.add_im,Complex.zero_im]
    rw [hIm _ hiQ,hIm _ (hiF 0),hIm _ (hiF 1),hIm _ (hiF 2)]
    simpa only [Fin.sum_univ_three,dcoord,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,add_assoc] using him

end OQ14.RealDivergenceComplex

#print axioms OQ14.RealDivergenceComplex.of_real_tests
