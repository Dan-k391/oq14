import ConicalStaticField

/-! Actual complex-valued tests for the real conical static field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.ConicalComplexTests
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalCapField
open scoped Topology

def complexElectric (ν a t : ℝ) : Field := fun x i => (electric ν a t x i : ℂ)

theorem projection_fderiv (L : ℂ →L[ℝ] ℝ) (ψ : Space → ℂ) (hψ : Differentiable ℝ ψ)
    (x v : Space) : fderiv ℝ (fun y => L (ψ y)) x v = L (fderiv ℝ ψ x v) := by
  have h := L.hasFDerivAt.comp x ((hψ x).hasFDerivAt)
  change HasFDerivAt (fun y => L (ψ y)) _ x at h
  rw [h.fderiv,ContinuousLinearMap.comp_apply]

theorem weak_partial (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) (ψ : Space → ℂ)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, (potential ν a t x : ℂ)*dcoord ψ x i) =
      -(∫ x : Space, complexElectric ν a t x i*ψ x) := by
  have hiL : Integrable (fun x : Space => (potential ν a t x : ℂ)*dcoord ψ x i) := by
    simpa only [Complex.real_smul,dcoord] using
      (ConicalSpatialTests.potential_locallyIntegrable ν a t hν.le ha ht ht1).integrable_smul_right_of_hasCompactSupport
        ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const) (hc.fderiv_apply ℝ (basis i))
  have hiR : Integrable (fun x : Space => complexElectric ν a t x i*ψ x) := by
    simpa only [Complex.real_smul,complexElectric] using
      (ConicalSpatialTests.electric_component_locallyIntegrable ν a t hν.le ha ht ht1 i).integrable_smul_right_of_hasCompactSupport
        hψ.continuous hc
  have hre := ConicalWeakGradient.weak_partial ν a t hν ha ht ht1 i
    (fun x => (ψ x).re) (Complex.reCLM.contDiff.comp hψ) (hc.comp_left (g := Complex.re) rfl)
  have him := ConicalWeakGradient.weak_partial ν a t hν ha ht ht1 i
    (fun x => (ψ x).im) (Complex.imCLM.contDiff.comp hψ) (hc.comp_left (g := Complex.im) rfl)
  have hReFD (x v : Space) : fderiv ℝ (fun y => (ψ y).re) x v = (fderiv ℝ ψ x v).re :=
    projection_fderiv Complex.reCLM ψ (hψ.differentiable le_rfl) x v
  have hImFD (x v : Space) : fderiv ℝ (fun y => (ψ y).im) x v = (fderiv ℝ ψ x v).im :=
    projection_fderiv Complex.imCLM ψ (hψ.differentiable le_rfl) x v
  simp_rw [hReFD] at hre
  simp_rw [hImFD] at him
  have hLre := integral_re hiL
  have hRre := integral_re hiR
  have hLim := integral_im hiL
  have hRim := integral_im hiR
  simp only [RCLike.re_eq_complex_re,RCLike.im_eq_complex_im] at hLre hRre hLim hRim
  apply Complex.ext
  · rw [Complex.neg_re,← hLre,← hRre]
    simpa only [complexElectric,dcoord,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] using hre
  · rw [Complex.neg_im,← hLim,← hRim]
    simpa only [complexElectric,dcoord,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero] using him

theorem weak_cross_pair (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (ψ : Space → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (i j : Fin 3) :
    (∫ x : Space, complexElectric ν a t x i*dcoord ψ x j) =
      ∫ x : Space, complexElectric ν a t x j*dcoord ψ x i := by
  have hp (j : Fin 3) : ContDiff ℝ 1 (fun x => dcoord ψ x j) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ ψ) :=
      (contDiff_succ_iff_fderiv (n := 1)).mp hψ |>.2.2
    exact hd.clm_apply contDiff_const
  have hi := weak_partial ν a t hν ha ht ht1 i (fun x => dcoord ψ x j) (hp j) (hc.fderiv_apply ℝ (basis j))
  have hj := weak_partial ν a t hν ha ht ht1 j (fun x => dcoord ψ x i) (hp i) (hc.fderiv_apply ℝ (basis i))
  have he : (∫ x : Space, (potential ν a t x : ℂ)*dcoord (fun y => dcoord ψ y j) x i) =
      ∫ x : Space, (potential ν a t x : ℂ)*dcoord (fun y => dcoord ψ y i) x j := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Maxwell.partial_comm hψ x i j]
  exact neg_injective (hi.symm.trans (he.trans hj))

theorem weak_curl_zero (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (ψ : Space → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) : Maxwell.weakCurlPairing (complexElectric ν a t) ψ = 0 := by
  ext i
  fin_cases i
  · change (∫ x, complexElectric ν a t x 1*dcoord ψ x 2)-
        (∫ x, complexElectric ν a t x 2*dcoord ψ x 1) = 0
    rw [weak_cross_pair ν a t hν ha ht ht1 ψ hψ hc 1 2,sub_self]
  · change (∫ x, complexElectric ν a t x 2*dcoord ψ x 0)-
        (∫ x, complexElectric ν a t x 0*dcoord ψ x 2) = 0
    rw [weak_cross_pair ν a t hν ha ht ht1 ψ hψ hc 2 0,sub_self]
  · change (∫ x, complexElectric ν a t x 0*dcoord ψ x 1)-
        (∫ x, complexElectric ν a t x 1*dcoord ψ x 0) = 0
    rw [weak_cross_pair ν a t hν ha ht ht1 ψ hψ hc 0 1,sub_self]

theorem electric_test_integrable (ν a d t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (ψ : Space → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun x : Space => (permittivity d t x : ℂ)*fderiv ℝ ψ x (electric ν a t x)) := by
  have hi (L : ℂ →L[ℝ] ℝ) : Integrable (fun x : Space => permittivity d t x*
      fderiv ℝ (fun y => L (ψ y)) x (electric ν a t x)) :=
    ConicalStaticDivergence.electric_test_integrable ν a d t hν ha ht ht1 _
      (L.contDiff.comp hψ) (hc.comp_left (g := L) (map_zero L))
  have hReFD (x v : Space) : fderiv ℝ (fun y => (ψ y).re) x v = (fderiv ℝ ψ x v).re :=
    projection_fderiv Complex.reCLM ψ (hψ.differentiable le_rfl) x v
  have hImFD (x v : Space) : fderiv ℝ (fun y => (ψ y).im) x v = (fderiv ℝ ψ x v).im :=
    projection_fderiv Complex.imCLM ψ (hψ.differentiable le_rfl) x v
  have hire := hi Complex.reCLM
  have hiim := hi Complex.imCLM
  change Integrable (fun x => permittivity d t x*fderiv ℝ (fun y => (ψ y).re) x (electric ν a t x)) at hire
  change Integrable (fun x => permittivity d t x*fderiv ℝ (fun y => (ψ y).im) x (electric ν a t x)) at hiim
  simp_rw [hReFD] at hire
  simp_rw [hImFD] at hiim
  apply Integrable.re_im_iff.mp
  constructor
  · simpa only [RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,projection_fderiv _ ψ (hψ.differentiable le_rfl),Complex.reCLM_apply] using hire
  · simpa only [RCLike.im_eq_complex_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,projection_fderiv _ ψ (hψ.differentiable le_rfl),Complex.imCLM_apply] using hiim

theorem weak_divergence (ν a d t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (heq : ν*(ν+1) = a) (ψ : Space → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    (∫ x : Space, (permittivity d t x : ℂ)*fderiv ℝ ψ x (electric ν a t x)) = 0 := by
  have hi := electric_test_integrable ν a d t hν.le ha ht ht1 ψ hψ hc
  have hReFD (x v : Space) : fderiv ℝ (fun y => (ψ y).re) x v = (fderiv ℝ ψ x v).re :=
    projection_fderiv Complex.reCLM ψ (hψ.differentiable le_rfl) x v
  have hImFD (x v : Space) : fderiv ℝ (fun y => (ψ y).im) x v = (fderiv ℝ ψ x v).im :=
    projection_fderiv Complex.imCLM ψ (hψ.differentiable le_rfl) x v
  have hre := ConicalStaticDivergence.weak_divergence ν a d t hν ha ht ht1 hroot heq
    (fun x => (ψ x).re) (Complex.reCLM.contDiff.comp hψ) (hc.comp_left (g := Complex.re) rfl)
  have him := ConicalStaticDivergence.weak_divergence ν a d t hν ha ht ht1 hroot heq
    (fun x => (ψ x).im) (Complex.imCLM.contDiff.comp hψ) (hc.comp_left (g := Complex.im) rfl)
  simp_rw [hReFD] at hre
  simp_rw [hImFD] at him
  have hire := integral_re hi
  have hiim := integral_im hi
  simp only [RCLike.re_eq_complex_re,RCLike.im_eq_complex_im] at hire hiim
  apply Complex.ext
  · rw [← hire]
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.zero_re] using hre
  · rw [← hiim]
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,Complex.zero_im] using him

end OQ14.ConicalComplexTests

#print axioms OQ14.ConicalComplexTests.projection_fderiv
#print axioms OQ14.ConicalComplexTests.weak_partial
#print axioms OQ14.ConicalComplexTests.weak_cross_pair
#print axioms OQ14.ConicalComplexTests.weak_curl_zero
#print axioms OQ14.ConicalComplexTests.electric_test_integrable
#print axioms OQ14.ConicalComplexTests.weak_divergence
