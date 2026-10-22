import ConicalAnnularSource
import ConicalComplexTests

/-! Actual complex test identities and L2 classes of the annular conical construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalComplexLocalization
open MeasureTheory Set OQ14.Maxwell OQ14.ConicalCapField OQ14.ConicalCutoffGradient
  OQ14.ConicalCutoffCurl OQ14.ConicalAnnularSource
open scoped Topology ENNReal

def complexify (F : Space → Space) : Field := fun x i => (F x i : ℂ)

private theorem mul_continuous_locallyIntegrable (f g : Space → ℝ)
    (hf : LocallyIntegrable f) (hg : Continuous g) : LocallyIntegrable (fun x => f x*g x) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).mul_continuousOn hg.continuousOn hK

private theorem real_integral (f : Space → ℂ) (hf : Integrable f) :
    (∫ x : Space, f x).re=∫ x : Space, (f x).re := by
  simpa only [RCLike.re_eq_complex_re] using (integral_re hf).symm

private theorem imag_integral (f : Space → ℂ) (hf : Integrable f) :
    (∫ x : Space, f x).im=∫ x : Space, (f x).im := by
  simpa only [RCLike.im_eq_complex_im] using (integral_im hf).symm

private theorem complex_partial_of_real (u v : Space → ℝ) (hu : LocallyIntegrable u)
    (hv : LocallyIntegrable v) (i : Fin 3)
    (hreal : ∀ (ψ : Space → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x : Space, u x*fderiv ℝ ψ x (basis i))=-(∫ x : Space, v x*ψ x))
    (ψ : Space → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, (u x : ℂ)*dcoord ψ x i)=-(∫ x : Space, (v x : ℂ)*ψ x) := by
  have hiL : Integrable (fun x : Space => (u x : ℂ)*dcoord ψ x i) := by
    simpa only [Complex.real_smul,dcoord] using hu.integrable_smul_right_of_hasCompactSupport
      ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const) (hc.fderiv_apply ℝ (basis i))
  have hiR : Integrable (fun x : Space => (v x : ℂ)*ψ x) := by
    simpa only [Complex.real_smul] using hv.integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have hReFD (x w : Space) : fderiv ℝ (fun y => (ψ y).re) x w=(fderiv ℝ ψ x w).re :=
    ConicalComplexTests.projection_fderiv Complex.reCLM ψ (hψ.differentiable le_rfl) x w
  have hImFD (x w : Space) : fderiv ℝ (fun y => (ψ y).im) x w=(fderiv ℝ ψ x w).im :=
    ConicalComplexTests.projection_fderiv Complex.imCLM ψ (hψ.differentiable le_rfl) x w
  have hre := hreal (fun x => (ψ x).re) (Complex.reCLM.contDiff.comp hψ) (hc.comp_left (g := Complex.re) rfl)
  have him := hreal (fun x => (ψ x).im) (Complex.imCLM.contDiff.comp hψ) (hc.comp_left (g := Complex.im) rfl)
  simp_rw [hReFD] at hre
  simp_rw [hImFD] at him
  apply Complex.ext
  · rw [Complex.neg_re,real_integral _ hiL,real_integral _ hiR]
    simpa only [dcoord,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre
  · rw [Complex.neg_im,imag_integral _ hiL,imag_integral _ hiR]
    simpa only [dcoord,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using him

private theorem complex_curl_of_real (A C : Space → Space)
    (hA : ∀ i, LocallyIntegrable (fun x => A x i)) (hC : ∀ i, LocallyIntegrable (fun x => C x i))
    (hreal : ∀ (i : Fin 3) (ψ : Space → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x : Space, A x (WeakCurl.next i)*fderiv ℝ ψ x (basis (WeakCurl.previous i)))-
        (∫ x : Space, A x (WeakCurl.previous i)*fderiv ℝ ψ x (basis (WeakCurl.next i)))=
          ∫ x : Space, C x i*ψ x)
    (i : Fin 3) (ψ : Space → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, complexify A x (WeakCurl.next i)*dcoord ψ x (WeakCurl.previous i))-
      (∫ x : Space, complexify A x (WeakCurl.previous i)*dcoord ψ x (WeakCurl.next i))=
        ∫ x : Space, complexify C x i*ψ x := by
  have hiA (j k : Fin 3) : Integrable (fun x : Space => (A x j : ℂ)*dcoord ψ x k) := by
    simpa only [Complex.real_smul,dcoord] using (hA j).integrable_smul_right_of_hasCompactSupport
      ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const) (hc.fderiv_apply ℝ (basis k))
  have hiC : Integrable (fun x : Space => (C x i : ℂ)*ψ x) := by
    simpa only [Complex.real_smul] using (hC i).integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have hReFD (x w : Space) : fderiv ℝ (fun y => (ψ y).re) x w=(fderiv ℝ ψ x w).re :=
    ConicalComplexTests.projection_fderiv Complex.reCLM ψ (hψ.differentiable le_rfl) x w
  have hImFD (x w : Space) : fderiv ℝ (fun y => (ψ y).im) x w=(fderiv ℝ ψ x w).im :=
    ConicalComplexTests.projection_fderiv Complex.imCLM ψ (hψ.differentiable le_rfl) x w
  have hre := hreal i (fun x => (ψ x).re) (Complex.reCLM.contDiff.comp hψ) (hc.comp_left (g := Complex.re) rfl)
  have him := hreal i (fun x => (ψ x).im) (Complex.imCLM.contDiff.comp hψ) (hc.comp_left (g := Complex.im) rfl)
  simp_rw [hReFD] at hre
  simp_rw [hImFD] at him
  dsimp only [complexify]
  apply Complex.ext
  · rw [Complex.sub_re,real_integral _ (hiA (WeakCurl.next i) (WeakCurl.previous i)),
      real_integral _ (hiA (WeakCurl.previous i) (WeakCurl.next i)),real_integral _ hiC]
    simpa only [complexify,dcoord,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre
  · rw [Complex.sub_im,imag_integral _ (hiA (WeakCurl.next i) (WeakCurl.previous i)),
      imag_integral _ (hiA (WeakCurl.previous i) (WeakCurl.next i)),imag_integral _ hiC]
    simpa only [complexify,dcoord,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using him

theorem cut_weak_partial_complex (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (i : Fin 3) (ψ : Space → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, (cutPotential χ ν a t x : ℂ)*dcoord ψ x i)=
      -(∫ x : Space, complexify (cutElectric χ ν a t) x i*ψ x) := by
  have hu : LocallyIntegrable (cutPotential χ ν a t) := by
    have he : cutPotential χ ν a t=(fun x => potential ν a t x*χ x) := by
      funext x
      exact mul_comm _ _
    rw [he]
    exact mul_continuous_locallyIntegrable _ _
      (ConicalSpatialTests.potential_locallyIntegrable ν a t hν.le ha ht ht1) χ.continuous
  exact complex_partial_of_real _ _ hu
    ((cutElectric_component_memLp χ ν a t hν.le ha ht ht1 i).locallyIntegrable (by norm_num)) i
    (fun φ hφ hφc => cut_weak_partial ν a t hν ha ht ht1 χ χ.contDiff φ hφ hφc i) ψ hψ hc

theorem cut_weak_curl_complex (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ)
    (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1)
    (hroot : CapAngularShooting.determinant d t a = 0) (heq : ν*(ν+1)=a)
    (i : Fin 3) (ψ : Space → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, complexify (cutVectorPotential χ ν a d t) x (WeakCurl.next i)*dcoord ψ x (WeakCurl.previous i))-
      (∫ x : Space, complexify (cutVectorPotential χ ν a d t) x (WeakCurl.previous i)*dcoord ψ x (WeakCurl.next i))=
        ∫ x : Space, complexify (cutCurl χ ν a d t) x i*ψ x := by
  have hA (j : Fin 3) : LocallyIntegrable (fun x => cutVectorPotential χ ν a d t x j) := by
    simpa only [cutVectorPotential,PiLp.smul_apply,smul_eq_mul,mul_comm] using
      mul_continuous_locallyIntegrable _ _ (potential_component_locallyIntegrable ν a d t hν.le ha ht ht1 j) χ.continuous
  exact complex_curl_of_real _ _ hA
    (fun j => (cutCurl_component_memLp χ ν a d t hν.le ha hd ht ht1 j).locallyIntegrable (by norm_num))
    (fun j φ hφ hφc => cut_weak_curl ν a d t hν ha ht ht1 hroot heq χ χ.contDiff j φ hφ hφc) i ψ hψ hc

theorem cutElectric_memLp_complex (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    MemLp (fun x => complexify (cutElectric χ ν a t) x i) 2 (volume : Measure Space) :=
  (cutElectric_component_memLp χ ν a t hν ha ht ht1 i).ofReal

theorem cutCurl_memLp_complex (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    MemLp (fun x => complexify (cutCurl χ ν a d t) x i) 2 (volume : Measure Space) :=
  (cutCurl_component_memLp χ ν a d t hν ha hd ht ht1 i).ofReal

theorem forcing_memLp_complex (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    MemLp (fun x => complexify (forcing χ ν a d t) x i) 2 (volume : Measure Space) :=
  (forcing_component_memLp χ ν a d t hν ha hd ht ht1 i).ofReal

theorem cutPotential_memLp_complex (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    MemLp (fun x => (cutPotential χ ν a t x : ℂ)) 2 (volume : Measure Space) := by
  classical
  have hball : MemLp (cutPotential χ ν a t) 2 (volume.restrict (Metric.closedBall 0 χ.rOut)) := by
    apply (potential_memLp_two_ball ν a t χ.rOut hν ha ht ht1).of_le_mul (c := 1)
    · exact (χ.continuous.measurable.mul (potential_measurable ν a t ha ht ht1)).aestronglyMeasurable
    · filter_upwards with x
      change ‖χ x*potential ν a t x‖ ≤ 1*‖potential ν a t x‖
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg χ.nonneg]
      exact mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg _)
  have hInd : MemLp ((Metric.closedBall (0 : Space) χ.rOut).indicator (cutPotential χ ν a t)) 2
      (volume : Measure Space) := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr hball
  have he : (Metric.closedBall (0 : Space) χ.rOut).indicator (cutPotential χ ν a t)=cutPotential χ ν a t := by
    funext x
    by_cases hx : x ∈ Metric.closedBall (0 : Space) χ.rOut
    · rw [indicator_of_mem hx]
    · rw [indicator_of_not_mem hx]
      have hz : χ x=0 := χ.zero_of_le_dist (le_of_lt (not_le.mp hx))
      simp only [cutPotential,hz,zero_mul]
  rw [he] at hInd
  exact hInd.ofReal

theorem cutCurl_weak_divergence_complex (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ)
    (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1)
    (hroot : CapAngularShooting.determinant d t a = 0) (heq : ν*(ν+1)=a)
    (ψ : Space → ℂ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin 3, ∫ x : Space, complexify (cutCurl χ ν a d t) x i*dcoord ψ x i)=0 := by
  have hp (i : Fin 3) : ContDiff ℝ 1 (fun x => dcoord ψ x i) := by
    have hD : ContDiff ℝ 1 (fderiv ℝ ψ) := (contDiff_succ_iff_fderiv (n := 1)).mp hψ |>.2.2
    exact hD.clm_apply contDiff_const
  have he (i : Fin 3) : (∫ x : Space, complexify (cutCurl χ ν a d t) x i*dcoord ψ x i)=
      (∫ x : Space, complexify (cutVectorPotential χ ν a d t) x (WeakCurl.next i)*
        dcoord (fun y => dcoord ψ y i) x (WeakCurl.previous i))-
      (∫ x : Space, complexify (cutVectorPotential χ ν a d t) x (WeakCurl.previous i)*
        dcoord (fun y => dcoord ψ y i) x (WeakCurl.next i)) :=
    (cut_weak_curl_complex χ ν a d t hν ha hd ht ht1 hroot heq i _ (hp i) (hc.fderiv_apply ℝ (basis i))).symm
  have hm (j k l : Fin 3) :
      (∫ x : Space, complexify (cutVectorPotential χ ν a d t) x j*dcoord (fun y => dcoord ψ y k) x l)=
        ∫ x : Space, complexify (cutVectorPotential χ ν a d t) x j*dcoord (fun y => dcoord ψ y l) x k := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Maxwell.partial_comm hψ x l k]
  simp only [Fin.sum_univ_three]
  rw [he 0,he 1,he 2]
  simp [WeakCurl.next,WeakCurl.previous]
  rw [hm 1 0 2,hm 2 0 1,hm 0 1 2]
  ring

end OQ14.ConicalComplexLocalization

#print axioms OQ14.ConicalComplexLocalization.cut_weak_partial_complex
#print axioms OQ14.ConicalComplexLocalization.cut_weak_curl_complex
#print axioms OQ14.ConicalComplexLocalization.cutElectric_memLp_complex
#print axioms OQ14.ConicalComplexLocalization.cutCurl_memLp_complex
#print axioms OQ14.ConicalComplexLocalization.forcing_memLp_complex
#print axioms OQ14.ConicalComplexLocalization.cutPotential_memLp_complex
#print axioms OQ14.ConicalComplexLocalization.cutCurl_weak_divergence_complex
