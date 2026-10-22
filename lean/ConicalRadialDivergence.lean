import ConicalAnnularTests
import HomogeneousEuler
import WeakDivergenceGraph

/-! Actual radial H(div) test identity with the discontinuous conical weight. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ConicalRadialDivergence
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.ConicalCapField OQ14.ConicalSpatialTests OQ14.ConicalAnnularSource
open scoped Topology

def angularWeight (a d t : ℝ) (n : Sphere) : ℝ :=
  CapSturmLiouville.coefficient d t ((n : Space) 2)*field a t n

def spatialWeight (a d t : ℝ) (x : Space) : ℝ := permittivity d t x*field a t (unit x)

theorem weight_integrable (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    Integrable (angularWeight a d t) angularMeasure :=
  SphereCapWeak.coefficient_integrable _
    (ConicalAngularTrial.continuous_integrable _ (SphereCapWeak.profile_continuous a t ha ht ht1)) d t

theorem weight_locallyIntegrable (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) : LocallyIntegrable (spatialWeight a d t) := by
  obtain ⟨C,hC,hb⟩ := angular_bounds 0 a t ha ht ht1
  have hm : Measurable (spatialWeight a d t) :=
    (permittivity_measurable d t).mul ((SphereCapWeak.profile_continuous a t ha ht ht1).measurable.comp unit_measurable)
  have he : ∀ x : Space, ‖spatialWeight a d t x‖ ≤ (1+d)*C := by
    intro x
    have hε := ConicalStaticField.permittivity_bounds d t hd x
    rw [spatialWeight,norm_mul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ permittivity d t x)]
    exact mul_le_mul hε.2 (hb (unit x)).1 (norm_nonneg _) (by positivity)
  exact (memLp_top_of_bound hm.aestronglyMeasurable _ (Eventually.of_forall he)).locallyIntegrable (by norm_num)

def radialReal (ζ : ℝ → ℝ) (x : Space) : ℝ := ζ ‖x‖

theorem radialReal_smooth (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (h0 : 0 ∉ tsupport ζ) : ContDiff ℝ (⊤ : ℕ∞) (radialReal ζ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have hz : ζ =ᶠ[𝓝 (0 : ℝ)] 0 := by
      filter_upwards [(isClosed_tsupport ζ).isOpen_compl.mem_nhds h0] with s hs
      exact image_eq_zero_of_nmem_tsupport hs
    have he : radialReal ζ =ᶠ[𝓝 (0 : Space)] (fun _ => (0 : ℝ)) :=
      hz.comp_tendsto (by simpa using (continuous_norm : Continuous (norm : Space → ℝ)).continuousAt (x := (0 : Space)) |>.tendsto)
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact hζ.contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem radialReal_radial_derivative (ζ : ℝ → ℝ) (hζ : ContDiff ℝ 1 ζ) (x : Space) :
    fderiv ℝ (radialReal ζ) x x=deriv ζ ‖x‖*‖x‖ := by
  by_cases hx : x=0
  · subst x
    simp
  · have hn := (differentiableAt_id.norm ℝ hx).hasFDerivAt
    have hs := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have he := (hn.mul hn).unique (by simpa only [pow_two] using hs)
    have hv := congrArg (fun L : Space →L[ℝ] ℝ => L x) he
    have hnorm : fderiv ℝ (norm : Space → ℝ) x x=‖x‖ := by
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
        innerSL_apply,real_inner_self_eq_norm_sq,id_eq,two_smul] at hv
      have hp := norm_pos_iff.mpr hx
      nlinarith
    have hd := (hζ.differentiable le_rfl ‖x‖).hasDerivAt.hasFDerivAt.comp x hn
    change HasFDerivAt (radialReal ζ) _ x at hd
    rw [hd.fderiv,ContinuousLinearMap.comp_apply]
    simp only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.one_apply,smul_eq_mul,id_eq]
    rw [hnorm,mul_comm]

theorem radial_weighted_weak_divergence (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (h0 : 0 ∉ tsupport ζ)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, spatialWeight a d t x*ζ ‖x‖*fderiv ℝ ψ x x)=
      -(∫ x : Space, spatialWeight a d t x*(3*ζ ‖x‖+‖x‖*deriv ζ ‖x‖)*ψ x) := by
  have hW := weight_locallyIntegrable a d t ha hd ht ht1
  have hq := (radialReal_smooth ζ hζ h0).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hpolar (r : ℝ) (hr : 0 < r) (n : Sphere) :
      spatialWeight a d t (r • (n : Space))=r^((1 : ℝ)-1)*angularWeight a d t n := by
    simp only [spatialWeight,permittivity_polar d t r hr n,unit_polar r hr n,
      sub_self,Real.rpow_zero,one_mul,angularWeight]
  have h := HomogeneousEuler.weak_euler 1 zero_lt_one _ hW _
    (weight_integrable a d t ha ht ht1) hpolar (fun x => radialReal ζ x*ψ x) (hq.mul hψ) hc.mul_left
  have hiA : Integrable (fun x : Space => spatialWeight a d t x*(ζ ‖x‖*fderiv ℝ ψ x x)) := by
    simpa only [smul_eq_mul,radialReal] using hW.integrable_smul_right_of_hasCompactSupport
      (hq.continuous.mul ((hψ.continuous_fderiv le_rfl).clm_apply continuous_id))
      (HomogeneousEuler.euler_test_compact ψ hc).mul_left
  have hiB : Integrable (fun x : Space => spatialWeight a d t x*(‖x‖*deriv ζ ‖x‖*ψ x)) := by
    simpa only [smul_eq_mul] using hW.integrable_smul_right_of_hasCompactSupport
      ((continuous_norm.mul ((hζ.continuous_deriv (by simp)).comp continuous_norm)).mul hψ.continuous) hc.mul_left
  have hiC : Integrable (fun x : Space => spatialWeight a d t x*(ζ ‖x‖*ψ x)) := by
    simpa only [smul_eq_mul,radialReal] using hW.integrable_smul_right_of_hasCompactSupport
      (hq.continuous.mul hψ.continuous) hc.mul_left
  have he : (fun x : Space => spatialWeight a d t x*fderiv ℝ (fun y => radialReal ζ y*ψ y) x x)=
      fun x => spatialWeight a d t x*(ζ ‖x‖*fderiv ℝ ψ x x)+
        spatialWeight a d t x*(‖x‖*deriv ζ ‖x‖*ψ x) := by
    funext x
    rw [fderiv_mul ((hq.differentiable le_rfl) x) ((hψ.differentiable le_rfl) x)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      radialReal_radial_derivative ζ (hζ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)),radialReal]
    ring
  rw [he,integral_add hiA hiB] at h
  have hR : (∫ x : Space, spatialWeight a d t x*(3*ζ ‖x‖+‖x‖*deriv ζ ‖x‖)*ψ x)=
      3*(∫ x : Space, spatialWeight a d t x*(ζ ‖x‖*ψ x))+
        ∫ x : Space, spatialWeight a d t x*(‖x‖*deriv ζ ‖x‖*ψ x) := by
    rw [← integral_const_mul,← integral_add (hiC.const_mul 3) hiB]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hR]
  dsimp only [radialReal] at h
  simp_rw [mul_assoc] at h ⊢
  linear_combination h

theorem weight_measurable (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    Measurable (spatialWeight a d t) :=
  (permittivity_measurable d t).mul ((SphereCapWeak.profile_continuous a t ha ht ht1).measurable.comp unit_measurable)

theorem weight_bound (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) : ∃ C ≥ (0 : ℝ), ∀ x, ‖spatialWeight a d t x‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := angular_bounds 0 a t ha ht ht1
  refine ⟨(1+d)*C,by positivity,fun x => ?_⟩
  have hε := ConicalStaticField.permittivity_bounds d t hd x
  rw [spatialWeight,norm_mul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ permittivity d t x)]
  exact mul_le_mul hε.2 (hb (unit x)).1 (norm_nonneg _) (by positivity)

theorem weight_mul_memLp (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (f : Space → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp (fun x => spatialWeight a d t x*f x) 2 (volume : Measure Space) := by
  obtain ⟨C,_,hC⟩ := weight_bound a d t ha hd ht ht1
  apply (hf.memLp_of_hasCompactSupport hc).of_le_mul (c := C)
    (((weight_measurable a d t ha ht ht1).mul hf.measurable).aestronglyMeasurable)
  filter_upwards with x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem radialReal_compact (ζ : ℝ → ℝ) (hc : HasCompactSupport ζ) : HasCompactSupport (radialReal ζ) := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0 : ℝ)
  apply (isCompact_closedBall (0 : Space) R).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  have hs : tsupport (radialReal ζ) ⊆ (norm : Space → ℝ) ⁻¹' tsupport ζ :=
    closure_minimal (fun x hx => subset_tsupport ζ hx) ((isClosed_tsupport ζ).preimage continuous_norm)
  have h := hR (hs hx)
  simpa only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_norm] using h

def radialField (ζ : ℝ → ℝ) (a d t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  spatialWeight a d t x*(ζ ‖x‖*x i)

def radialDivergence (ζ : ℝ → ℝ) (a d t : ℝ) (x : Space) : ℝ :=
  spatialWeight a d t x*(3*ζ ‖x‖+‖x‖*deriv ζ ‖x‖)

theorem radialField_memLp (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : Continuous ζ) (hc : HasCompactSupport ζ) (i : Fin 3) :
    MemLp (fun x => radialField ζ a d t x i) 2 (volume : Measure Space) :=
  weight_mul_memLp a d t ha hd ht ht1 _
    ((hζ.comp continuous_norm).mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous))
    (radialReal_compact ζ hc).mul_right

theorem radialDivergence_memLp (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    MemLp (radialDivergence ζ a d t) 2 (volume : Measure Space) :=
  weight_mul_memLp a d t ha hd ht ht1 _
    ((continuous_const.mul (hζ.continuous.comp continuous_norm)).add
      (continuous_norm.mul ((hζ.continuous_deriv (by simp)).comp continuous_norm)))
    (((radialReal_compact ζ hc).mul_left).add (radialReal_compact (deriv ζ) hc.deriv).mul_left)

theorem radial_field_real_weak_divergence (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcζ : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, radialDivergence ζ a d t x*ψ x)+
      (∑ i : Fin 3, ∫ x : Space, radialField ζ a d t x i*fderiv ℝ ψ x (basis i))=0 := by
  have hi (i : Fin 3) : Integrable (fun x : Space => radialField ζ a d t x i*fderiv ℝ ψ x (basis i)) := by
    simpa only [smul_eq_mul] using
      ((radialField_memLp a d t ha hd ht ht1 ζ hζ.continuous hcζ i).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const) (hc.fderiv_apply ℝ (basis i))
  have hsum : (∑ i : Fin 3, ∫ x : Space, radialField ζ a d t x i*fderiv ℝ ψ x (basis i))=
      ∫ x : Space, spatialWeight a d t x*ζ ‖x‖*fderiv ℝ ψ x x := by
    rw [← integral_finset_sum _ (fun i _ => hi i)]
    apply integral_congr_ae
    filter_upwards with x
    have hv : (∑ i : Fin 3, x i • basis i)=x := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
    have he : fderiv ℝ ψ x x=∑ i : Fin 3, x i*fderiv ℝ ψ x (basis i) := by
      conv_lhs => rw [← hv,map_sum]
      simp only [map_smul,smul_eq_mul,hv]
    rw [he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [radialField]
    ring
  rw [hsum,radial_weighted_weak_divergence a d t ha hd ht ht1 ζ hζ h0 ψ hψ hc]
  exact add_neg_cancel _

theorem radialField_compact (ζ : ℝ → ℝ) (hc : HasCompactSupport ζ) (a d t : ℝ) (i : Fin 3) :
    HasCompactSupport (fun x : Space => radialField ζ a d t x i) :=
  ((radialReal_compact ζ hc).mul_right (f' := fun x : Space => x i)).mul_left

private theorem complex_weak_divergence (F : Fin 3 → Space → ℝ) (Q : Space → ℝ)
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

def radialFieldL2 (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (i : Fin 3) : WeakCurl.L2Scalar :=
  ((radialField_memLp a d t ha hd ht ht1 ζ hζ.continuous hc i).ofReal).toLp
    (fun x => (radialField ζ a d t x i : ℂ))

def radialDivergenceL2 (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : WeakCurl.L2Scalar :=
  ((radialDivergence_memLp a d t ha hd ht ht1 ζ hζ hc).ofReal).toLp
    (fun x => (radialDivergence ζ a d t x : ℂ))

theorem radial_hasWeakDivergence (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    DivCurlCompact.HasWeakDivergence (radialFieldL2 a d t ha hd ht ht1 ζ hζ hc)
      (radialDivergenceL2 a d t ha hd ht ht1 ζ hζ hc) :=
  complex_weak_divergence _ _ (radialField_memLp a d t ha hd ht ht1 ζ hζ.continuous hc)
    (radialDivergence_memLp a d t ha hd ht ht1 ζ hζ hc)
    (radial_field_real_weak_divergence a d t ha hd ht ht1 ζ hζ hc h0)

theorem radialFieldL2_ae (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (i : Fin 3) :
    (radialFieldL2 a d t ha hd ht ht1 ζ hζ hc i : Space → ℂ) =ᵐ[volume]
      fun x => (radialField ζ a d t x i : ℂ) :=
  ((radialField_memLp a d t ha hd ht ht1 ζ hζ.continuous hc i).ofReal).coeFn_toLp

theorem radialDivergenceL2_ae (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    (radialDivergenceL2 a d t ha hd ht ht1 ζ hζ hc : Space → ℂ) =ᵐ[volume]
      fun x => (radialDivergence ζ a d t x : ℂ) :=
  ((radialDivergence_memLp a d t ha hd ht ht1 ζ hζ hc).ofReal).coeFn_toLp

theorem radialFieldL2_compact (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (i : Fin 3) : DivCurlCompact.CompactRepresentative (radialFieldL2 a d t ha hd ht ht1 ζ hζ hc i) :=
  ⟨_,(radialField_compact ζ hc a d t i).comp_left (g := Complex.ofReal) (by simp),
    radialFieldL2_ae a d t ha hd ht ht1 ζ hζ hc i⟩

theorem radial_gradient_pairing (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) (u : WeakCurl.L2Scalar) (G : WeakCurl.L2Vector)
    (hG : ∀ i, DivCurlCompact.HasWeakPartial u (G i) i) :
    (∑ i : Fin 3, ∫ x : Space, G i x*(radialField ζ a d t x i : ℂ))+
      (∫ x : Space, u x*(radialDivergence ζ a d t x : ℂ))=0 := by
  have h := WeakDivergenceGraph.weak_gradient_divergence_integral u G
    (radialFieldL2 a d t ha hd ht ht1 ζ hζ hc) (radialDivergenceL2 a d t ha hd ht ht1 ζ hζ hc)
    hG (radialFieldL2_compact a d t ha hd ht ht1 ζ hζ hc)
    (radial_hasWeakDivergence a d t ha hd ht ht1 ζ hζ hc h0)
  have hF (i : Fin 3) : (∫ x : Space, G i x*radialFieldL2 a d t ha hd ht ht1 ζ hζ hc i x)=
      ∫ x : Space, G i x*(radialField ζ a d t x i : ℂ) := by
    apply integral_congr_ae
    filter_upwards [radialFieldL2_ae a d t ha hd ht ht1 ζ hζ hc i] with x hx
    rw [hx]
  have hD : (∫ x : Space, u x*radialDivergenceL2 a d t ha hd ht ht1 ζ hζ hc x)=
      ∫ x : Space, u x*(radialDivergence ζ a d t x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [radialDivergenceL2_ae a d t ha hd ht ht1 ζ hζ hc] with x hx
    rw [hx]
  simpa only [hF,hD] using h

end OQ14.ConicalRadialDivergence

#print axioms OQ14.ConicalRadialDivergence.weight_integrable
#print axioms OQ14.ConicalRadialDivergence.weight_locallyIntegrable
#print axioms OQ14.ConicalRadialDivergence.radialReal_smooth
#print axioms OQ14.ConicalRadialDivergence.radialReal_radial_derivative
#print axioms OQ14.ConicalRadialDivergence.radial_weighted_weak_divergence
#print axioms OQ14.ConicalRadialDivergence.weight_measurable
#print axioms OQ14.ConicalRadialDivergence.weight_bound
#print axioms OQ14.ConicalRadialDivergence.weight_mul_memLp
#print axioms OQ14.ConicalRadialDivergence.radialReal_compact
#print axioms OQ14.ConicalRadialDivergence.radialField_memLp
#print axioms OQ14.ConicalRadialDivergence.radialDivergence_memLp
#print axioms OQ14.ConicalRadialDivergence.radial_field_real_weak_divergence
#print axioms OQ14.ConicalRadialDivergence.radialField_compact
#print axioms OQ14.ConicalRadialDivergence.radial_hasWeakDivergence
#print axioms OQ14.ConicalRadialDivergence.radialFieldL2_ae
#print axioms OQ14.ConicalRadialDivergence.radialDivergenceL2_ae
#print axioms OQ14.ConicalRadialDivergence.radialFieldL2_compact
#print axioms OQ14.ConicalRadialDivergence.radial_gradient_pairing
