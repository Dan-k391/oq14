import ConicalSeparatedMaxwell
import ConicalInnerMaxwell
import ConicalAnnularTests

/-! Actual separated Maxwell Gauss law against the genuine conical H1 angular test. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalSeparatedGauss
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalSeparatedSource
  OQ14.ConicalAnnularTests
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space

def region (a : ℝ) : Set Space := ball 0 a
def epsilon (p : Data) : Space → ℝ := ConicalCapField.permittivity p.contrast p.threshold
abbrev E := ConicalSeparatedMaxwell.electric
abbrev H := ConicalSeparatedMaxwell.magnetic

def D (p : Data) (a k : ℝ) : Field := fun x i => (epsilon p x : ℂ)*E p a k x i

theorem regional_maxwell (p : Data) (a k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a)
    (i : Fin 3) (f : RegionalMaxwellHelmholtz.Test (region a)) :
    RegionalMaxwellHelmholtz.curlPair (RegionalMaxwellHelmholtz.fieldPair (E p a k)) i f=
      Complex.I*(k : ℂ)*RegionalMaxwellHelmholtz.fieldPair (H p a k) i f ∧
    RegionalMaxwellHelmholtz.curlPair (RegionalMaxwellHelmholtz.fieldPair (H p a k)) i f=
      -(Complex.I*(k : ℂ))*RegionalMaxwellHelmholtz.fieldPair (D p a k) i f :=
  ConicalSeparatedMaxwell.maxwell_inner p a k ha hai hk i (ConicalInnerMaxwell.globalTest f) f.property.2.2

theorem gauss_test (p : Data) (a k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a)
    (f : RegionalMaxwellHelmholtz.Test (region a)) :
    (∑ i : Fin 3, ∫ x, (epsilon p x : ℂ)*E p a k x i*dcoord f.val x i)=0 :=
  RegionalMaxwellHelmholtz.divPair_zero_of_curl (RegionalMaxwellHelmholtz.fieldPair (H p a k))
    (RegionalMaxwellHelmholtz.fieldPair (D p a k)) (-(Complex.I*(k : ℂ)))
    (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk0)))
    (fun i f => (regional_maxwell p a k ha hai hk i f).2) f

theorem gauss_schwartz (p : Data) (a k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a)
    (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ region a) :
    (∑ i : Fin 3, ∫ x, (epsilon p x : ℂ)*E p a k x i*dcoord f x i)=0 := by
  have hc : HasCompactSupport (f : Space → ℂ) :=
    (isCompact_closedBall (0 : Space) a).of_isClosed_subset isClosed_closure (hf.trans ball_subset_closedBall)
  exact gauss_test p a k ha hai hk0 hk ⟨f,f.smooth (⊤ : ℕ∞),hc,hf⟩

theorem displacement_memLp (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    MemLp (fun x => D p a k x i) 2 (DomainCurl.regionMeasure (region a)) := by
  apply MaterialHCurl.coefficient_mul_memLp (region a) (epsilon p)
    (ConicalAnnularSource.permittivity_measurable p.contrast p.threshold) (1+p.contrast) _ _
    ((ConicalSeparatedMaxwell.electric_memLp p a k a hai i).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl))
  intro x
  have h := ConicalStaticField.permittivity_bounds p.contrast p.threshold p.contrast_nonnegative x
  change ‖ConicalCapField.permittivity p.contrast p.threshold x‖ ≤ 1+p.contrast
  rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by norm_num) h.1)]
  exact h.2

def extendedDisplacement (p : Data) (a k : ℝ) (i : Fin 3) : Space → ℂ :=
  (region a).indicator (fun x => D p a k x i)

theorem extendedDisplacement_memLp (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    MemLp (extendedDisplacement p a k i) 2 (volume : Measure Space) :=
  (memLp_indicator_iff_restrict isOpen_ball.measurableSet).mpr (displacement_memLp p a k hai i)

def displacementL2 (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) : WeakCurl.L2Scalar :=
  (extendedDisplacement_memLp p a k hai i).toLp (extendedDisplacement p a k i)

theorem displacementL2_ae (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    (displacementL2 p a k hai i : Space → ℂ) =ᵐ[volume] extendedDisplacement p a k i :=
  (extendedDisplacement_memLp p a k hai i).coeFn_toLp

private theorem test_support_inner (a : ℝ) (η : ℝ → ℂ)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) :
    (norm : Space → ℝ) ⁻¹' tsupport η ⊆ region a := by
  intro x hx
  simpa only [region,mem_ball,dist_zero_right] using (hs hx).2

private theorem derivative_zero_outer (p : Data) (a : ℝ) (η : ℝ → ℂ)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) (x : Space) (hx : x ∉ region a) (i : Fin 3) :
    angularDerivative p.eigenvalue p.threshold η x i=0 := by
  have hn : ‖x‖ ∉ tsupport η := fun h => hx (test_support_inner a η hs h)
  have hη := image_eq_zero_of_nmem_tsupport hn
  have hd : deriv η ‖x‖=0 := by
    by_contra h
    exact hn (support_deriv_subset h)
  simp only [angularDerivative,hη,hd,zero_mul,zero_div,zero_add]

theorem maxwell_angular_gauss (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (ha : 0 ≤ a) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) :
    (∑ i : Fin 3, ∫ x : Space, (epsilon p x : ℂ)*E p a k x i*
      angularDerivative p.eigenvalue p.threshold η x i)=0 := by
  have hweak (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ (norm : Space → ℝ) ⁻¹' tsupport η) :
      (∑ i : Fin 3, ∫ x : Space, displacementL2 p a k hai i x*dcoord f x i)=0 := by
    have he (i : Fin 3) : (∫ x : Space, displacementL2 p a k hai i x*dcoord f x i)=
        ∫ x : Space, (epsilon p x : ℂ)*E p a k x i*dcoord f x i := by
      apply integral_congr_ae
      filter_upwards [displacementL2_ae p a k hai i] with x hx
      rw [hx]
      by_cases hr : x ∈ region a
      · simp only [extendedDisplacement,indicator_of_mem hr,D]
      · have hz : x ∉ tsupport (f : Space → ℂ) := fun h => hr (test_support_inner a η hs (hf h))
        simp only [extendedDisplacement,indicator_of_not_mem hr,dcoord,fderiv_of_not_mem_tsupport ℝ hz,
          ContinuousLinearMap.zero_apply,mul_zero]
    simpa only [he] using gauss_schwartz p a k ha hai hk0 hk f (hf.trans (test_support_inner a η hs))
  have hs' : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn :=
    fun r hr => ⟨(hs hr).1,(hs hr).2.trans hai⟩
  have h := divergence_angular_test p.cutoff p.exponent p.eigenvalue p.threshold p.exponent_pos
    p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one η hη hc hs' (displacementL2 p a k hai) hweak
  have he (i : Fin 3) : (∫ x : Space, displacementL2 p a k hai i x*angularDerivative p.eigenvalue p.threshold η x i)=
      ∫ x : Space, (epsilon p x : ℂ)*E p a k x i*angularDerivative p.eigenvalue p.threshold η x i := by
    apply integral_congr_ae
    filter_upwards [displacementL2_ae p a k hai i] with x hx
    rw [hx]
    by_cases hr : x ∈ region a
    · simp only [extendedDisplacement,indicator_of_mem hr,D]
    · simp only [extendedDisplacement,indicator_of_not_mem hr,derivative_zero_outer p a η hs x hr i,mul_zero,zero_mul]
  simpa only [he] using h

theorem angular_product_integrable (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) (i : Fin 3) :
    Integrable (fun x : Space => (epsilon p x : ℂ)*E p a k x i*
      angularDerivative p.eigenvalue p.threshold η x i) := by
  have hs' : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn :=
    fun r hr => ⟨(hs hr).1,(hs hr).2.trans hai⟩
  apply (WeakGreen.scalarProduct_integrable (displacementL2 p a k hai i)
    (gradientL2 p.cutoff p.exponent p.eigenvalue p.threshold p.exponent_pos.le
      p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one η hη hc hs' i)).congr
  filter_upwards [displacementL2_ae p a k hai i,
    gradientL2_ae p.cutoff p.exponent p.eigenvalue p.threshold p.exponent_pos.le
      p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one η hη hc hs' i] with x hD hG
  rw [hD,hG]
  by_cases hr : x ∈ region a
  · simp only [extendedDisplacement,indicator_of_mem hr,D]
  · simp only [extendedDisplacement,indicator_of_not_mem hr,derivative_zero_outer p a η hs x hr i,mul_zero,zero_mul]

end OQ14.ConicalSeparatedGauss

#print axioms OQ14.ConicalSeparatedGauss.regional_maxwell
#print axioms OQ14.ConicalSeparatedGauss.gauss_test
#print axioms OQ14.ConicalSeparatedGauss.gauss_schwartz
#print axioms OQ14.ConicalSeparatedGauss.displacement_memLp
#print axioms OQ14.ConicalSeparatedGauss.extendedDisplacement_memLp
#print axioms OQ14.ConicalSeparatedGauss.displacementL2_ae
#print axioms OQ14.ConicalSeparatedGauss.maxwell_angular_gauss
#print axioms OQ14.ConicalSeparatedGauss.angular_product_integrable
