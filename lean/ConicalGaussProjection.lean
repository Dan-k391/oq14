import ConicalAnnularTests
import ConicalInnerMaxwell

/-! Actual Maxwell Gauss law tested by the genuine cap-profile H1 angular test. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ConicalGaussProjection
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalInnerMaxwell OQ14.ConicalAnnularTests
open scoped Topology SchwartzMap

abbrev Space := Maxwell.Space

def extendedDisplacement (p : Data) (k : ℝ) (i : Fin 3) : Space → ℂ :=
  (region p).indicator (fun x => D p k x i)

theorem extendedDisplacement_memLp (p : Data) (k : ℝ) (i : Fin 3) :
    MemLp (extendedDisplacement p k i) 2 (volume : Measure Space) :=
  (memLp_indicator_iff_restrict isOpen_ball.measurableSet).mpr (displacement_memLp p k i)

def displacementL2 (p : Data) (k : ℝ) (i : Fin 3) : WeakCurl.L2Scalar :=
  (extendedDisplacement_memLp p k i).toLp (extendedDisplacement p k i)

theorem displacementL2_ae (p : Data) (k : ℝ) (i : Fin 3) :
    (displacementL2 p k i : Space → ℂ) =ᵐ[volume] extendedDisplacement p k i :=
  (extendedDisplacement_memLp p k i).coeFn_toLp

private theorem test_support_inner (p : Data) (η : ℝ → ℂ)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    (norm : Space → ℝ) ⁻¹' tsupport η ⊆ region p := by
  intro x hx
  simpa only [region,mem_ball,dist_zero_right] using (hs hx).2

private theorem derivative_zero_outer (p : Data) (η : ℝ → ℂ)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn) (x : Space) (hx : x ∉ region p) (i : Fin 3) :
    angularDerivative p.eigenvalue p.threshold η x i=0 := by
  have hn : ‖x‖ ∉ tsupport η := fun h => hx (test_support_inner p η hs h)
  have hη := image_eq_zero_of_nmem_tsupport hn
  have hd : deriv η ‖x‖=0 := by
    by_contra h
    exact hn (support_deriv_subset h)
  simp only [angularDerivative,hη,hd,zero_mul,zero_div,zero_add]

theorem maxwell_angular_gauss (p : Data) (k : ℝ) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    (∑ i : Fin 3, ∫ x : Space, (epsilon p x : ℂ)*E p k x i*
      angularDerivative p.eigenvalue p.threshold η x i)=0 := by
  have hweak (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ (norm : Space → ℝ) ⁻¹' tsupport η) :
      (∑ i : Fin 3, ∫ x : Space, displacementL2 p k i x*dcoord f x i)=0 := by
    have he (i : Fin 3) : (∫ x : Space, displacementL2 p k i x*dcoord f x i)=
        ∫ x : Space, (epsilon p x : ℂ)*E p k x i*dcoord f x i := by
      apply integral_congr_ae
      filter_upwards [displacementL2_ae p k i] with x hx
      rw [hx]
      by_cases hr : x ∈ region p
      · simp only [extendedDisplacement,indicator_of_mem hr,D]
      · have hz : x ∉ tsupport (f : Space → ℂ) := fun h => hr (test_support_inner p η hs (hf h))
        simp only [extendedDisplacement,indicator_of_not_mem hr,dcoord,fderiv_of_not_mem_tsupport ℝ hz,
          ContinuousLinearMap.zero_apply,mul_zero]
    simpa only [he] using gauss_schwartz p k hk0 hk f (hf.trans (test_support_inner p η hs))
  have h := divergence_angular_test p.cutoff p.exponent p.eigenvalue p.threshold p.exponent_pos
    p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one η hη hc hs (displacementL2 p k) hweak
  have he (i : Fin 3) : (∫ x : Space, displacementL2 p k i x*angularDerivative p.eigenvalue p.threshold η x i)=
      ∫ x : Space, (epsilon p x : ℂ)*E p k x i*angularDerivative p.eigenvalue p.threshold η x i := by
    apply integral_congr_ae
    filter_upwards [displacementL2_ae p k i] with x hx
    rw [hx]
    by_cases hr : x ∈ region p
    · simp only [extendedDisplacement,indicator_of_mem hr,D]
    · simp only [extendedDisplacement,indicator_of_not_mem hr,derivative_zero_outer p η hs x hr i,mul_zero,zero_mul]
  simpa only [he] using h

theorem angular_product_integrable (p : Data) (k : ℝ)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn) (i : Fin 3) :
    Integrable (fun x : Space => (epsilon p x : ℂ)*E p k x i*
      angularDerivative p.eigenvalue p.threshold η x i) := by
  apply (WeakGreen.scalarProduct_integrable (displacementL2 p k i)
    (gradientL2 p.cutoff p.exponent p.eigenvalue p.threshold p.exponent_pos.le
      p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one η hη hc hs i)).congr
  filter_upwards [displacementL2_ae p k i,
    gradientL2_ae p.cutoff p.exponent p.eigenvalue p.threshold p.exponent_pos.le
      p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one η hη hc hs i] with x hD hG
  rw [hD,hG]
  by_cases hr : x ∈ region p
  · simp only [extendedDisplacement,indicator_of_mem hr,D]
  · simp only [extendedDisplacement,indicator_of_not_mem hr,derivative_zero_outer p η hs x hr i,mul_zero,zero_mul]

end OQ14.ConicalGaussProjection

#print axioms OQ14.ConicalGaussProjection.extendedDisplacement_memLp
#print axioms OQ14.ConicalGaussProjection.displacementL2_ae
#print axioms OQ14.ConicalGaussProjection.maxwell_angular_gauss
#print axioms OQ14.ConicalGaussProjection.angular_product_integrable
