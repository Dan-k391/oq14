import ConicalFiniteExpansion
import ConicalAngularEnergy

/-! Genuine annular L2 functionals of the constructed conical Maxwell family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalAnnularCoefficient
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalCorrectionMoments OQ14.ConicalTangentialDivergence OQ14.PolarMomentTesting
  OQ14.ConicalPotentialGraph OQ14.WeakGreen OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space

def testCoordinate (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (i : Fin 3) : WeakCurl.L2Scalar :=
  tangentFieldL2 p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i

def fieldPair (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    VectorFourier.VectorL2 →L[ℂ] ℂ :=
  ∑ i : Fin 3, (scalarProduct (testCoordinate p ζ hζ hc i)).comp
    (VectorFourier.scalarCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp (VectorFourier.coordinate i))

def correctionPair (p : Data) (k : ℝ) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : ℂ :=
  ∑ i : Fin 3, scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 p k i)

def gradientPair (p : Data) (k : ℝ) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : ℂ :=
  ∑ i : Fin 3, scalarProduct (testCoordinate p ζ hζ hc i) (gradient p k i)

theorem fieldPair_apply (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (F : VectorFourier.VectorL2) :
    fieldPair p ζ hζ hc F=∑ i : Fin 3, scalarProduct (testCoordinate p ζ hζ hc i) (physicalCoordinate F i) := by
  simp only [fieldPair,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,physicalCoordinate,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe]

theorem fieldPair_tendsto (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    Tendsto (fun k => fieldPair p ζ hζ hc (ConicalDynamicVolume.field p k)) (𝓝 (0 : ℝ))
      (𝓝 (fieldPair p ζ hζ hc (electric p))) :=
  (fieldPair p ζ hζ hc).continuous.tendsto _ |>.comp (ConicalDynamicVolume.field_tendsto p)

theorem gradientPair_eq (p : Data) (k : ℝ) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    gradientPair p k ζ hζ hc=fieldPair p ζ hζ hc (ConicalDynamicVolume.field p k)-correctionPair p k ζ hζ hc := by
  have hi (i : Fin 3) : scalarProduct (testCoordinate p ζ hζ hc i) (gradient p k i)=
      scalarProduct (testCoordinate p ζ hζ hc i) (physicalCoordinate (ConicalDynamicVolume.field p k) i)-
      scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 p k i) := by
    rw [← map_sub,scalarProduct_integral,scalarProduct_integral]
    apply integral_congr_ae
    filter_upwards [tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i,
      gradient_ae p k i,correctionL2_ae p k i,
      Lp.coeFn_sub (physicalCoordinate (ConicalDynamicVolume.field p k) i) (correctionL2 p k i),
      ae_imp_of_ae_restrict (ConicalSpatialMaxwell.field_ae p k i)] with x ht hg hw ha hf
    change testCoordinate p ζ hζ hc i x*gradient p k i x=_
    dsimp only [testCoordinate]
    rw [ht,hg,ha]
    simp only [Pi.sub_apply]
    by_cases hx : x ∈ ball (0 : Space) p.cutoff.rIn
    · have hxo : x ∈ closedBall (0 : Space) p.cutoff.rOut := by
        simp only [mem_ball,dist_zero_right] at hx
        simp only [mem_closedBall,dist_zero_right]
        exact hx.le.trans p.cutoff.rIn_lt_rOut.le
      rw [(bump_inner p x hx).1,(bump_inner p x hx).2 i,hf hxo,hw]
      simp only [Pi.sub_apply,cutCorrection,(bump_inner p x hx).1,one_mul,zero_mul,add_zero]
    · have hz : ζ ‖x‖=0 := image_eq_zero_of_nmem_tsupport (fun h => hx (by
        simpa only [mem_ball,dist_zero_right] using (hs h).2))
      simp only [tangentField,hz,zero_mul,Complex.ofReal_zero,mul_zero]
  simp only [gradientPair,fieldPair_apply,correctionPair,hi,Finset.sum_sub_distrib]

theorem test_integrable (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (i : Fin 3) :
    Integrable (fun x : Space => (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)) := by
  have hm : MemLp (fun x : Space => (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)) 2 volume :=
    (tangentField_memLp _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ.continuous hc i).ofReal
  have hi := hm.locallyIntegrable (by norm_num)
  have hs : HasCompactSupport (fun x : Space => (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)) :=
    ((ConicalRadialDivergence.radialReal_compact ζ hc).mul_right).comp_left (g := Complex.ofReal) (by simp)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).mp (hi.integrableOn_isCompact hs)

def testMass (p : Data) (ζ : ℝ → ℝ) : ℝ :=
  ∑ i : Fin 3, ∫ x : Space, ‖(tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)‖

theorem correctionPair_norm_le (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    ‖correctionPair p k ζ hζ hc‖ ≤
      (k^2*ConicalPotentialSplit.sourceBound p*‖ScalarPotentialBound.cutoff 0 (p.cutoff.rOut+p.cutoff.rOut)‖)*testMass p ζ := by
  let M := k^2*ConicalPotentialSplit.sourceBound p*‖ScalarPotentialBound.cutoff 0 (p.cutoff.rOut+p.cutoff.rOut)‖
  have hb (i : Fin 3) (x : Space) : ‖cutCorrection p k i x‖ ≤ M := by
    by_cases hx : x ∈ closedBall (0 : Space) p.cutoff.rOut
    · exact cutCorrection_norm_le p k _ hk i x hx
    · have hz : p.cutoff x=0 := p.cutoff.zero_of_le_dist (le_of_lt (not_le.mp hx))
      have hM : 0 ≤ M := (norm_nonneg _).trans (cutCorrection_norm_le p k _ hk i 0
        (by simp only [mem_closedBall,dist_self]; exact p.cutoff.rOut_pos.le))
      simpa only [cutCorrection,bump,hz,Complex.ofReal_zero,zero_mul,norm_zero] using hM
  have hi (i : Fin 3) : ‖scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 p k i)‖ ≤
      M*(∫ x : Space, ‖(tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)‖) := by
    rw [scalarProduct_integral]
    have he : (∫ x : Space, testCoordinate p ζ hζ hc i x*correctionL2 p k i x)=
        ∫ x : Space, (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)*cutCorrection p k i x := by
      apply integral_congr_ae
      filter_upwards [tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i,
        correctionL2_ae p k i] with x ht hw
      exact congrArg₂ (fun a b : ℂ => a*b) ht hw
    rw [he,← integral_const_mul]
    apply norm_integral_le_of_norm_le ((test_integrable p ζ hζ hc i).norm.const_mul M)
    filter_upwards with x
    rw [norm_mul,mul_comm M]
    exact mul_le_mul_of_nonneg_left (hb i x) (norm_nonneg _)
  calc
    ‖correctionPair p k ζ hζ hc‖ ≤ ∑ i : Fin 3, ‖scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 p k i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, M*(∫ x : Space, ‖(tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)‖) := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [testMass,Finset.mul_sum,M]

theorem correctionPair_tendsto (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    Tendsto (fun k => correctionPair p k ζ hζ hc) (𝓝 (0 : ℝ)) (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have he : ∀ᶠ k : ℝ in 𝓝 0, |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (DynamicStaticLimit.frequencyRadius_positive (coefficient p) p.cutoff.rOut)] with k hk
    have ht : |k| < DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hk
    exact ht.le
  have hl : Tendsto (fun k : ℝ => (k^2*ConicalPotentialSplit.sourceBound p*‖ScalarPotentialBound.cutoff 0 (p.cutoff.rOut+p.cutoff.rOut)‖)*testMass p ζ)
      (𝓝 0) (𝓝 0) := by
    simpa using ((((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 (0 : ℝ)) (𝓝 0)).pow 2).mul_const (ConicalPotentialSplit.sourceBound p)).mul_const
      ‖ScalarPotentialBound.cutoff 0 (p.cutoff.rOut+p.cutoff.rOut)‖).mul_const (testMass p ζ)
  exact squeeze_zero' (Filter.Eventually.of_forall (fun k => norm_nonneg _))
    (he.mono (fun k hk => correctionPair_norm_le p k hk ζ hζ hc)) hl

theorem gradientPair_tendsto (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    Tendsto (fun k => gradientPair p k ζ hζ hc) (𝓝 (0 : ℝ)) (𝓝 (fieldPair p ζ hζ hc (electric p))) := by
  simpa only [sub_zero] using ((fieldPair_tendsto p ζ hζ hc).sub (correctionPair_tendsto p ζ hζ hc)).congr'
    (Filter.Eventually.of_forall (fun k => (gradientPair_eq p k ζ hζ hc hs).symm))

end OQ14.ConicalAnnularCoefficient


#print axioms OQ14.ConicalAnnularCoefficient.fieldPair_apply
#print axioms OQ14.ConicalAnnularCoefficient.fieldPair_tendsto
#print axioms OQ14.ConicalAnnularCoefficient.gradientPair_eq
#print axioms OQ14.ConicalAnnularCoefficient.test_integrable
#print axioms OQ14.ConicalAnnularCoefficient.correctionPair_norm_le
#print axioms OQ14.ConicalAnnularCoefficient.correctionPair_tendsto
#print axioms OQ14.ConicalAnnularCoefficient.gradientPair_tendsto
