import ConicalProjectedEnergy
import PolarMomentContinuity
import ConicalGaussProjection

/-! Literal continuous correction moments and actual total L2 coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ConicalCorrectionMoments
open MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalPotentialGraph OQ14.ConicalPotentialSplit OQ14.PolarMomentTesting
open scoped Topology
abbrev Space := Maxwell.Space

def cutCorrection (p : Data) (k : ℝ) (i : Fin 3) (x : Space) : ℂ := bump p x*correction p k x i

theorem cutCorrection_continuous (p : Data) (k : ℝ) (i : Fin 3) : Continuous (cutCorrection p k i) :=
  (Complex.continuous_ofReal.comp p.cutoff.continuous).mul (correction_continuous p k i)

theorem cutCorrection_compact (p : Data) (k : ℝ) (i : Fin 3) : HasCompactSupport (cutCorrection p k i) :=
  (p.cutoff.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right

theorem cutCorrection_memLp (p : Data) (k : ℝ) (i : Fin 3) : MemLp (cutCorrection p k i) 2 (volume : Measure Space) :=
  (cutCorrection_continuous p k i).memLp_of_hasCompactSupport (cutCorrection_compact p k i)

def correctionL2 (p : Data) (k : ℝ) (i : Fin 3) : WeakCurl.L2Scalar :=
  (cutCorrection_memLp p k i).toLp (cutCorrection p k i)

theorem correctionL2_ae (p : Data) (k : ℝ) (i : Fin 3) :
    (correctionL2 p k i : Space → ℂ) =ᵐ[volume] cutCorrection p k i :=
  (cutCorrection_memLp p k i).coeFn_toLp

def totalCoordinate (p : Data) (k : ℝ) (i : Fin 3) : WeakCurl.L2Scalar := gradient p k i+correctionL2 p k i

theorem totalCoordinate_inner (p : Data) (k : ℝ) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) p.cutoff.rIn → totalCoordinate p k i x=ConicalSpatialMaxwell.electric p k x i := by
  filter_upwards [Lp.coeFn_add (gradient p k i) (correctionL2 p k i),gradient_ae p k i,correctionL2_ae p k i] with x ha hg hw
  intro hx
  change (gradient p k i+correctionL2 p k i) x=_
  rw [ha]
  change gradient p k i x+correctionL2 p k i x=_
  rw [hg,hw]
  simp only [cutCorrection,(bump_inner p x hx).1,(bump_inner p x hx).2 i,one_mul,zero_mul,add_zero,sub_add_cancel]

def radialCorrection (p : Data) (k r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (cutCorrection p k i) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i) r

def tangentCorrection (p : Data) (k r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (cutCorrection p k i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r

theorem radialCorrection_continuous (p : Data) (k : ℝ) : Continuous (radialCorrection p k) := by
  apply continuous_finset_sum
  intro i _
  obtain ⟨C,hC,hb⟩ := ConicalMomentWeights.radial_bound _ _ _ p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact PolarMomentContinuity.moment_continuous _ (cutCorrection_continuous p k i) (cutCorrection_compact p k i) _
    (ConicalMomentWeights.radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb

theorem tangentCorrection_continuous (p : Data) (k : ℝ) : Continuous (tangentCorrection p k) := by
  apply continuous_finset_sum
  intro i _
  obtain ⟨C,hC,hb⟩ := ConicalMomentWeights.tangent_bound _ _ _ p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact PolarMomentContinuity.moment_continuous _ (cutCorrection_continuous p k i) (cutCorrection_compact p k i) _
    (ConicalMomentWeights.tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb

private theorem angularDerivative_zero_outer (p : Data) (η : ℝ → ℂ)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn) (x : Space)
    (hx : x ∉ ball (0 : Space) p.cutoff.rIn) (i : Fin 3) :
    ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i=0 := by
  have hn : ‖x‖ ∉ tsupport η := by
    intro h
    exact hx (by simpa only [mem_ball,dist_zero_right] using (hs h).2)
  have hz := image_eq_zero_of_nmem_tsupport hn
  have hd : deriv η ‖x‖=0 := by
    by_contra h
    exact hn (support_deriv_subset h)
  simp only [ConicalAnnularTests.angularDerivative,hz,hd,zero_mul,zero_div,zero_add]

theorem actual_gauss_pairing (p : Data) (k : ℝ) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    (∑ i : Fin 3, ∫ x : Space, (ConicalInnerMaxwell.epsilon p x : ℂ)*totalCoordinate p k i x*
      ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i)=0 := by
  have he (i : Fin 3) : (∫ x : Space, (ConicalInnerMaxwell.epsilon p x : ℂ)*totalCoordinate p k i x*
      ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i)=
      ∫ x : Space, (ConicalInnerMaxwell.epsilon p x : ℂ)*ConicalSpatialMaxwell.electric p k x i*
        ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i := by
    apply integral_congr_ae
    filter_upwards [totalCoordinate_inner p k i] with x hx
    by_cases hi : x ∈ ball (0 : Space) p.cutoff.rIn
    · rw [hx hi]
    · rw [angularDerivative_zero_outer p η hs x hi i,mul_zero,mul_zero]
  simpa only [he,ConicalInnerMaxwell.E] using
    ConicalGaussProjection.maxwell_angular_gauss p k hk0 hk η hη hc hs

theorem cutCorrection_norm_le (p : Data) (k R : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (i : Fin 3) (x : Space) (hx : x ∈ closedBall (0 : Space) R) :
    ‖cutCorrection p k i x‖ ≤ k^2*sourceBound p*‖ScalarPotentialBound.cutoff 0 (R+p.cutoff.rOut)‖ := by
  have hb : ‖bump p x‖ ≤ 1 := by
    simp only [bump,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg p.cutoff.nonneg]
    exact p.cutoff.le_one
  rw [cutCorrection,norm_mul]
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans
    (by simpa only [one_mul] using correction_bound p k R hk i x hx)

theorem correction_moment_norm_le (p : Data) (k R : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (i : Fin 3) (σ : Sphere → ℂ) (C : ℝ) (hb : ∀ n, ‖σ n‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ R) :
    ‖moment (cutCorrection p k i) σ r‖ ≤
      (k^2*sourceBound p*‖ScalarPotentialBound.cutoff 0 (R+p.cutoff.rOut)‖)*C*(angularMeasure univ).toReal := by
  have hz : (0 : Space) ∈ closedBall (0 : Space) R := by simp only [mem_closedBall,dist_self]; linarith
  apply PolarMomentContinuity.moment_norm_le
  · exact (norm_nonneg _).trans (cutCorrection_norm_le p k R hk i 0 hz)
  · exact hb
  · intro n
    apply cutCorrection_norm_le p k R hk i
    simpa only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,
      AngularPower.sphere_norm,mul_one] using hrR

end OQ14.ConicalCorrectionMoments



#print axioms OQ14.ConicalCorrectionMoments.cutCorrection_continuous
#print axioms OQ14.ConicalCorrectionMoments.cutCorrection_compact
#print axioms OQ14.ConicalCorrectionMoments.cutCorrection_memLp
#print axioms OQ14.ConicalCorrectionMoments.correctionL2_ae
#print axioms OQ14.ConicalCorrectionMoments.totalCoordinate_inner
#print axioms OQ14.ConicalCorrectionMoments.radialCorrection_continuous
#print axioms OQ14.ConicalCorrectionMoments.tangentCorrection_continuous
#print axioms OQ14.ConicalCorrectionMoments.actual_gauss_pairing
#print axioms OQ14.ConicalCorrectionMoments.cutCorrection_norm_le
#print axioms OQ14.ConicalCorrectionMoments.correction_moment_norm_le
