import ConicalGraphEnergy
import ConicalSeparatedGauss
import PolarMomentContinuity

/-! Actual separated conical correction moments and total L2 coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalSeparatedCorrection
open MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalGradientGraph OQ14.ConicalSeparatedPotential OQ14.PolarMomentTesting
open scoped Topology
abbrev Space := Maxwell.Space

def cutCorrection (p : Data) (a k : ℝ) (i : Fin 3) (x : Space) : ℂ := bump p.cutoff x*correction p a k x i

theorem cutCorrection_continuous (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) : Continuous (cutCorrection p a k i) :=
  (Complex.continuous_ofReal.comp p.cutoff.continuous).mul (correction_continuous p a k hai i)

theorem cutCorrection_compact (p : Data) (a k : ℝ) (i : Fin 3) : HasCompactSupport (cutCorrection p a k i) :=
  (p.cutoff.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right

theorem cutCorrection_memLp (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) : MemLp (cutCorrection p a k i) 2 (volume : Measure Space) :=
  (cutCorrection_continuous p a k hai i).memLp_of_hasCompactSupport (cutCorrection_compact p a k i)

def correctionL2 (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) : WeakCurl.L2Scalar :=
  (cutCorrection_memLp p a k hai i).toLp (cutCorrection p a k i)

theorem correctionL2_ae (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    (correctionL2 p a k hai i : Space → ℂ) =ᵐ[volume] cutCorrection p a k i :=
  (cutCorrection_memLp p a k hai i).coeFn_toLp

def totalCoordinate (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) : WeakCurl.L2Scalar := (separated p a k hai).gradient i+correctionL2 p a k hai i

theorem totalCoordinate_inner (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) a → totalCoordinate p a k hai i x=ConicalSeparatedMaxwell.electric p a k x i := by
  filter_upwards [Lp.coeFn_add ((separated p a k hai).gradient i) (correctionL2 p a k hai i),separated_gradient_ae p a k hai i,correctionL2_ae p a k hai i] with x ha hg hw
  intro hx
  change ((separated p a k hai).gradient i+correctionL2 p a k hai i) x=_
  rw [ha]
  change (separated p a k hai).gradient i x+correctionL2 p a k hai i x=_
  rw [hg,hw]
  simp only [cutCorrection,(bump_inner p.cutoff x (ball_subset_ball hai.le hx)).1,(bump_inner p.cutoff x (ball_subset_ball hai.le hx)).2 i,one_mul,zero_mul,add_zero,sub_add_cancel]

def radialCorrection (p : Data) (a k r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (cutCorrection p a k i) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i) r

def tangentCorrection (p : Data) (a k r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (cutCorrection p a k i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r

theorem radialCorrection_continuous (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) : Continuous (radialCorrection p a k) := by
  apply continuous_finset_sum
  intro i _
  obtain ⟨C,hC,hb⟩ := ConicalMomentWeights.radial_bound _ _ _ p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact PolarMomentContinuity.moment_continuous _ (cutCorrection_continuous p a k hai i) (cutCorrection_compact p a k i) _
    (ConicalMomentWeights.radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb

theorem tangentCorrection_continuous (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) : Continuous (tangentCorrection p a k) := by
  apply continuous_finset_sum
  intro i _
  obtain ⟨C,hC,hb⟩ := ConicalMomentWeights.tangent_bound _ _ _ p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact PolarMomentContinuity.moment_continuous _ (cutCorrection_continuous p a k hai i) (cutCorrection_compact p a k i) _
    (ConicalMomentWeights.tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb

private theorem angularDerivative_zero_outer (p : Data) (a : ℝ) (η : ℝ → ℂ)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) (x : Space)
    (hx : x ∉ ball (0 : Space) a) (i : Fin 3) :
    ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i=0 := by
  have hn : ‖x‖ ∉ tsupport η := by
    intro h
    exact hx (by simpa only [mem_ball,dist_zero_right] using (hs h).2)
  have hz := image_eq_zero_of_nmem_tsupport hn
  have hd : deriv η ‖x‖=0 := by
    by_contra h
    exact hn (support_deriv_subset h)
  simp only [ConicalAnnularTests.angularDerivative,hz,hd,zero_mul,zero_div,zero_add]

theorem actual_gauss_pairing (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (ha : 0 ≤ a) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) :
    (∑ i : Fin 3, ∫ x : Space, (ConicalSeparatedGauss.epsilon p x : ℂ)*totalCoordinate p a k hai i x*
      ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i)=0 := by
  have he (i : Fin 3) : (∫ x : Space, (ConicalSeparatedGauss.epsilon p x : ℂ)*totalCoordinate p a k hai i x*
      ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i)=
      ∫ x : Space, (ConicalSeparatedGauss.epsilon p x : ℂ)*ConicalSeparatedMaxwell.electric p a k x i*
        ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i := by
    apply integral_congr_ae
    filter_upwards [totalCoordinate_inner p a k hai i] with x hx
    by_cases hi : x ∈ ball (0 : Space) a
    · rw [hx hi]
    · rw [angularDerivative_zero_outer p a η hs x hi i,mul_zero,mul_zero]
  simpa only [he,ConicalSeparatedGauss.E] using
    ConicalSeparatedGauss.maxwell_angular_gauss p a k hai ha hk0 hk η hη hc hs

theorem cutCorrection_norm_le (p : Data) (a k R : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (i : Fin 3) (x : Space) (hx : x ∈ closedBall (0 : Space) R) :
    ‖cutCorrection p a k i x‖ ≤ k^2*sourceBound p a*‖ScalarPotentialBound.cutoff 0 (R+p.cutoff.rOut)‖ := by
  have hb : ‖bump p.cutoff x‖ ≤ 1 := by
    simp only [bump,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg p.cutoff.nonneg]
    exact p.cutoff.le_one
  rw [cutCorrection,norm_mul]
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans
    (by simpa only [one_mul] using correction_bound p a k R ha hai hk i x hx)

theorem correction_moment_norm_le (p : Data) (a k R : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (i : Fin 3) (σ : Sphere → ℂ) (C : ℝ) (hb : ∀ n, ‖σ n‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ R) :
    ‖moment (cutCorrection p a k i) σ r‖ ≤
      (k^2*sourceBound p a*‖ScalarPotentialBound.cutoff 0 (R+p.cutoff.rOut)‖)*C*(angularMeasure univ).toReal := by
  have hz : (0 : Space) ∈ closedBall (0 : Space) R := by simp only [mem_closedBall,dist_self]; linarith
  apply PolarMomentContinuity.moment_norm_le
  · exact (norm_nonneg _).trans (cutCorrection_norm_le p a k R ha hai hk i 0 hz)
  · exact hb
  · intro n
    apply cutCorrection_norm_le p a k R ha hai hk i
    simpa only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,
      AngularPower.sphere_norm,mul_one] using hrR

end OQ14.ConicalSeparatedCorrection

#print axioms OQ14.ConicalSeparatedCorrection.cutCorrection_continuous
#print axioms OQ14.ConicalSeparatedCorrection.cutCorrection_compact
#print axioms OQ14.ConicalSeparatedCorrection.cutCorrection_memLp
#print axioms OQ14.ConicalSeparatedCorrection.correctionL2_ae
#print axioms OQ14.ConicalSeparatedCorrection.totalCoordinate_inner
#print axioms OQ14.ConicalSeparatedCorrection.radialCorrection_continuous
#print axioms OQ14.ConicalSeparatedCorrection.tangentCorrection_continuous
#print axioms OQ14.ConicalSeparatedCorrection.actual_gauss_pairing
#print axioms OQ14.ConicalSeparatedCorrection.cutCorrection_norm_le
#print axioms OQ14.ConicalSeparatedCorrection.correction_moment_norm_le
