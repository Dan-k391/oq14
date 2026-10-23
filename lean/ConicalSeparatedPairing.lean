import ConicalSeparatedBounds
import ConicalAnnularCoefficient

/-! Actual annular coefficient functional of the separated physical family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalSeparatedPairing
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalSeparatedCorrection OQ14.ConicalTangentialDivergence OQ14.PolarMomentTesting
  OQ14.WeakGreen OQ14.NewtonL2 OQ14.ConicalAnnularCoefficient
open scoped Topology
abbrev Space := Maxwell.Space

def correctionPair (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : ℂ :=
  ∑ i : Fin 3, scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 p a k hai i)

def gradientPair (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : ℂ :=
  ∑ i : Fin 3, scalarProduct (testCoordinate p ζ hζ hc i) ((ConicalGradientGraph.separated p a k hai).gradient i)

theorem fieldPair_tendsto (p : Data) (a : ℝ) (ha : 0 ≤ a) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    Tendsto (fun k => fieldPair p ζ hζ hc (ConicalSeparatedDynamic.field p a k)) (𝓝 (0 : ℝ))
      (𝓝 (fieldPair p ζ hζ hc (electric p))) :=
  (fieldPair p ζ hζ hc).continuous.tendsto _ |>.comp (ConicalSeparatedDynamic.field_tendsto p a ha)

theorem gradientPair_eq (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) a) :
    gradientPair p a k hai ζ hζ hc=fieldPair p ζ hζ hc (ConicalSeparatedDynamic.field p a k)-correctionPair p a k hai ζ hζ hc := by
  have hi (i : Fin 3) : scalarProduct (testCoordinate p ζ hζ hc i) ((ConicalGradientGraph.separated p a k hai).gradient i)=
      scalarProduct (testCoordinate p ζ hζ hc i) (physicalCoordinate (ConicalSeparatedDynamic.field p a k) i)-
      scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 p a k hai i) := by
    rw [← map_sub,scalarProduct_integral,scalarProduct_integral]
    apply integral_congr_ae
    filter_upwards [tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i,
      ConicalGradientGraph.separated_gradient_ae p a k hai i,correctionL2_ae p a k hai i,
      Lp.coeFn_sub (physicalCoordinate (ConicalSeparatedDynamic.field p a k) i) (correctionL2 p a k hai i),
      ae_imp_of_ae_restrict (ConicalSeparatedMaxwell.field_ae p a k hai i)] with x ht hg hw ha hf
    change testCoordinate p ζ hζ hc i x*(ConicalGradientGraph.separated p a k hai).gradient i x=_
    dsimp only [testCoordinate]
    rw [ht,hg,ha]
    simp only [Pi.sub_apply]
    by_cases hx : x ∈ ball (0 : Space) a
    · have hxo : x ∈ closedBall (0 : Space) a := by
        simp only [mem_ball,dist_zero_right] at hx
        simpa only [mem_closedBall,dist_zero_right] using hx.le
      rw [(ConicalGradientGraph.bump_inner p.cutoff x (ball_subset_ball hai.le hx)).1,(ConicalGradientGraph.bump_inner p.cutoff x (ball_subset_ball hai.le hx)).2 i,hf hxo,hw]
      simp only [Pi.sub_apply,cutCorrection,(ConicalGradientGraph.bump_inner p.cutoff x (ball_subset_ball hai.le hx)).1,one_mul,zero_mul,add_zero]
    · have hz : ζ ‖x‖=0 := image_eq_zero_of_nmem_tsupport (fun h => hx (by
        simpa only [mem_ball,dist_zero_right] using (hs h).2))
      simp only [tangentField,hz,zero_mul,Complex.ofReal_zero,mul_zero]
  simp only [gradientPair,fieldPair_apply,correctionPair,hi,Finset.sum_sub_distrib]

theorem correctionPair_norm_le (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn)
    (ha : 0 ≤ a) (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    ‖correctionPair p a k hai ζ hζ hc‖ ≤
      (k^2*ConicalSeparatedPotential.sourceBound p a*‖ScalarPotentialBound.cutoff 0 (p.cutoff.rOut+p.cutoff.rOut)‖)*testMass p ζ := by
  let M := k^2*ConicalSeparatedPotential.sourceBound p a*‖ScalarPotentialBound.cutoff 0 (p.cutoff.rOut+p.cutoff.rOut)‖
  have hb (i : Fin 3) (x : Space) : ‖cutCorrection p a k i x‖ ≤ M := by
    by_cases hx : x ∈ closedBall (0 : Space) p.cutoff.rOut
    · exact cutCorrection_norm_le p a k _ ha hai hk i x hx
    · have hz : p.cutoff x=0 := p.cutoff.zero_of_le_dist (le_of_lt (not_le.mp hx))
      have hM : 0 ≤ M := (norm_nonneg _).trans (cutCorrection_norm_le p a k _ ha hai hk i 0
        (by simp only [mem_closedBall,dist_self]; exact p.cutoff.rOut_pos.le))
      simpa only [cutCorrection,ConicalGradientGraph.bump,hz,Complex.ofReal_zero,zero_mul,norm_zero] using hM
  have hi (i : Fin 3) : ‖scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 p a k hai i)‖ ≤
      M*(∫ x : Space, ‖(tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)‖) := by
    rw [scalarProduct_integral]
    have he : (∫ x : Space, testCoordinate p ζ hζ hc i x*correctionL2 p a k hai i x)=
        ∫ x : Space, (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)*cutCorrection p a k i x := by
      apply integral_congr_ae
      filter_upwards [tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i,
        correctionL2_ae p a k hai i] with x ht hw
      exact congrArg₂ (fun a b : ℂ => a*b) ht hw
    rw [he,← integral_const_mul]
    apply norm_integral_le_of_norm_le ((test_integrable p ζ hζ hc i).norm.const_mul M)
    filter_upwards with x
    rw [norm_mul,mul_comm M]
    exact mul_le_mul_of_nonneg_left (hb i x) (norm_nonneg _)
  calc
    ‖correctionPair p a k hai ζ hζ hc‖ ≤ ∑ i : Fin 3, ‖scalarProduct (testCoordinate p ζ hζ hc i) (correctionL2 p a k hai i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, M*(∫ x : Space, ‖(tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)‖) := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [testMass,Finset.mul_sum,M]

theorem correctionPair_tendsto (p : Data) (a : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    Tendsto (fun k => correctionPair p a k hai ζ hζ hc) (𝓝 (0 : ℝ)) (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have he : ∀ᶠ k : ℝ in 𝓝 0, |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (DynamicStaticLimit.frequencyRadius_positive (ConicalSeparatedSource.material p a) a)] with k hk
    have ht : |k| < DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a := by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hk
    exact ht.le
  have hl : Tendsto (fun k : ℝ => (k^2*ConicalSeparatedPotential.sourceBound p a*‖ScalarPotentialBound.cutoff 0 (p.cutoff.rOut+p.cutoff.rOut)‖)*testMass p ζ)
      (𝓝 0) (𝓝 0) := by
    simpa using ((((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 (0 : ℝ)) (𝓝 0)).pow 2).mul_const (ConicalSeparatedPotential.sourceBound p a)).mul_const
      ‖ScalarPotentialBound.cutoff 0 (p.cutoff.rOut+p.cutoff.rOut)‖).mul_const (testMass p ζ)
  exact squeeze_zero' (Filter.Eventually.of_forall (fun k => norm_nonneg _))
    (he.mono (fun k hk => correctionPair_norm_le p a k hai ha hk ζ hζ hc)) hl

theorem gradientPair_tendsto (p : Data) (a : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) a) :
    Tendsto (fun k => gradientPair p a k hai ζ hζ hc) (𝓝 (0 : ℝ)) (𝓝 (fieldPair p ζ hζ hc (electric p))) := by
  simpa only [sub_zero] using ((fieldPair_tendsto p a ha ζ hζ hc).sub (correctionPair_tendsto p a ha hai ζ hζ hc)).congr'
    (Filter.Eventually.of_forall (fun k => (gradientPair_eq p a k hai ζ hζ hc hs).symm))

end OQ14.ConicalSeparatedPairing

#print axioms OQ14.ConicalSeparatedPairing.fieldPair_tendsto
#print axioms OQ14.ConicalSeparatedPairing.gradientPair_eq
#print axioms OQ14.ConicalSeparatedPairing.correctionPair_norm_le
#print axioms OQ14.ConicalSeparatedPairing.correctionPair_tendsto
#print axioms OQ14.ConicalSeparatedPairing.gradientPair_tendsto
