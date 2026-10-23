import ConicalSeparatedRetention
import ConicalRadialUnbounded
import PolarMomentBound

/-! Actual separated-source positive-frequency fields have no essential bound in any tip ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalSeparatedHotspot
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalSeparatedCorrection OQ14.ConicalRadialParticular OQ14.ConicalGraphProjection OQ14.PolarMomentTesting
open scoped Topology
abbrev Space := Maxwell.Space

theorem projected_not_linear_bounded_on (p : Data) (a : ℝ) (ha : 0 < a) (hai : a < p.cutoff.rIn) (hν : p.exponent < 1) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (c : ℂ) (hc : c≠0)
    (he : projected p (ConicalGradientGraph.separated p a k hai) =ᵐ[volume.restrict (Ioo (0 : ℝ) a)] fun r =>
      c*power p.exponent r+particular p.exponent (radialCorrection p a k) (tangentCorrection p a k) r) :
    ∀ R : ℝ, 0 < R → R ≤ a →
    ¬∃ M : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖projected p (ConicalGradientGraph.separated p a k hai) r‖ ≤ M*r := by
  intro R hR hRR
  rintro ⟨M,hM⟩
  obtain ⟨C,_,hb⟩ := ConicalSeparatedBounds.particular_quadratic_bound p a ha.le hai hν R
  apply ConicalRadialUnbounded.nonzero_power_not_linear_bounded p.exponent R ⟨p.exponent_pos,hν⟩ hR c hc
    (particular p.exponent (radialCorrection p a k) (tangentCorrection p a k))
    (fun r hr => (particular_hasDerivAt _ ⟨p.exponent_pos,hν⟩ _ _
      (radialCorrection_continuous p a k hai).continuousOn (tangentCorrection_continuous p a k hai).continuousOn r hr.1).continuousAt.continuousWithinAt)
    (k^2*C) (fun r hr => hb k hk r ⟨hr.1,hr.2.le⟩)
  refine ⟨M,?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (show Ioo (0 : ℝ) R ⊆ Ioo (0 : ℝ) a from fun r hr => ⟨hr.1,hr.2.trans_le hRR⟩) he,hM] with r hr hm
  rwa [hr] at hm

theorem positive_frequency_projection_unbounded_on (p : Data) (a : ℝ) (ha : 0 < a) (hai : a < p.cutoff.rIn) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ a →
      ¬∃ M : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖projected p (ConicalGradientGraph.separated p a k hai) r‖ ≤ M*r := by
  obtain ⟨δ,hδ,hb⟩ := ConicalSeparatedRetention.positive_frequency_nonzero_coefficient p a ha hai hν
  refine ⟨min δ (DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a),
    lt_min hδ (DynamicStaticLimit.frequencyRadius_positive _ _),?_⟩
  intro k hk hkd R hR hRR
  obtain ⟨c,hc,he⟩ := hb k hk (hkd.trans_le (min_le_left _ _))
  have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  exact projected_not_linear_bounded_on p a ha hai hν k hfreq c hc he R hR hRR
theorem bounded_field_projection (p : Data) (a k R M : ℝ) (hai : a < p.cutoff.rIn) (hRR : R ≤ a) (hM : 0 ≤ M)
    (hE : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖ConicalSeparatedMaxwell.electric p a k x‖ ≤ M) :
    ∃ N : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖projected p (ConicalGradientGraph.separated p a k hai) r‖ ≤ N*r := by
  have hW : Continuous (fun x : Space => ConicalSeparatedPotential.correction p a k x) := continuous_pi (fun i => ConicalSeparatedPotential.correction_continuous p a k hai i)
  obtain ⟨CW,hCW⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hW.continuousOn
  let B := M+max CW 0
  have hB : 0 ≤ B := add_nonneg hM (le_max_right _ _)
  have hg (i : Fin 3) : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖(ConicalGradientGraph.separated p a k hai).gradient i x‖ ≤ B := by
    filter_upwards [ae_restrict_of_ae (ConicalGradientGraph.separated_gradient_ae p a k hai i),hE,ae_restrict_mem measurableSet_ball] with x hx he hm
    have hi : x ∈ ball (0 : Space) p.cutoff.rIn := ball_subset_ball (hRR.trans hai.le) hm
    rw [hx,(ConicalGradientGraph.bump_inner p.cutoff x hi).1,(ConicalGradientGraph.bump_inner p.cutoff x hi).2 i,one_mul,zero_mul,add_zero]
    apply (norm_sub_le _ _).trans
    exact add_le_add ((norm_le_pi_norm _ i).trans he)
      (((norm_le_pi_norm _ i).trans (hCW x (ball_subset_closedBall hm))).trans (le_max_left _ _))
  obtain ⟨C,hC,hb⟩ := ConicalTangentialDivergence.weightedTangent_bound p.eigenvalue p.contrast p.threshold
    p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one
  have hσ (i : Fin 3) (n : Sphere) : ‖ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i n‖ ≤ C := by
    rw [ConicalMomentWeights.tangent_sphere,Complex.norm_real]
    exact (PiLp.norm_apply_le _ i).trans (hb n)
  let D := B*C*(angularMeasure univ).toReal
  have hm (i : Fin 3) : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R),
      ‖moment ((ConicalGradientGraph.separated p a k hai).gradient i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r‖ ≤ D :=
    PolarMomentBound.moment_bound_ae _ R B C hB _ (hσ i) (hg i)
  refine ⟨3*D/p.eigenvalue,?_⟩
  filter_upwards [ae_all_iff.mpr hm,ae_restrict_mem measurableSet_Ioo] with r hr hp
  have hsum : ‖ConicalGraphMoments.tangentMoment p (ConicalGradientGraph.separated p a k hai) r‖ ≤ 3*D := by
    calc
      _ ≤ ∑ i : Fin 3, ‖moment ((ConicalGradientGraph.separated p a k hai).gradient i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, D := Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  simp only [projected,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hp.1,abs_of_pos (eigenvalue_pos p)]
  exact (mul_le_mul_of_nonneg_left hsum (div_nonneg hp.1.le (eigenvalue_pos p).le)).trans_eq (by ring)

theorem positive_frequency_electric_not_essentially_bounded (p : Data) (a : ℝ) (ha : 0 < a) (hai : a < p.cutoff.rIn) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ a →
      ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖ConicalSeparatedMaxwell.electric p a k x‖ ≤ M := by
  obtain ⟨δ,hδ,hb⟩ := positive_frequency_projection_unbounded_on p a ha hai hν
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd R hR hRR
  rintro ⟨M,hM⟩
  have hE : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖ConicalSeparatedMaxwell.electric p a k x‖ ≤ max M 0 :=
    hM.mono (fun x hx => hx.trans (le_max_left _ _))
  obtain ⟨N,hN⟩ := bounded_field_projection p a k R (max M 0) hai hRR (le_max_right _ _) hE
  exact hb k hk hkd R hR hRR ⟨N,hN⟩

end OQ14.ConicalSeparatedHotspot

#print axioms OQ14.ConicalSeparatedHotspot.projected_not_linear_bounded_on
#print axioms OQ14.ConicalSeparatedHotspot.positive_frequency_projection_unbounded_on
#print axioms OQ14.ConicalSeparatedHotspot.bounded_field_projection
#print axioms OQ14.ConicalSeparatedHotspot.positive_frequency_electric_not_essentially_bounded
