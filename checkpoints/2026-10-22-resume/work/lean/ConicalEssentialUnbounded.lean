import ConicalRadialUnbounded
import PolarMomentBound

/-! Genuine positive-frequency conical Maxwell fields are not essentially bounded at the tip. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalEssentialUnbounded
open MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalPotentialGraph OQ14.ConicalPotentialSplit OQ14.ConicalMomentIdentities
  OQ14.ConicalProjectedDerivative OQ14.PolarMomentTesting
open scoped Topology
abbrev Space := Maxwell.Space

theorem bounded_field_projection (p : Data) (k R M : ℝ) (hRR : R ≤ p.cutoff.rIn) (hM : 0 ≤ M)
    (hE : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖ConicalSpatialMaxwell.electric p k x‖ ≤ M) :
    ∃ N : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖projected p k r‖ ≤ N*r := by
  have hW : Continuous (fun x : Space => correction p k x) := continuous_pi (fun i => correction_continuous p k i)
  obtain ⟨CW,hCW⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hW.continuousOn
  let B := M+max CW 0
  have hB : 0 ≤ B := add_nonneg hM (le_max_right _ _)
  have hg (i : Fin 3) : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖gradient p k i x‖ ≤ B := by
    filter_upwards [ae_restrict_of_ae (gradient_ae p k i),hE,ae_restrict_mem measurableSet_ball] with x hx he hm
    have hi : x ∈ ball (0 : Space) p.cutoff.rIn := ball_subset_ball hRR hm
    rw [hx,(bump_inner p x hi).1,(bump_inner p x hi).2 i,one_mul,zero_mul,add_zero]
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
      ‖moment (gradient p k i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r‖ ≤ D :=
    PolarMomentBound.moment_bound_ae _ R B C hB _ (hσ i) (hg i)
  refine ⟨3*D/p.eigenvalue,?_⟩
  filter_upwards [ae_all_iff.mpr hm,ae_restrict_mem measurableSet_Ioo] with r hr hp
  have hsum : ‖tangentMoment p k r‖ ≤ 3*D := by
    calc
      _ ≤ ∑ i : Fin 3, ‖moment (gradient p k i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, D := Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  simp only [projected,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hp.1,abs_of_pos (eigenvalue_pos p)]
  exact (mul_le_mul_of_nonneg_left hsum (div_nonneg hp.1.le (eigenvalue_pos p).le)).trans_eq (by ring)

theorem positive_frequency_electric_not_essentially_bounded (p : Data) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ p.cutoff.rIn →
      ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖ConicalSpatialMaxwell.electric p k x‖ ≤ M := by
  obtain ⟨δ,hδ,hb⟩ := ConicalRadialUnbounded.positive_frequency_projection_unbounded_on p hν
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd R hR hRR
  rintro ⟨M,hM⟩
  have hE : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖ConicalSpatialMaxwell.electric p k x‖ ≤ max M 0 :=
    hM.mono (fun x hx => hx.trans (le_max_left _ _))
  obtain ⟨N,hN⟩ := bounded_field_projection p k R (max M 0) hRR (le_max_right _ _) hE
  exact hb k hk hkd R hR hRR ⟨N,hN⟩

end OQ14.ConicalEssentialUnbounded

#print axioms OQ14.ConicalEssentialUnbounded.bounded_field_projection
#print axioms OQ14.ConicalEssentialUnbounded.positive_frequency_electric_not_essentially_bounded
