import ConicalCommonFixedGauge

/-! Fixed-gauge correction stability under common-material union approximation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.ConicalCommonCorrectionStability
open MeasureTheory Set Metric OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem correction_difference_bound (i : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hk : k ≠ 0) (hb : b < a i)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (d : Input) (J : Maxwell.Field)
    (hJ : ∀ j, Continuous (fun x => J x j))
    (heJ : ∀ j x, x ∈ closedBall (0 : Space) b → J x j = ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x)
    (hKR : UnionFreeRunge.balls center a ⊆ closedBall (0 : Space) R) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ j x, x ∈ closedBall (0 : Space) b →
      ‖(ConicalCommonFixedGauge.system p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk hb hfreq hR hai d J hJ heJ).correction j x -
        (ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k b hR0 hk hb hfreq hR
          (fun j => (hR j).trans (closedBall_subset_closedBall hRT)) hai).correction j x‖ ≤
      C*‖ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR ((hR i).trans (closedBall_subset_closedBall hRT)) d‖ +
      D*‖ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) -
        ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ := by
  have hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T :=
    fun j => (hR j).trans (closedBall_subset_closedBall hRT)
  obtain ⟨C,hC,herr⟩ := ConicalCommonErrorNorm.uniform_error_bound p a center ha hsep i R T k b hk hb hKR (hR i) (hT i) hai
  let D := k^2 * ‖StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)‖ *
    ‖ScalarPotentialBound.cutoff 0 ((max b 0 + ‖center i‖)+T)‖
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  refine ⟨C,D,hC,hD,?_⟩
  intro j x hx
  have hx' : x+center i ∈ closedBall (0 : Space) (max b 0+‖center i‖) := by
    have hxnorm : ‖x‖ ≤ b := by simpa using hx
    simp only [mem_closedBall, dist_zero_right]
    exact (norm_add_le x (center i)).trans (add_le_add_right (hxnorm.trans (le_max_left _ _)) _)
  have hw := ConicalResponseLinear.correction_difference_bound k (max b 0+‖center i‖) T
    (ConicalCommonFixedGauge.totalSource p a center B hB hcontrast ha hsep i R k d)
    (ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k)
    (ConicalCommonFixedGauge.source p a center B hB hcontrast ha hsep i R k d)
    (ConicalCommonResponse.source p a center B hB hcontrast ha hsep i R T k)
    (ConicalCommonFixedGauge.source_ae p a center B hB hcontrast ha hsep i R k d)
    (ConicalCommonResponse.source_ae p a center B hB hcontrast ha hsep i R T k)
    (ConicalCommonFixedGauge.source_zero_outer p a center B hB hcontrast ha hsep i R T k hRT hR d)
    (ConicalCommonResponse.source_zero_outer p a center B hB hcontrast ha hsep i R T k T hT) j (x+center i) hx'
  have hsrc : ‖physicalCoordinate (ConicalCommonFixedGauge.totalSource p a center B hB hcontrast ha hsep i R k d -
      ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k) j‖ ≤
      ‖StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)‖ *
      ‖ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) -
        ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ := by
    apply (DynamicConvolution.component_norm j _).trans
    have he : ConicalCommonFixedGauge.totalSource p a center B hB hcontrast ha hsep i R k d -
        ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k =
      StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
        (ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) -
          ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k) := by
      simp only [ConicalCommonFixedGauge.totalSource, ConicalCommonResponse.totalSource,
        ConicalCommonEntire.polarization, map_sub]
      abel
    rw [he]
    exact (StaticCoefficient.sqrtMultiplier _).le_opNorm _
  have hw' : ‖ElectricPotentialDecomposition.correction k (ConicalCommonFixedGauge.source p a center B hB hcontrast ha hsep i R k d) (x+center i) j -
      ElectricPotentialDecomposition.correction k (ConicalCommonResponse.source p a center B hB hcontrast ha hsep i R T k) (x+center i) j‖ ≤
      D*‖ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) -
        ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ := by
    exact hw.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsrc (sq_nonneg k)) (norm_nonneg _)).trans_eq (by dsimp [D]; ring))
  change ‖ConicalGradientGraph.bump (p i).cutoff x * (J x j + ElectricPotentialDecomposition.correction k
    (ConicalCommonFixedGauge.source p a center B hB hcontrast ha hsep i R k d) (x+center i) j) -
      ConicalGradientGraph.bump (p i).cutoff x * ElectricPotentialDecomposition.correction k
        (ConicalCommonResponse.source p a center B hB hcontrast ha hsep i R T k) (x+center i) j‖ ≤ _
  have hinner : x ∈ ball (0 : Space) (p i).cutoff.rIn := closedBall_subset_ball (hb.trans (hai i)) hx
  rw [(ConicalGradientGraph.bump_inner (p i).cutoff x hinner).1, one_mul, one_mul, heJ j x hx]
  have heq : ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x +
      ElectricPotentialDecomposition.correction k (ConicalCommonFixedGauge.source p a center B hB hcontrast ha hsep i R k d) (x+center i) j -
      ElectricPotentialDecomposition.correction k (ConicalCommonResponse.source p a center B hB hcontrast ha hsep i R T k) (x+center i) j =
      ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x +
        (ElectricPotentialDecomposition.correction k (ConicalCommonFixedGauge.source p a center B hB hcontrast ha hsep i R k d) (x+center i) j -
          ElectricPotentialDecomposition.correction k (ConicalCommonResponse.source p a center B hB hcontrast ha hsep i R T k) (x+center i) j) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (herr d j x hx) hw')

end OQ14.ConicalCommonCorrectionStability
#print axioms OQ14.ConicalCommonCorrectionStability.correction_difference_bound
