import ConicalCorrectionMoments
import ConicalParticularBounds

/-! Actual uniform quadratic-frequency bounds for radial forcing and its particular solution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ConicalCorrectionBounds
open MeasureTheory Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalCorrectionMoments OQ14.ConicalMomentWeights OQ14.PolarMomentTesting
abbrev Space := Maxwell.Space

theorem uniform_quadratic_bound (p : Data) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℝ,
      |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut →
      ∀ r ∈ Icc (0 : ℝ) R, ‖radialCorrection p k r‖ ≤ k^2*C ∧ ‖tangentCorrection p k r‖ ≤ k^2*C := by
  obtain ⟨Cr,hCr,hbr⟩ := scalar_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one
  obtain ⟨Ct,hCt,hbt⟩ := ConicalTangentialDivergence.weightedTangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one
  let Cw := max Cr Ct
  have hCw : 0 ≤ Cw := hCr.trans (le_max_left _ _)
  have hrb (i : Fin 3) (n : Sphere) : ‖radial p.eigenvalue p.contrast p.threshold i n‖ ≤ Cw := by
    rw [radial,norm_mul,Complex.norm_real]
    have hn : ‖(n : Space) i‖ ≤ 1 := (PiLp.norm_apply_le _ i).trans_eq (sphere_norm n)
    exact ((mul_le_mul (hbr n) hn (norm_nonneg _) hCr).trans_eq (mul_one Cr)).trans (le_max_left _ _)
  have htb (i : Fin 3) (n : Sphere) : ‖tangent p.eigenvalue p.contrast p.threshold i n‖ ≤ Cw := by
    rw [tangent_sphere,Complex.norm_real]
    exact ((PiLp.norm_apply_le _ i).trans (hbt n)).trans (le_max_right _ _)
  let S := ConicalPotentialSplit.sourceBound p*‖ScalarPotentialBound.cutoff 0 (R+p.cutoff.rOut)‖
  have hsrc : 0 ≤ ConicalPotentialSplit.sourceBound p := by
    unfold ConicalPotentialSplit.sourceBound
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (norm_nonneg _)
      (ConicalPotentialSplit.solutionConstant_nonnegative p))) (norm_nonneg _)
  have hS : 0 ≤ S := mul_nonneg hsrc (norm_nonneg _)
  let D := S*Cw*(angularMeasure univ).toReal
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hS hCw) ENNReal.toReal_nonneg
  refine ⟨3*D,mul_nonneg (by norm_num) hD,?_⟩
  intro k hk r hr
  have hb (σ : Fin 3 → Sphere → ℂ) (hσ : ∀ i n, ‖σ i n‖ ≤ Cw) :
      ‖∑ i : Fin 3, moment (cutCorrection p k i) (σ i) r‖ ≤ k^2*(3*D) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖moment (cutCorrection p k i) (σ i) r‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, k^2*D := Finset.sum_le_sum (fun i _ =>
        (correction_moment_norm_le p k R hk i (σ i) Cw (hσ i) r hr.1 hr.2).trans_eq (by dsimp only [D,S]; ring))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  exact ⟨hb _ hrb,hb _ htb⟩

theorem particular_quadratic_bound (p : Data) (hν : p.exponent < 1) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℝ,
      |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut →
      ∀ r ∈ Ioc (0 : ℝ) R,
      ‖ConicalRadialParticular.particular p.exponent (radialCorrection p k) (tangentCorrection p k) r‖ ≤ k^2*C*r := by
  obtain ⟨C,hC,hb⟩ := uniform_quadratic_bound p R
  have hK : 0 ≤ ConicalParticularBounds.constant p.exponent := by
    dsimp only [ConicalParticularBounds.constant]
    exact add_nonneg (div_nonneg (by linarith [p.exponent_pos]) (by linarith)) (by norm_num)
  refine ⟨ConicalParticularBounds.constant p.exponent*C,mul_nonneg hK hC,?_⟩
  intro k hk r hr
  apply (ConicalParticularBounds.particular_norm_le p.exponent ⟨p.exponent_pos,hν⟩
    (radialCorrection p k) (tangentCorrection p k) (radialCorrection_continuous p k).continuousOn
    (tangentCorrection_continuous p k).continuousOn r (k^2*C) hr.1 (mul_nonneg (sq_nonneg k) hC)
    (fun s hs => hb k hk s ⟨hs.1.le,hs.2.le.trans hr.2⟩)).trans_eq
  ring

end OQ14.ConicalCorrectionBounds

#print axioms OQ14.ConicalCorrectionBounds.uniform_quadratic_bound
#print axioms OQ14.ConicalCorrectionBounds.particular_quadratic_bound
