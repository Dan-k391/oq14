import ConicalProjectionData
import ConicalParticularBounds

/-! Actual quantitative correction bounds for arbitrary spatial projection systems. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalLocalBounds
open MeasureTheory Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalProjectionData OQ14.ConicalMomentWeights OQ14.PolarMomentTesting
abbrev Space := Maxwell.Space

theorem uniform_bound (p : Data) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ} (s : System p a) (R M : ℝ), 0 ≤ M →
      (∀ i x, x ∈ Metric.closedBall (0 : Space) R → ‖s.correction i x‖ ≤ M) →
      ∀ r ∈ Icc (0 : ℝ) R, ‖radialCorrection s r‖ ≤ M*C ∧ ‖tangentCorrection s r‖ ≤ M*C := by
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
  let D := Cw*(angularMeasure univ).toReal
  have hD : 0 ≤ D := mul_nonneg hCw ENNReal.toReal_nonneg
  refine ⟨3*D,mul_nonneg (by norm_num) hD,?_⟩
  intro a s R M hM hW r hr
  have hb (σ : Fin 3 → Sphere → ℂ) (hσ : ∀ i n, ‖σ i n‖ ≤ Cw) :
      ‖∑ i : Fin 3, moment (s.correction i) (σ i) r‖ ≤ M*(3*D) := by
    calc
      _ ≤ ∑ i : Fin 3, ‖moment (s.correction i) (σ i) r‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, M*D := Finset.sum_le_sum (fun i _ =>
        (correction_moment_norm_le s R M hM hW i (σ i) Cw (hσ i) r hr.1 hr.2).trans_eq (by dsimp only [D]; ring))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  exact ⟨hb _ hrb,hb _ htb⟩

theorem particular_bound (p : Data) (hν : p.exponent < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ} (s : System p a) (R M : ℝ), 0 ≤ M →
      (∀ i x, x ∈ Metric.closedBall (0 : Space) R → ‖s.correction i x‖ ≤ M) →
      ∀ r ∈ Ioc (0 : ℝ) R,
      ‖ConicalRadialParticular.particular p.exponent (radialCorrection s) (tangentCorrection s) r‖ ≤ C*M*r := by
  obtain ⟨C,hC,hb⟩ := uniform_bound p
  have hK : 0 ≤ ConicalParticularBounds.constant p.exponent := by
    dsimp only [ConicalParticularBounds.constant]
    exact add_nonneg (div_nonneg (by linarith [p.exponent_pos]) (by linarith)) (by norm_num)
  refine ⟨ConicalParticularBounds.constant p.exponent*C,mul_nonneg hK hC,?_⟩
  intro a s R M hM hW r hr
  apply (ConicalParticularBounds.particular_norm_le p.exponent ⟨p.exponent_pos,hν⟩
    (radialCorrection s) (tangentCorrection s) (radialCorrection_continuous s).continuousOn
    (tangentCorrection_continuous s).continuousOn r (M*C) hr.1 (mul_nonneg hM hC)
    (fun t ht => hb s R M hM hW t ⟨ht.1.le,ht.2.le.trans hr.2⟩)).trans_eq
  ring

end OQ14.ConicalLocalBounds

#print axioms OQ14.ConicalLocalBounds.uniform_bound
#print axioms OQ14.ConicalLocalBounds.particular_bound
