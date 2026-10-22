import StaticSphereForcing
import StaticSphereResidual

/-! # Actual sphere volume and explicit perturbation scaling -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticSphereScale

open MeasureTheory Metric Set StaticBallNewton StaticSphereMaterial
  ParityReactionVolume
open scoped Topology BigOperators

def volumeConstant (ρ : ℝ) : ℝ := ρ^3*(Real.pi*4/3)

theorem volumeConstant_nonnegative (ρ : ℝ) (hρ : 0 ≤ ρ) : 0 ≤ volumeConstant ρ := by
  unfold volumeConstant
  positivity

theorem scaled_ball_volume (c : Space) (ρ a : ℝ) (hρ : 0 ≤ ρ) (ha : 0 ≤ a) :
    volume.real (ball c (ρ*a)) = volumeConstant ρ*a^3 := by
  simp only [measureReal_def, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg hρ ha),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  unfold volumeConstant
  ring

theorem sqrt_scaled_ball_volume (c : Space) (ρ a : ℝ) (hρ : 0 ≤ ρ) (ha : 0 ≤ a) :
    Real.sqrt (volume.real (ball c (ρ*a))) = Real.sqrt (volumeConstant ρ)*a*Real.sqrt a := by
  rw [scaled_ball_volume c ρ a hρ ha,
    Real.sqrt_mul (volumeConstant_nonnegative ρ hρ)]
  rw [show a^3=a^2*a by ring, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
    abs_of_nonneg ha]
  ring

theorem trial_component_bound (χ : ℝ) (hχ : 0 ≤ χ) (E : Vector) (i : Fin 3) :
    ‖trialVector χ E i‖ ≤ Real.sqrt χ * ‖E i‖ := by
  have hd : 0 < χ+3 := by linarith
  have hc : 0 ≤ 3*Real.sqrt χ/(χ+3) := by positivity
  change ‖((3*Real.sqrt χ/(χ+3) : ℝ) : ℂ)*E i‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ hd).mpr
  nlinarith [Real.sqrt_nonneg χ]

theorem trial_norm_bound (c : Space) (R χ : ℝ) (hχ : 0 ≤ χ) (E : Vector) :
    ‖trial c R χ E‖ ≤ (Real.sqrt χ * (∑ i : Fin 3, ‖E i‖)) *
      Real.sqrt (volume.real (ball (0 : Space) R)) := by
  apply (StaticSphereForcing.source_norm_le c R (trialVector χ E)).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => trial_component_bound χ hχ E i)

def linearBound (χ V k R b : ℝ) : ℝ :=
  χ*Real.sqrt V*DynamicSupportVolume.kernelSize k R +
    (9*χ*V*SphereReactionKernel.entryBound k)*(b^2+2+1/b^2)

theorem linearBound_nonnegative (χ V k R b : ℝ) (hχ : 0 ≤ χ) (hV : 0 ≤ V) :
    0 ≤ linearBound χ V k R b := by
  have hk := DynamicSupportVolume.kernelSize_nonnegative k R
  have he := SphereReactionKernel.entryBound_nonnegative k
  unfold linearBound
  positivity

theorem explicitBound_linear (χ V k R b a : ℝ) (hχ : 0 ≤ χ) (hV : 0 ≤ V)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    SmallParityInclusions.explicitBound χ V k R b a ≤ linearBound χ V k R b*a := by
  have h3 : a^3 ≤ a := by
    calc
      a^3 = a*a^2 := by ring
      _ ≤ a*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ha ha1) ha
      _ = a := mul_one _
  have h5 : a^5 ≤ a := by
    calc
      a^5 = a*a^4 := by ring
      _ ≤ a*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ha ha1) ha
      _ = a := mul_one _
  have hs : Real.sqrt (V*a^3) ≤ Real.sqrt V*a := by
    have h32 : a^3 ≤ a^2 := by
      have hh := mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
      nlinarith
    apply (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h32 hV)).trans_eq
    rw [Real.sqrt_mul hV, Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  have ht : b^2*a+2*a^3+a^5/b^2 ≤ (b^2+2+1/b^2)*a := by
    have hh := div_le_div_of_nonneg_right h5 (sq_nonneg b)
    calc
      _ ≤ b^2*a+2*a+a/b^2 := add_le_add
        (add_le_add_left (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 2)) _) hh
      _ = _ := by ring
  have he := SphereReactionKernel.entryBound_nonnegative k
  unfold SmallParityInclusions.explicitBound linearBound
  apply (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hχ)
      (DynamicSupportVolume.kernelSize_nonnegative k R))
    (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 9*χ*V*SphereReactionKernel.entryBound k))).trans_eq
  ring

theorem perturbation_linear {c : StaticCoefficient.Coefficient} (d : SupportData c)
    (χ V k b a : ℝ) (hχ : 0 ≤ χ) (hV : 0 ≤ V) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : b ≠ 0) (hc : c.bound ≤ χ) (hv : volume.real d.carrier ≤ V*a^3) :
    perturbationBound d k (b/a) ≤ linearBound χ V k d.radius b*a :=
  (SmallParityInclusions.scaled_perturbation_bound d k b a χ V ha hb hχ hc hv).trans
    (explicitBound_linear χ V k d.radius b a hχ hV ha.le ha1)

theorem linear_smallness (K : ℝ) (hK : 0 ≤ K) :
    ∃ δ > 0, ∀ a : ℝ, 0 ≤ a → a < δ → K*a < 1/2 := by
  refine ⟨(2*(K+1))⁻¹, by positivity, ?_⟩
  intro a ha had
  have hh := (mul_lt_mul_of_pos_left had (by positivity : 0 < 2*(K+1)))
  have hn : 2*(K+1) ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hn] at hh
  nlinarith

end OQ14.StaticSphereScale

#print axioms OQ14.StaticSphereScale.volumeConstant_nonnegative
#print axioms OQ14.StaticSphereScale.scaled_ball_volume
#print axioms OQ14.StaticSphereScale.sqrt_scaled_ball_volume
#print axioms OQ14.StaticSphereScale.trial_component_bound
#print axioms OQ14.StaticSphereScale.trial_norm_bound
#print axioms OQ14.StaticSphereScale.linearBound_nonnegative
#print axioms OQ14.StaticSphereScale.explicitBound_linear
#print axioms OQ14.StaticSphereScale.perturbation_linear
#print axioms OQ14.StaticSphereScale.linear_smallness
