import MaxwellFarField

/-! # Actual radial power in the outgoing Maxwell far field -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.FarFieldPower

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.GreenKernel
  OQ14.MaxwellRadiation OQ14.MaxwellFarField
open scoped Topology ComplexConjugate

def radialPower (n : Space) (E H : Vector) : ℝ :=
  (dot (direction n) (crossProduct E (conjugate H))).re / 2

theorem direction_conjugate (n : Space) (i : Fin 3) :
    conj (direction n i) = direction n i := by
  simp [direction, unitCoordinate]

theorem transverse_power_identity (d E : Vector)
    (hd : ∀ i, conj (d i) = d i) :
    dot d (crossProduct E (conjugate (crossProduct d E))) =
      dot d d * dot E (conjugate E) - dot d E * dot d (conjugate E) := by
  simp only [dot, cross_apply, conjugate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, map_sub, map_mul, hd]
  ring

theorem amplitude_power (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) (hn : ‖n‖ = 1) :
    radialPower n (electricAmplitude k ρ n) (magneticAmplitude k ρ n) =
      energy (electricAmplitude k ρ n) / 2 := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  unfold radialPower
  rw [← amplitude_tangential_relation, transverse_power_identity _ _ (direction_conjugate n),
    direction_dot n hn0, amplitude_transverse k ρ n hn, dot_conjugate,
    one_mul, zero_mul, sub_zero, Complex.ofReal_re]

theorem radialPower_smul (n : Space) (E H : Vector) (a : ℂ) :
    radialPower n (a • E) (a • H) = Complex.normSq a * radialPower n E H := by
  have he : dot (direction n) (crossProduct (a • E) (conjugate (a • H))) =
      (a * conj a) * dot (direction n) (crossProduct E (conjugate H)) := by
    simp only [dot, cross_apply, conjugate, Pi.smul_apply, smul_eq_mul, map_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    ring
  unfold radialPower
  rw [he, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem radialPower_continuous (n : Space) :
    Continuous (fun p : Vector × Vector => radialPower n p.1 p.2) := by
  have hc (i : Fin 3) : Continuous (fun p : Vector × Vector => conj (p.2 i)) :=
    Complex.continuous_conj.comp ((continuous_apply i).comp continuous_snd)
  unfold radialPower dot conjugate
  simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons]
  fun_prop

theorem energy_nonnegative (v : Vector) : 0 ≤ energy v :=
  add_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (Complex.normSq_nonneg _)

theorem energy_zero_iff (v : Vector) : energy v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h0 := Complex.normSq_nonneg (v 0)
    have h1 := Complex.normSq_nonneg (v 1)
    have h2 := Complex.normSq_nonneg (v 2)
    unfold energy at h
    have hz0 : v 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have hz1 : v 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have hz2 : v 2 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2
  · rintro rfl
    simp [energy]

theorem amplitude_power_nonnegative (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (n : Space) (hn : ‖n‖ = 1) :
    0 ≤ radialPower n (electricAmplitude k ρ n) (magneticAmplitude k ρ n) := by
  rw [amplitude_power k ρ n hn]
  exact div_nonneg (energy_nonnegative _) (by norm_num)

/-- The actual outgoing electric and magnetic fields have nonnegative
limiting radial power, equal to half the squared electric far-field norm. -/
theorem actual_radial_power_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => r^2 *
      radialPower n (ExteriorContinuity.electric k ρ (r • n))
        (MagneticResponse.magnetic k ρ (r • n))) atTop
      (𝓝 (energy (electricAmplitude k ρ n) / 2)) := by
  have he := electric_far_vector_limit k R hR ρ hρ hc n hn
  have hh := magnetic_far_vector_limit k R hR ρ hρ hc n hn
  have ht := ((radialPower_continuous n).tendsto
    (electricAmplitude k ρ n, magneticAmplitude k ρ n)).comp (he.prodMk_nhds hh)
  rw [amplitude_power k ρ n hn] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp only [Function.comp_def, radialPower_smul]
  rw [Complex.normSq_eq_norm_sq, factor_norm k r hr]

end OQ14.FarFieldPower

#print axioms OQ14.FarFieldPower.direction_conjugate
#print axioms OQ14.FarFieldPower.transverse_power_identity
#print axioms OQ14.FarFieldPower.amplitude_power
#print axioms OQ14.FarFieldPower.radialPower_smul
#print axioms OQ14.FarFieldPower.radialPower_continuous
#print axioms OQ14.FarFieldPower.energy_nonnegative
#print axioms OQ14.FarFieldPower.energy_zero_iff
#print axioms OQ14.FarFieldPower.amplitude_power_nonnegative
#print axioms OQ14.FarFieldPower.actual_radial_power_limit
