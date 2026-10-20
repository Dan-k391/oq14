import FarFieldPower
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! # Spherical outgoing power of the actual compact-source Maxwell fields -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.AngularPower

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.GreenKernel
  OQ14.KernelConvolution OQ14.ScalarRadiation OQ14.DyadicRadiation
  OQ14.MaxwellRadiation OQ14.MaxwellFarField OQ14.FarFieldPower
open scoped Topology ComplexConjugate InnerProductSpace

abbrev Sphere := Metric.sphere (0 : Space) 1

def angularMeasure : Measure Sphere := (volume : Measure Space).toSphere

instance : IsFiniteMeasure angularMeasure := inferInstanceAs
  (IsFiniteMeasure (volume : Measure Space).toSphere)

theorem sphere_norm (n : Sphere) : ‖(n : Space)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using n.property

theorem scalar_amplitude_continuous (k : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ) :
    Continuous (ScalarFarField.amplitude k ρ) := by
  apply continuous_of_dominated (bound := fun y => ‖ρ y‖ / (4 * Real.pi))
  · intro n
    apply hρ.aestronglyMeasurable.mul
    exact (by fun_prop : Continuous (fun y : Space =>
      Complex.exp (-Complex.I * k * (⟪n, y⟫_ℝ : ℝ)) / (4 * Real.pi))).aestronglyMeasurable
  · intro n
    filter_upwards with y
    simp only [norm_mul, norm_div, Complex.norm_exp]
    simp [abs_of_pos Real.pi_pos]
    ring_nf
    exact le_rfl
  · exact hρ.norm.div_const _
  · filter_upwards with y
    fun_prop

theorem direction_sphere_continuous :
    Continuous (fun n : Sphere => direction (n : Space)) := by
  apply continuous_pi
  intro i
  simp only [direction, unitCoordinate, sphere_norm, div_one]
  exact Complex.continuous_ofReal.comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp continuous_subtype_val)

theorem electric_amplitude_continuous (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) :
    Continuous (fun n : Sphere => electricAmplitude k ρ (n : Space)) := by
  have hp (i : Fin 3) : Continuous (fun n : Sphere => potentialAmplitude k ρ (n : Space) i) :=
    (scalar_amplitude_continuous k (ρ i) (hρ i)).comp continuous_subtype_val
  have hd (i : Fin 3) : Continuous (fun n : Sphere => direction (n : Space) i) :=
    (continuous_apply i).comp direction_sphere_continuous
  apply continuous_pi
  intro i
  simp only [amplitude_formula, dot]
  fun_prop

theorem scaled_potential_bound (k R r : ℝ) (hR : 0 ≤ R) (hr : 2*R < r)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    ‖factor k r * potential k ρ (r • n) i‖ ≤
      (2 / (4 * Real.pi)) * sourceMass ρ := by
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hnr : ‖r • n‖ = r := by simp [norm_smul, hn, abs_of_pos hr0]
  have hb := response_norm_bound (phi k) (ρ i) (KernelIntegrability.phi_measurable k)
    (hρ i) (r • n) ((4 * Real.pi)⁻¹ * (2/r)) (by
      intro y hy
      have hyb : y ∈ closedBall 0 R := by
        by_contra hz
        exact hy (hc i y hz)
      simpa only [hnr] using phi_source_bound k R hR (r • n) y (by rwa [hnr]) hyb)
  rw [norm_mul, factor_norm k r hr0]
  calc
    _ ≤ r * (((4 * Real.pi)⁻¹ * (2/r)) * ∫ y, ‖ρ i y‖) :=
      mul_le_mul_of_nonneg_left hb hr0.le
    _ = (2 / (4 * Real.pi)) * ∫ y, ‖ρ i y‖ := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (component_mass_le ρ i) (by positivity)

theorem scaled_leading_electric_bound (k r B : ℝ) (_hB : 0 ≤ B)
    (ρ : Fin 3 → Space → ℂ) (n : Space)
    (hA : ∀ j, ‖factor k r * potential k ρ (r • n) j‖ ≤ B) (i : Fin 3) :
    ‖factor k r * leadingElectric k ρ (r • n) i‖ ≤ 6*k^2*B := by
  have he : factor k r * leadingElectric k ρ (r • n) i =
      ∑ j : Fin 3, (k : ℂ)^2 * transverse (r • n) i j *
        (factor k r * potential k ρ (r • n) j) := by
    simp only [leadingElectric, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin 3, k^2 * 2 * B := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (transverse_norm_bound (r • n) i j) (sq_nonneg k))
        (by simpa only [norm_mul] using hA j) (by positivity) (by positivity)
    _ = _ := by simp; ring

theorem scaled_leading_magnetic_bound (k r B : ℝ) (_hB : 0 ≤ B)
    (ρ : Fin 3 → Space → ℂ) (n : Space)
    (hA : ∀ j, ‖factor k r * potential k ρ (r • n) j‖ ≤ B) (i : Fin 3) :
    ‖factor k r * leadingMagnetic k ρ (r • n) i‖ ≤ 2*k^2*B := by
  have he : factor k r * leadingMagnetic k ρ (r • n) i =
      (k : ℂ)^2 *
        (direction (r • n) (WeakCurl.next i) *
          (factor k r * potential k ρ (r • n) (WeakCurl.previous i)) -
        direction (r • n) (WeakCurl.previous i) *
          (factor k r * potential k ρ (r • n) (WeakCurl.next i))) := by
    simp only [leadingMagnetic, cross_component]
    ring
  have hd (j : Fin 3) : ‖direction (r • n) j‖ ≤ 1 := unitCoordinate_norm_le j _
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ k^2 * (‖direction (r • n) (WeakCurl.next i) *
        (factor k r * potential k ρ (r • n) (WeakCurl.previous i))‖ +
      ‖direction (r • n) (WeakCurl.previous i) *
        (factor k r * potential k ρ (r • n) (WeakCurl.next i))‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sq_nonneg k)
    _ ≤ k^2 * (1*B + 1*B) := by
      simp only [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg k)
      exact add_le_add
        (mul_le_mul (hd _) (by simpa only [norm_mul] using hA (WeakCurl.previous i))
          (by positivity) (by norm_num))
        (mul_le_mul (hd _) (by simpa only [norm_mul] using hA (WeakCurl.next i))
          (by positivity) (by norm_num))
    _ = _ := by ring

theorem scaled_error_bound (k C r : ℝ) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (f : ℂ) (hf : ‖f‖ ≤ C/r^2) : ‖factor k r * f‖ ≤ C := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [norm_mul, factor_norm k r hr0]
  calc
    _ ≤ r * (C/r^2) := mul_le_mul_of_nonneg_left hf hr0.le
    _ = C/r := by field_simp; ring
    _ ≤ C := (div_le_self hC hr)

theorem actual_fields_uniform_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, max (2*R) 2 < r →
      ∀ n : Space, ‖n‖ = 1 → ∀ i : Fin 3,
      ‖factor k r * ExteriorContinuity.electric k ρ (r • n) i‖ ≤ C ∧
      ‖factor k r * MagneticResponse.magnetic k ρ (r • n) i‖ ≤ C := by
  let B := (2 / (4 * Real.pi)) * sourceMass ρ
  let CE := 4 * (k^2 * R + |k| + 1) / Real.pi * sourceMass ρ
  let CH := 2 * |k| * (2 * |k| * R + 1) / Real.pi * sourceMass ρ
  have hB : 0 ≤ B := mul_nonneg (by positivity) (sourceMass_nonnegative ρ)
  have hCE : 0 ≤ CE := mul_nonneg (by positivity) (sourceMass_nonnegative ρ)
  have hCH : 0 ≤ CH := mul_nonneg (by positivity) (sourceMass_nonnegative ρ)
  refine ⟨6*k^2*B + CE + CH, by positivity, ?_⟩
  intro r hr n hn i
  have hrR : 2*R < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hr2 : 2 < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hnr : ‖r • n‖ = r := by simp [norm_smul, hn, abs_of_pos hr0]
  have hA := scaled_potential_bound k R r hR hrR ρ hρ hc n hn
  have he := electric_transverse_bound k R hR ρ hρ hc (r • n)
    (by rwa [hnr]) (by rw [hnr]; exact hr2.le) i
  have hh := magnetic_transverse_bound k R hR ρ hρ hc (r • n) (by rwa [hnr]) i
  rw [hnr] at he hh
  have he' : ‖ExteriorContinuity.electric k ρ (r • n) i -
      leadingElectric k ρ (r • n) i‖ ≤ CE/r^2 := by
    convert he using 1
    dsimp [CE, sourceMass]
    ring
  have hh' : ‖MagneticResponse.magnetic k ρ (r • n) i -
      leadingMagnetic k ρ (r • n) i‖ ≤ CH/r^2 := by
    convert hh using 1
    dsimp [CH]
    ring
  have hle := scaled_leading_electric_bound k r B hB ρ n hA i
  have hlh := scaled_leading_magnetic_bound k r B hB ρ n hA i
  have hde := scaled_error_bound k CE r hCE hr1 _ he'
  have hdh := scaled_error_bound k CH r hCH hr1 _ hh'
  constructor
  · have htri := norm_add_le
      (factor k r * (ExteriorContinuity.electric k ρ (r • n) i -
        leadingElectric k ρ (r • n) i))
      (factor k r * leadingElectric k ρ (r • n) i)
    rw [mul_sub, sub_add_cancel] at htri
    rw [mul_sub] at hde
    linarith
  · have htri := norm_add_le
      (factor k r * (MagneticResponse.magnetic k ρ (r • n) i -
        leadingMagnetic k ρ (r • n) i))
      (factor k r * leadingMagnetic k ρ (r • n) i)
    rw [mul_sub, sub_add_cancel] at htri
    rw [mul_sub] at hdh
    nlinarith [mul_nonneg (sq_nonneg k) hB]

theorem radialPower_bound (n : Space) (E H : Vector) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ i, ‖E i‖ ≤ C) (hH : ∀ i, ‖H i‖ ≤ C) :
    ‖radialPower n E H‖ ≤ 3*C^2 := by
  have hc (i : Fin 3) : ‖crossProduct E (conjugate H) i‖ ≤ 2*C^2 := by
    rw [cross_component]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, conjugate, Complex.norm_conj]
    have ha := mul_le_mul (hE (WeakCurl.next i)) (hH (WeakCurl.previous i))
      (norm_nonneg _) hC
    have hb := mul_le_mul (hE (WeakCurl.previous i)) (hH (WeakCurl.next i))
      (norm_nonneg _) hC
    nlinarith
  have hd (i : Fin 3) : ‖direction n i * crossProduct E (conjugate H) i‖ ≤ 2*C^2 := by
    rw [norm_mul]
    exact (mul_le_mul (unitCoordinate_norm_le i n) (hc i)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hb : ‖dot (direction n) (crossProduct E (conjugate H))‖ ≤ 6*C^2 := by
    unfold dot
    exact (norm_add_le _ _).trans
      ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith [hd 0, hd 1, hd 2]))
  unfold radialPower
  rw [norm_div]
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right
    ((Complex.abs_re_le_norm _).trans hb) (by norm_num)).trans_eq (by ring)

theorem actual_power_uniform_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, max (2*R) 2 < r → ∀ n : Sphere,
      ‖r^2 * radialPower (n : Space)
        (ExteriorContinuity.electric k ρ (r • (n : Space)))
        (MagneticResponse.magnetic k ρ (r • (n : Space)))‖ ≤ C := by
  obtain ⟨B,hB,h⟩ := actual_fields_uniform_bound k R hR ρ hρ hc
  refine ⟨3*B^2, by positivity, ?_⟩
  intro r hr n
  have hr0 : 0 < r := lt_trans (by positivity) (lt_of_le_of_lt (le_max_right _ _) hr)
  have hb := radialPower_bound (n : Space)
    (factor k r • ExteriorContinuity.electric k ρ (r • (n : Space)))
    (factor k r • MagneticResponse.magnetic k ρ (r • (n : Space))) B hB
    (fun i => (h r hr n (sphere_norm n) i).1)
    (fun i => (h r hr n (sphere_norm n) i).2)
  rwa [radialPower_smul, Complex.normSq_eq_norm_sq, factor_norm k r hr0] at hb

theorem radialPower_sphere_continuous (E H : Sphere → Vector)
    (hE : Continuous E) (hH : Continuous H) :
    Continuous (fun n : Sphere => radialPower (n : Space) (E n) (H n)) := by
  have hd (i : Fin 3) : Continuous (fun n : Sphere => direction (n : Space) i) :=
    (continuous_apply i).comp direction_sphere_continuous
  have he (i : Fin 3) : Continuous (fun n => E n i) := (continuous_apply i).comp hE
  have hh (i : Fin 3) : Continuous (fun n => conj (H n i)) :=
    Complex.continuous_conj.comp ((continuous_apply i).comp hH)
  unfold radialPower
  apply Continuous.div_const
  unfold dot conjugate
  simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons]
  exact Complex.continuous_re.comp
    ((((hd 0).mul (((he 1).mul (hh 2)).sub ((he 2).mul (hh 1)))).add
      ((hd 1).mul (((he 2).mul (hh 0)).sub ((he 0).mul (hh 2))))).add
      ((hd 2).mul (((he 0).mul (hh 1)).sub ((he 1).mul (hh 0)))))

theorem actual_fields_sphere_continuous (k R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    Continuous (fun n : Sphere => ExteriorContinuity.electric k ρ (r • (n : Space))) ∧
    Continuous (fun n : Sphere => MagneticResponse.magnetic k ρ (r • (n : Space))) := by
  have hp : 0 < r := lt_of_le_of_lt hR hr
  have hnorm (n : Sphere) : R < ‖r • (n : Space)‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hp, sphere_norm, mul_one] using hr
  have hmap : Continuous (fun n : Sphere => r • (n : Space)) :=
    continuous_const.smul continuous_subtype_val
  constructor
  · apply continuous_iff_continuousAt.mpr
    intro n
    exact (ExteriorContinuity.electric_continuousAt k ρ hρ R hc _ (hnorm n)).comp
      (f := fun n : Sphere => r • (n : Space))
      hmap.continuousAt
  · apply continuous_iff_continuousAt.mpr
    intro n
    exact (ExteriorContinuity.magnetic_continuousAt k ρ hρ R hc _ (hnorm n)).comp
      (f := fun n : Sphere => r • (n : Space))
      hmap.continuousAt

def sphericalPower (k r : ℝ) (ρ : Fin 3 → Space → ℂ) : ℝ :=
  ∫ n : Sphere, r^2 * radialPower (n : Space)
    (ExteriorContinuity.electric k ρ (r • (n : Space)))
    (MagneticResponse.magnetic k ρ (r • (n : Space))) ∂angularMeasure

def farPower (k : ℝ) (ρ : Fin 3 → Space → ℂ) : ℝ :=
  ∫ n : Sphere, energy (electricAmplitude k ρ (n : Space)) / 2 ∂angularMeasure

theorem actual_spherical_power_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    Tendsto (fun r => sphericalPower k r ρ) atTop (𝓝 (farPower k ρ)) := by
  obtain ⟨C, _, hC⟩ := actual_power_uniform_bound k R hR ρ hρ hc
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ : Sphere => C)
  · filter_upwards [eventually_gt_atTop R] with r hr
    obtain ⟨he,hh⟩ := actual_fields_sphere_continuous k R r hR hr ρ hρ hc
    exact (continuous_const.mul (radialPower_sphere_continuous _ _ he hh)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (max (2*R) 2)] with r hr
    exact Eventually.of_forall (hC r hr)
  · exact integrable_const C
  · exact Eventually.of_forall
      (fun n => actual_radial_power_limit k R hR ρ hρ hc n (sphere_norm n))

theorem farPower_nonnegative (k : ℝ) (ρ : Fin 3 → Space → ℂ) : 0 ≤ farPower k ρ :=
  integral_nonneg (fun _ => div_nonneg (energy_nonnegative _) (by norm_num))

theorem far_energy_continuous (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) :
    Continuous (fun n : Sphere => energy (electricAmplitude k ρ (n : Space)) / 2) := by
  have he (i : Fin 3) : Continuous (fun n : Sphere => electricAmplitude k ρ (n : Space) i) :=
    (continuous_apply i).comp (electric_amplitude_continuous k ρ hρ)
  unfold energy
  fun_prop

theorem farPower_zero_iff (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) :
    farPower k ρ = 0 ↔ ∀ᵐ n : Sphere ∂angularMeasure, electricAmplitude k ρ (n : Space) = 0 := by
  have hi : Integrable (fun n : Sphere =>
      energy (electricAmplitude k ρ (n : Space)) / 2) angularMeasure :=
    (far_energy_continuous k ρ hρ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [farPower, integral_eq_zero_iff_of_nonneg (fun _ =>
    div_nonneg (energy_nonnegative _) (by norm_num)) hi]
  apply eventually_congr
  filter_upwards with n
  simp only [Pi.zero_apply, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, energy_zero_iff]

end OQ14.AngularPower

#print axioms OQ14.AngularPower.sphere_norm
#print axioms OQ14.AngularPower.scalar_amplitude_continuous
#print axioms OQ14.AngularPower.direction_sphere_continuous
#print axioms OQ14.AngularPower.electric_amplitude_continuous
#print axioms OQ14.AngularPower.scaled_potential_bound
#print axioms OQ14.AngularPower.scaled_leading_electric_bound
#print axioms OQ14.AngularPower.scaled_leading_magnetic_bound
#print axioms OQ14.AngularPower.scaled_error_bound
#print axioms OQ14.AngularPower.actual_fields_uniform_bound
#print axioms OQ14.AngularPower.radialPower_bound
#print axioms OQ14.AngularPower.actual_power_uniform_bound
#print axioms OQ14.AngularPower.radialPower_sphere_continuous
#print axioms OQ14.AngularPower.actual_fields_sphere_continuous
#print axioms OQ14.AngularPower.actual_spherical_power_limit
#print axioms OQ14.AngularPower.farPower_nonnegative
#print axioms OQ14.AngularPower.far_energy_continuous
#print axioms OQ14.AngularPower.farPower_zero_iff
