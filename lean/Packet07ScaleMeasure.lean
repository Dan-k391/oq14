import Packet07PlanarPacking
import DilationL2
import FrequencyScalingMaxwell

/-! Positive-volume peak sets survive an invertible spatial dilation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07ScaleMeasure
open MeasureTheory Set

/-- Nonzero spatial dilation preserves positive measure under preimage,
    without requiring the set to be measurable. -/
theorem positive_preimage_smul (s : ℝ) (hs : s ≠ 0) (A : Set Maxwell.Space)
    (hA : 0 < volume A) : 0 < volume ((fun x : Maxwell.Space => s • x) ⁻¹' A) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have ha : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ ((fun x : Maxwell.Space => s • x) ⁻¹' A) := by
    apply ae_iff.mpr
    simpa only [not_not] using hz
  have hb := (DilationL2.smul_qmp_space s⁻¹ (inv_ne_zero hs)).ae ha
  have hc : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ A := by
    filter_upwards [hb] with x hx
    simpa only [Set.mem_preimage, smul_smul, mul_inv_cancel₀ hs, one_smul] using hx
  have hzA : volume A = 0 := by
    rw [ae_iff] at hc
    simpa only [not_not] using hc
  exact (ne_of_gt hA) hzA

/-- A positive-volume peak transfers to the corresponding scaled ball and
    power-normalized field, with its threshold scaled by the positive factor. -/
theorem positive_peak_dilation (s : ℝ) (hs : 0 < s) (c : Maxwell.Space) (r M : ℝ)
    (E : Maxwell.Field) (i : Fin 3)
    (hpeak : 0 < (volume.restrict (Metric.ball c r)) {x | M / s < ‖E x i‖}) :
    0 < (volume.restrict (Metric.ball (s⁻¹ • c) (r / s)))
      {x | M < ‖FrequencyScalingMaxwell.scaleField s E x i‖} := by
  rw [Measure.restrict_apply' measurableSet_ball] at hpeak ⊢
  have hp := positive_preimage_smul s hs.ne' ({x | M / s < ‖E x i‖} ∩ Metric.ball c r) hpeak
  have he : (fun x : Maxwell.Space => s • x) ⁻¹' ({x | M / s < ‖E x i‖} ∩ Metric.ball c r) =
      {x | M < ‖FrequencyScalingMaxwell.scaleField s E x i‖} ∩ Metric.ball (s⁻¹ • c) (r / s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_ball]
    have hd : dist (s • x) c = s * dist x (s⁻¹ • c) := by
      have hh := dist_smul₀ s x (s⁻¹ • c)
      simpa only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, Real.norm_eq_abs, abs_of_pos hs] using hh
    rw [hd]
    simp only [FrequencyScalingMaxwell.scaleField_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨by simpa only [mul_comm] using (div_lt_iff₀ hs).mp h1, (lt_div_iff₀ hs).mpr (by nlinarith)⟩
    · rintro ⟨h1,h2⟩
      exact ⟨(div_lt_iff₀ hs).mpr (by simpa only [mul_comm] using h1), by have := (lt_div_iff₀ hs).mp h2; nlinarith⟩
  rwa [he] at hp

/-- Positive measure is preserved under translation preimages. -/
theorem positive_preimage_sub (a : Maxwell.Space) (A : Set Maxwell.Space)
    (hA : 0 < volume A) : 0 < volume ((fun x : Maxwell.Space => x-a) ⁻¹' A) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have ha : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ ((fun x : Maxwell.Space => x-a) ⁻¹' A) := by
    apply ae_iff.mpr
    simpa only [not_not] using hz
  have hb := (measurePreserving_add_right (volume : Measure Maxwell.Space) a).quasiMeasurePreserving.ae ha
  have hc : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ A := by
    filter_upwards [hb] with x hx
    simpa only [Set.mem_preimage, add_sub_cancel_right] using hx
  have hzA : volume A = 0 := by
    rw [ae_iff] at hc
    simpa only [not_not] using hc
  exact (ne_of_gt hA) hzA

/-- Translating a positive-volume local peak preserves its height and ball radius. -/
theorem positive_peak_translate (a c : Maxwell.Space) (r M : ℝ) (E : Maxwell.Field) (i : Fin 3)
    (hpeak : 0 < (volume.restrict (Metric.ball c r)) {x | M < ‖E x i‖}) :
    0 < (volume.restrict (Metric.ball (c+a) r)) {x | M < ‖E (x-a) i‖} := by
  rw [Measure.restrict_apply' measurableSet_ball] at hpeak ⊢
  have hp := positive_preimage_sub a ({x | M < ‖E x i‖} ∩ Metric.ball c r) hpeak
  have he : (fun x : Maxwell.Space => x-a) ⁻¹' ({x | M < ‖E x i‖} ∩ Metric.ball c r) =
      {x | M < ‖E (x-a) i‖} ∩ Metric.ball (c+a) r := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_ball]
    rw [dist_eq_norm, dist_eq_norm]
    have hd : x - a - c = x - (c + a) := by abel
    rw [hd]
  rwa [he] at hp

end OQ14.Packet07ScaleMeasure
#print axioms OQ14.Packet07ScaleMeasure.positive_preimage_smul

#print axioms OQ14.Packet07ScaleMeasure.positive_peak_dilation

#print axioms OQ14.Packet07ScaleMeasure.positive_preimage_sub
#print axioms OQ14.Packet07ScaleMeasure.positive_peak_translate
