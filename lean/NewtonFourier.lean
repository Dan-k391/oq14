import HeatFourier
import KernelIntegrability

/-!
# Fourier identity of the actual Newton kernel

The local inverse-radius estimates and actual Gaussian representations are used
to prove absolute integrability of the scale-space pairings. No kernel Fourier
identity or integral interchange is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.NewtonFourier

open MeasureTheory Set Metric
open scoped SchwartzMap FourierTransform InnerProductSpace ComplexConjugate

abbrev Space := FourierL2.Space

private theorem weighted_schwartz_integrable (w : Space → ℝ)
    (hw : Measurable w) (hwloc : IntegrableOn w (closedBall 0 1))
    (hn : ∀ x, 0 ≤ w x) (ht : ∀ x, 1 ≤ ‖x‖ → w x ≤ 1)
    (f : 𝓢(Space, ℂ)) : Integrable (fun x => w x * ‖f x‖) := by
  have hsmall := hwloc.mul_continuousOn f.continuous.norm.continuousOn
    (isCompact_closedBall (0 : Space) 1)
  have hlarge : IntegrableOn (fun x => w x * ‖f x‖) (closedBall 0 1)ᶜ := by
    apply f.integrable.norm.integrableOn.mono'
      (hw.mul f.continuous.measurable.norm).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
    have hr : 1 ≤ ‖x‖ := by
      have hr' : 1 < ‖x‖ := by
        simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hx
      exact hr'.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn x) (norm_nonneg _))]
    exact mul_le_of_le_one_left (norm_nonneg _) (ht x hr)
  have h := hsmall.union hlarge
  simpa only [union_compl_self, integrableOn_univ] using h

theorem inverse_norm_schwartz_integrable (f : 𝓢(Space, ℂ)) :
    Integrable (fun x => ‖x‖⁻¹ * ‖f x‖) := by
  apply weighted_schwartz_integrable _ (by fun_prop)
    (KernelIntegrability.inverse_norm_integrable_ball 1)
    (fun x => inv_nonneg.mpr (norm_nonneg x))
  intro x hx
  exact inv_le_one_of_one_le₀ hx

theorem inverse_norm_sq_schwartz_integrable (f : 𝓢(Space, ℂ)) :
    Integrable (fun x => (‖x‖⁻¹)^2 * ‖f x‖) := by
  apply weighted_schwartz_integrable _ (by fun_prop)
    (KernelIntegrability.inverse_norm_sq_integrable_ball 1) (fun x => sq_nonneg _)
  intro x hx
  have h0 := inv_nonneg.mpr (norm_nonneg x)
  have h1 := inv_le_one_of_one_le₀ hx
  nlinarith

def newtonSymbol (ξ : Space) : ℂ := ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)⁻¹ : ℂ)

theorem newton_schwartz_integrable (f : 𝓢(Space, ℂ)) :
    Integrable (fun x => GreenKernel.phi 0 x * f x) := by
  apply ((inverse_norm_schwartz_integrable f).const_mul ((4 * Real.pi)⁻¹)).mono'
    ((KernelIntegrability.phi_measurable 0).mul f.continuous.measurable).aestronglyMeasurable
  filter_upwards with x
  rw [norm_mul, KernelIntegrability.phi_norm]
  exact (mul_assoc _ _ _).le

theorem symbol_schwartz_integrable (f : 𝓢(Space, ℂ)) :
    Integrable (fun ξ => newtonSymbol ξ * f ξ) := by
  apply ((inverse_norm_sq_schwartz_integrable f).const_mul ((4 * Real.pi ^ 2)⁻¹)).mono'
    (((show Measurable newtonSymbol by unfold newtonSymbol; fun_prop).mul
      f.continuous.measurable).aestronglyMeasurable)
  filter_upwards with ξ
  simp only [newtonSymbol, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg (sq_nonneg Real.pi),
    abs_of_nonneg (sq_nonneg ‖ξ‖), mul_inv_rev, inv_pow]
  exact (by ring : _ = _).le

private theorem gaussian_scale_norm_integral (x : Space) (hx : x ≠ 0) :
    (∫ s : ℝ in Ioi 0, ‖HeatFourier.gaussian (s ^ 2) x‖) =
      (Real.sqrt Real.pi / 2) * ‖x‖⁻¹ := by
  have h := congrArg Complex.re (HeatFourier.gaussian_scale_integral x hx)
  change RCLike.re (∫ s : ℝ in Ioi 0, HeatFourier.gaussian (s ^ 2) x) = _ at h
  rw [← integral_re (HeatFourier.gaussian_scale_integrable x hx)] at h
  simp only [HeatFourier.gaussian_eq_real, Complex.ofReal_re] at h
  rw [show (2 : ℂ) * (‖x‖ : ℂ) = ((2 * ‖x‖ : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re] at h
  simp only [RCLike.ofReal_re, Complex.ofReal_re] at h
  change (∫ s : ℝ in Ioi 0, Real.exp (-s ^ 2 * ‖x‖ ^ 2)) =
    Real.sqrt Real.pi / (2 * ‖x‖) at h
  simp only [HeatFourier.gaussian_norm]
  rw [h]
  ring

def spectralScale (s : ℝ) (ξ : Space) : ℂ :=
  (Real.pi * Real.sqrt Real.pi *
    (s⁻¹ ^ 3 * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2) / s ^ 2)) : ℝ)

theorem spectralScale_eq_fourier (s : ℝ) (hs : 0 < s) (ξ : Space) :
    spectralScale s ξ = 𝓕 (HeatFourier.gaussian (s ^ 2)) ξ :=
  (HeatFourier.gaussian_fourier_scale s hs ξ).symm

private theorem spectralScale_integrable (ξ : Space) (hξ : ξ ≠ 0) :
    IntegrableOn (fun s => spectralScale s ξ) (Ioi 0) := by
  apply (HeatFourier.gaussian_fourier_scale_integrable ξ hξ).congr_fun _ measurableSet_Ioi
  intro s hs
  exact (spectralScale_eq_fourier s hs ξ).symm

private theorem spectralScale_norm_integral (ξ : Space) (hξ : ξ ≠ 0) :
    (∫ s : ℝ in Ioi 0, ‖spectralScale s ξ‖) =
      (Real.sqrt Real.pi / (2 * Real.pi)) * (‖ξ‖⁻¹)^2 := by
  have he (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) : ‖spectralScale s ξ‖ =
      Real.pi * Real.sqrt Real.pi *
        (s⁻¹ ^ 3 * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2) / s ^ 2)) := by
    simp only [spectralScale, Complex.norm_real, Real.norm_eq_abs]
    apply abs_of_nonneg
    exact mul_nonneg (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg _))
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr hs.le) _) (Real.exp_pos _).le)
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    HeatFourier.inverse_scale_integral _ (mul_pos (sq_pos_of_pos Real.pi_pos)
      (sq_pos_of_pos (norm_pos_iff.mpr hξ)))]
  field_simp [Real.pi_ne_zero, norm_ne_zero_iff.mpr hξ]
  ring

theorem gaussian_pairing_integrable (f : 𝓢(Space, ℂ)) :
    Integrable (fun p : Space × ℝ => HeatFourier.gaussian (p.2 ^ 2) p.1 * f p.1)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun p : Space × ℝ => HeatFourier.gaussian (p.2 ^ 2) p.1) := by
    unfold HeatFourier.gaussian
    fun_prop
  apply (integrable_prod_iff (μ := (volume : Measure Space)) (ν := volume.restrict (Ioi (0 : ℝ)))
    (hm.mul (f.continuous.measurable.comp measurable_fst)).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
    exact (HeatFourier.gaussian_scale_integrable x hx).mul_const (f x)
  · apply ((inverse_norm_schwartz_integrable f).const_mul (Real.sqrt Real.pi / 2)).congr
    filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
    simp only [norm_mul, Function.comp_apply]
    rw [integral_mul_const, gaussian_scale_norm_integral x hx]
    exact (mul_assoc _ _ _).symm

theorem spectral_pairing_integrable (f : 𝓢(Space, ℂ)) :
    Integrable (fun p : Space × ℝ => spectralScale p.2 p.1 * f p.1)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun p : Space × ℝ => spectralScale p.2 p.1) := by
    unfold spectralScale
    fun_prop
  apply (integrable_prod_iff (μ := (volume : Measure Space)) (ν := volume.restrict (Ioi (0 : ℝ)))
    (hm.mul (f.continuous.measurable.comp measurable_fst)).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [show ∀ᵐ ξ : Space, ξ ≠ 0 from ae_iff.mpr (by simp)] with ξ hξ
    exact (spectralScale_integrable ξ hξ).mul_const (f ξ)
  · apply ((inverse_norm_sq_schwartz_integrable f).const_mul
      (Real.sqrt Real.pi / (2 * Real.pi))).congr
    filter_upwards [show ∀ᵐ ξ : Space, ξ ≠ 0 from ae_iff.mpr (by simp)] with ξ hξ
    simp only [norm_mul, Function.comp_apply]
    rw [integral_mul_const, spectralScale_norm_integral ξ hξ]
    exact (mul_assoc _ _ _).symm

theorem newton_pairing_scale (f : 𝓢(Space, ℂ)) :
    (∫ x, GreenKernel.phi 0 x * f x) =
      (2 * Real.pi * (Real.sqrt Real.pi : ℂ))⁻¹ *
        ∫ s : ℝ in Ioi 0, ∫ x, HeatFourier.gaussian (s ^ 2) x * f x := by
  rw [← integral_integral_swap (gaussian_pairing_integrable f), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
  rw [integral_mul_const, HeatFourier.newton_gaussian_representation x hx]
  ring

theorem symbol_pairing_scale (f : 𝓢(Space, ℂ)) :
    (∫ ξ, newtonSymbol ξ * f ξ) =
      (2 * Real.pi * (Real.sqrt Real.pi : ℂ))⁻¹ *
        ∫ s : ℝ in Ioi 0, ∫ ξ, spectralScale s ξ * f ξ := by
  rw [← integral_integral_swap (spectral_pairing_integrable f), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [show ∀ᵐ ξ : Space, ξ ≠ 0 from ae_iff.mpr (by simp)] with ξ hξ
  have he : newtonSymbol ξ = (2 * Real.pi * (Real.sqrt Real.pi : ℂ))⁻¹ *
      ∫ s : ℝ in Ioi 0, spectralScale s ξ := by
    rw [newtonSymbol, HeatFourier.newton_symbol_gaussian_representation ξ hξ]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact (spectralScale_eq_fourier s hs ξ).symm
  rw [integral_mul_const, he]
  ring

/-- The actual Newton distribution has the reciprocal-square Fourier symbol,
with mathlib's `exp(-2*pi*i*inner x xi)` convention. -/
theorem newton_fourier_pairing (f : 𝓢(Space, ℂ)) :
    (∫ x, GreenKernel.phi 0 x * 𝓕 f x) = ∫ ξ, newtonSymbol ξ * f ξ := by
  change (∫ x, GreenKernel.phi 0 x * (SchwartzMap.fourierTransformCLM ℂ f) x) = _
  rw [newton_pairing_scale, symbol_pairing_scale]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp_rw [spectralScale_eq_fourier s hs]
  exact (FourierL2.fourier_mul_integral_flip (HeatFourier.gaussian (s ^ 2)) f
    (HeatFourier.gaussian_integrable _ (sq_pos_of_pos hs)) f.integrable).symm

theorem newton_inverse_pairing (f : 𝓢(Space, ℂ)) :
    (∫ x, GreenKernel.phi 0 x * f x) =
      ∫ ξ, newtonSymbol ξ * ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ := by
  have h := newton_fourier_pairing ((SchwartzMap.fourierTransformCLE ℂ).symm f)
  change (∫ x, GreenKernel.phi 0 x *
    (SchwartzMap.fourierTransformCLE ℂ ((SchwartzMap.fourierTransformCLE ℂ).symm f)) x) = _ at h
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

end OQ14.NewtonFourier

#print axioms OQ14.NewtonFourier.inverse_norm_schwartz_integrable
#print axioms OQ14.NewtonFourier.inverse_norm_sq_schwartz_integrable
#print axioms OQ14.NewtonFourier.newton_schwartz_integrable
#print axioms OQ14.NewtonFourier.symbol_schwartz_integrable
#print axioms OQ14.NewtonFourier.spectralScale_eq_fourier
#print axioms OQ14.NewtonFourier.gaussian_pairing_integrable
#print axioms OQ14.NewtonFourier.spectral_pairing_integrable
#print axioms OQ14.NewtonFourier.newton_pairing_scale
#print axioms OQ14.NewtonFourier.symbol_pairing_scale
#print axioms OQ14.NewtonFourier.newton_fourier_pairing
#print axioms OQ14.NewtonFourier.newton_inverse_pairing
