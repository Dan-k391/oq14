import FourierL2
import GreenKernel
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Actual convolution and Gaussian Fourier identities

These identities concern ordinary integrals, not a supplied Fourier multiplier.
They prove the spatial Newton Gaussian-scale representation and its reciprocal-
square frequency counterpart. Scale integrability is derived from these actual
integrals. Interchanging the scale with a Schwartz pairing, and therefore the
distributional Newton Fourier identity, is left to a separate file.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.HeatFourier

open MeasureTheory
open scoped FourierTransform InnerProductSpace ComplexConjugate

abbrev Space := FourierL2.Space

def phase (ξ x : Space) : ℂ :=
  Complex.exp ((-2 * Real.pi * ⟪x, ξ⟫_ℝ : ℝ) * Complex.I)

def modulate (ξ : Space) (f : Space → ℂ) (x : Space) : ℂ := phase ξ x * f x

def convolution (f g : Space → ℂ) (x : Space) : ℂ := ∫ y, f y * g (x - y)

theorem phase_norm (ξ x : Space) : ‖phase ξ x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem phase_split (ξ x y : Space) : phase ξ y * phase ξ (x - y) = phase ξ x := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_sub_left]
  push_cast
  ring

theorem modulate_integrable (ξ : Space) {f : Space → ℂ} (hf : Integrable f) :
    Integrable (modulate ξ f) := by
  have hc : Continuous (phase ξ) := by unfold phase; fun_prop
  apply hf.mono (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with x
  change ‖phase ξ x * f x‖ ≤ ‖f x‖
  simp only [norm_mul, phase_norm, one_mul, le_refl]

theorem modulate_convolution (ξ : Space) (f g : Space → ℂ) (x : Space) :
    modulate ξ (convolution f g) x = convolution (modulate ξ f) (modulate ξ g) x := by
  simp only [modulate, convolution, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  calc
    phase ξ x * (f y * g (x - y)) =
        (phase ξ y * phase ξ (x - y)) * (f y * g (x - y)) := by rw [phase_split]
    _ = _ := by ring

theorem convolution_integrable {f g : Space → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (convolution f g) :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

theorem integral_convolution {f g : Space → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, convolution f g x) = (∫ x, f x) * ∫ x, g x :=
  MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hg

theorem fourier_as_modulate (f : Space → ℂ) (ξ : Space) :
    𝓕 f ξ = ∫ x, modulate ξ f x := by
  rw [Real.fourierIntegral_eq']
  rfl

theorem fourier_convolution {f g : Space → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ξ : Space) : 𝓕 (convolution f g) ξ = 𝓕 f ξ * 𝓕 g ξ := by
  simp only [fourier_as_modulate]
  simp_rw [modulate_convolution]
  exact integral_convolution (modulate_integrable ξ hf) (modulate_integrable ξ hg)

def gaussian (b : ℝ) (x : Space) : ℂ := Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2)

def gaussianMass (b : ℝ) : ℂ := ((Real.pi : ℂ) / b) ^ (3 / 2 : ℂ)

def normalizedGaussian (b : ℝ) (x : Space) : ℂ := (gaussianMass b)⁻¹ * gaussian b x

theorem gaussian_eq_real (b : ℝ) (x : Space) :
    gaussian b x = (Real.exp (-b * ‖x‖ ^ 2) : ℂ) := by
  rw [Complex.ofReal_exp]
  unfold gaussian
  congr 1
  push_cast
  ring

theorem gaussian_norm (b : ℝ) (x : Space) :
    ‖gaussian b x‖ = Real.exp (-b * ‖x‖ ^ 2) := by
  rw [gaussian_eq_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem gaussian_integrable (b : ℝ) (hb : 0 < b) : Integrable (gaussian b) := by
  simpa only [gaussian, zero_mul, add_zero] using
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (b : ℂ)) (by simpa using hb) 0 (0 : Space))

theorem gaussian_integral (b : ℝ) (hb : 0 < b) : ∫ x, gaussian b x = gaussianMass b := by
  simpa only [gaussian, gaussianMass, finrank_euclideanSpace, Fintype.card_fin] using
    (GaussianFourier.integral_cexp_neg_mul_sq_norm
      (V := Space) (b := (b : ℂ)) (by simpa using hb))

theorem gaussian_fourier (b : ℝ) (hb : 0 < b) (ξ : Space) :
    𝓕 (gaussian b) ξ = gaussianMass b *
      Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 / b) := by
  simpa only [gaussian, gaussianMass, finrank_euclideanSpace, Fintype.card_fin] using
    (fourierIntegral_gaussian_innerProductSpace (b := (b : ℂ)) (by simpa using hb) ξ)

theorem gaussianMass_ne_zero (b : ℝ) (hb : 0 < b) : gaussianMass b ≠ 0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast ne_of_gt hb))

theorem normalizedGaussian_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (normalizedGaussian b) := (gaussian_integrable b hb).const_mul _

theorem normalizedGaussian_mass (b : ℝ) (hb : 0 < b) :
    (∫ x, normalizedGaussian b x) = 1 := by
  simp only [normalizedGaussian]
  rw [integral_const_mul, gaussian_integral b hb]
  exact inv_mul_cancel₀ (gaussianMass_ne_zero b hb)

theorem normalizedGaussian_fourier (b : ℝ) (hb : 0 < b) (ξ : Space) :
    𝓕 (normalizedGaussian b) ξ =
      Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 / b) := by
  rw [fourier_as_modulate]
  simp only [modulate, normalizedGaussian, mul_left_comm (phase ξ _) ((gaussianMass b)⁻¹)]
  rw [integral_const_mul]
  change (gaussianMass b)⁻¹ * (∫ x, modulate ξ (gaussian b) x) = _
  rw [← fourier_as_modulate]
  rw [gaussian_fourier b hb ξ, ← mul_assoc, inv_mul_cancel₀ (gaussianMass_ne_zero b hb), one_mul]

theorem gaussian_convolution_fourier (b : ℝ) (hb : 0 < b)
    {f : Space → ℂ} (hf : Integrable f) (ξ : Space) :
    𝓕 (convolution (normalizedGaussian b) f) ξ =
      Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 / b) * 𝓕 f ξ := by
  rw [fourier_convolution (normalizedGaussian_integrable b hb) hf,
    normalizedGaussian_fourier b hb]

theorem gaussian_scale_integral (x : Space) (hx : x ≠ 0) :
    (∫ s : ℝ in Set.Ioi 0, gaussian (s ^ 2) x) =
      (Real.sqrt Real.pi : ℂ) / (2 * (‖x‖ : ℂ)) := by
  have he (s : ℝ) : gaussian (s ^ 2) x =
      (Real.exp (-(‖x‖ ^ 2) * s ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    unfold gaussian
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_complex_ofReal, integral_gaussian_Ioi]
  rw [Real.sqrt_div (by exact Real.pi_pos.le), Real.sqrt_sq (norm_nonneg x)]
  push_cast
  field_simp [norm_ne_zero_iff.mpr hx]
  ring_nf
  simp

/-- The actual Newton kernel, away from its source, as an integral of Gaussians. -/
theorem newton_gaussian_representation (x : Space) (hx : x ≠ 0) :
    GreenKernel.phi 0 x =
      (2 * Real.pi * (Real.sqrt Real.pi : ℂ))⁻¹ *
        ∫ s : ℝ in Set.Ioi 0, gaussian (s ^ 2) x := by
  rw [gaussian_scale_integral x hx]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  simp only [GreenKernel.phi, GreenKernel.radial, Complex.ofReal_zero, mul_zero,
    zero_mul, Complex.exp_zero]
  field_simp [hp, hs, hr]
  ring

theorem gaussianMass_sq (s : ℝ) (hs : 0 < s) :
    gaussianMass (s ^ 2) =
      (Real.pi * Real.sqrt Real.pi / s ^ 3 : ℝ) := by
  have hp : 0 ≤ Real.pi / s ^ 2 := div_nonneg Real.pi_pos.le (sq_nonneg s)
  unfold gaussianMass
  rw [show (Real.pi : ℂ) / (s ^ 2 : ℝ) = ((Real.pi / s ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow hp, Real.rpow_div_two_eq_sqrt 3 hp,
    Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq hs.le]
  congr 1
  rw [show (Real.sqrt Real.pi / s) ^ (3 : ℝ) =
    (Real.sqrt Real.pi / s) ^ (3 : ℕ) from Real.rpow_natCast _ 3]
  rw [div_pow]
  congr 1
  rw [show Real.sqrt Real.pi ^ 3 = Real.sqrt Real.pi ^ 2 * Real.sqrt Real.pi by ring,
    Real.sq_sqrt Real.pi_pos.le]

theorem inverse_scale_integral (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in Set.Ioi 0, s⁻¹ ^ 3 * Real.exp (-a / s ^ 2)) = (2 * a)⁻¹ := by
  have h := integral_comp_rpow_Ioi (fun t : ℝ => Real.exp (-a * t))
    (p := (-2 : ℝ)) (by norm_num)
  have he (s : ℝ) (hs : 0 < s) :
      (|(-2 : ℝ)| * s ^ ((-2 : ℝ) - 1)) • Real.exp (-a * s ^ (-2 : ℝ)) =
        2 * (s⁻¹ ^ 3 * Real.exp (-a / s ^ 2)) := by
    have h3 : s ^ ((-2 : ℝ) - 1) = (s ^ 3)⁻¹ := by
      norm_num [Real.rpow_neg hs.le]
      exact Real.rpow_natCast s 3
    have h2 : s ^ (-2 : ℝ) = (s ^ 2)⁻¹ := by norm_num [Real.rpow_neg hs.le]
    rw [h3, h2]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), smul_eq_mul]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos ha) 0] at h
  simp only [mul_zero, Real.exp_zero, neg_div, one_div] at h
  have han : a ≠ 0 := ne_of_gt ha
  field_simp [han] at h ⊢
  nlinarith

theorem gaussian_fourier_scale (s : ℝ) (hs : 0 < s) (ξ : Space) :
    𝓕 (gaussian (s ^ 2)) ξ =
      (Real.pi * Real.sqrt Real.pi *
        (s⁻¹ ^ 3 * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2) / s ^ 2)) : ℝ) := by
  rw [gaussian_fourier (s ^ 2) (sq_pos_of_pos hs), gaussianMass_sq s hs]
  rw [show -(Real.pi : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 / (s ^ 2 : ℝ) =
    ((-(Real.pi ^ 2 * ‖ξ‖ ^ 2) / s ^ 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp]
  push_cast
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- The reciprocal-square Newton symbol from the actual transformed Gaussians. -/
theorem newton_symbol_gaussian_representation (ξ : Space) (hξ : ξ ≠ 0) :
    ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)⁻¹ : ℂ) =
      (2 * Real.pi * (Real.sqrt Real.pi : ℂ))⁻¹ *
        ∫ s : ℝ in Set.Ioi 0, 𝓕 (gaussian (s ^ 2)) ξ := by
  have ha : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 :=
    mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos (norm_pos_iff.mpr hξ))
  have he := setIntegral_congr_fun (μ := volume) measurableSet_Ioi
    (fun s hs => gaussian_fourier_scale s hs ξ)
  rw [he, integral_complex_ofReal]
  rw [integral_const_mul, inverse_scale_integral _ ha]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  have hr : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
  push_cast
  field_simp [hp, hs, hr]
  ring

theorem gaussian_scale_integrable (x : Space) (hx : x ≠ 0) :
    IntegrableOn (fun s : ℝ => gaussian (s ^ 2) x) (Set.Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_scale_integral x hx]
  apply div_ne_zero
  · exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast norm_ne_zero_iff.mpr hx)

theorem gaussian_fourier_scale_integrable (ξ : Space) (hξ : ξ ≠ 0) :
    IntegrableOn (fun s : ℝ => 𝓕 (gaussian (s ^ 2)) ξ) (Set.Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  intro h
  have he := newton_symbol_gaussian_representation ξ hξ
  rw [h, mul_zero] at he
  have hp : 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
      (sq_pos_of_pos (norm_pos_iff.mpr hξ)))
  exact (by exact_mod_cast inv_ne_zero hp :
    ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)⁻¹ : ℂ) ≠ 0) he

end OQ14.HeatFourier

#print axioms OQ14.HeatFourier.phase_norm
#print axioms OQ14.HeatFourier.phase_split
#print axioms OQ14.HeatFourier.modulate_integrable
#print axioms OQ14.HeatFourier.modulate_convolution
#print axioms OQ14.HeatFourier.convolution_integrable
#print axioms OQ14.HeatFourier.integral_convolution
#print axioms OQ14.HeatFourier.fourier_as_modulate
#print axioms OQ14.HeatFourier.fourier_convolution
#print axioms OQ14.HeatFourier.gaussian_eq_real
#print axioms OQ14.HeatFourier.gaussian_norm
#print axioms OQ14.HeatFourier.gaussian_integrable
#print axioms OQ14.HeatFourier.gaussian_integral
#print axioms OQ14.HeatFourier.gaussian_fourier
#print axioms OQ14.HeatFourier.gaussianMass_ne_zero
#print axioms OQ14.HeatFourier.normalizedGaussian_integrable
#print axioms OQ14.HeatFourier.normalizedGaussian_mass
#print axioms OQ14.HeatFourier.normalizedGaussian_fourier
#print axioms OQ14.HeatFourier.gaussian_convolution_fourier
#print axioms OQ14.HeatFourier.gaussian_scale_integral
#print axioms OQ14.HeatFourier.newton_gaussian_representation
#print axioms OQ14.HeatFourier.gaussianMass_sq
#print axioms OQ14.HeatFourier.inverse_scale_integral
#print axioms OQ14.HeatFourier.gaussian_fourier_scale
#print axioms OQ14.HeatFourier.newton_symbol_gaussian_representation
#print axioms OQ14.HeatFourier.gaussian_scale_integrable
#print axioms OQ14.HeatFourier.gaussian_fourier_scale_integrable
