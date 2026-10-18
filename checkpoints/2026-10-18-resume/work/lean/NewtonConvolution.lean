import NewtonHessian

/-!
# Spatial weak Newton-Hessian convolution

The response is defined by integrating actual translated weak-Hessian test
pairings against a source. Its Fourier multiplier is derived using absolute
Fubini, rather than used as the definition of spatial convolution.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.NewtonConvolution

open MeasureTheory
open scoped SchwartzMap FourierTransform InnerProductSpace ComplexConjugate

abbrev Space := FourierL2.Space

private theorem translation_growth (y : Space) :
    Function.HasTemperateGrowth (fun x : Space => x + y) := by
  apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖y‖)
  · have he : fderiv ℝ (fun x : Space => x + y) =
        fun _ => ContinuousLinearMap.id ℝ Space := by ext x v; simp
    rw [he]
    exact Function.HasTemperateGrowth.const _
  · exact differentiable_id.add_const y
  · intro x
    have h := norm_add_le x y
    nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg (norm_nonneg x) (norm_nonneg y)]

def translate (y : Space) (f : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (translation_growth y) (isometry_add_right y).antilipschitz f

theorem translate_apply (y : Space) (f : 𝓢(Space, ℂ)) (x : Space) :
    translate y f x = f (x + y) := rfl

theorem translate_pderivative (y : Space) (i : Fin 3) (f : 𝓢(Space, ℂ)) :
    GradientProjection.pderivative i (translate y f) =
      translate y (GradientProjection.pderivative i f) := by
  ext x
  change (fderiv ℝ (fun z : Space => f (z + y)) x) (Maxwell.basis i) =
    (fderiv ℝ (f : Space → ℂ) (x + y)) (Maxwell.basis i)
  rw [fderiv_comp x f.differentiable.differentiableAt (differentiableAt_id.add_const y)]
  simp

theorem inverse_fourier_translate (y ξ : Space) (f : 𝓢(Space, ℂ)) :
    ((SchwartzMap.fourierTransformCLE ℂ).symm (translate y f)) ξ =
      HeatFourier.phase ξ y * ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure Space) (innerₗ Space) (f : Space → ℂ) y) (-ξ)
  change 𝓕 (fun x => f (x + y)) (-ξ) =
    (Real.fourierChar ⟪y, -ξ⟫_ℝ : ℂ) * 𝓕 f (-ξ) at h
  change 𝓕 (fun x => f (x + y)) (-ξ) = HeatFourier.phase ξ y * 𝓕 f (-ξ)
  rw [h]
  congr 1
  simp only [HeatFourier.phase, Real.fourierChar_apply, inner_neg_right]
  congr 1
  push_cast
  ring

theorem weakHessian_translate_spatial (y : Space) (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    NewtonHessian.weakHessian i j (translate y f) =
      ∫ x, GreenKernel.phi 0 (x - y) *
        (GradientProjection.pderivative i (GradientProjection.pderivative j f)) x := by
  rw [NewtonHessian.weakHessian, translate_pderivative, translate_pderivative]
  have h := integral_add_right_eq_self
    (fun x : Space => GreenKernel.phi 0 (x - y) *
      (GradientProjection.pderivative i (GradientProjection.pderivative j f)) x) y
  simpa only [translate_apply, add_sub_cancel_right] using h

theorem weakHessian_translate_fourier (y : Space) (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    NewtonHessian.weakHessian i j (translate y f) =
      ∫ ξ, NewtonHessian.hessianSymbol ξ i j *
        (HeatFourier.phase ξ y * ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ) := by
  rw [NewtonHessian.weakHessian_fourier]
  simp_rw [inverse_fourier_translate]

def weakConvolution (ρ : Space → ℂ) (i j : Fin 3) (f : 𝓢(Space, ℂ)) : ℂ :=
  ∫ y, ρ y * NewtonHessian.weakHessian i j (translate y f)

theorem weakConvolution_spatial (ρ : Space → ℂ) (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    weakConvolution ρ i j f = ∫ y, ρ y *
      ∫ x, GreenKernel.phi 0 (x - y) *
        (GradientProjection.pderivative i (GradientProjection.pderivative j f)) x := by
  simp only [weakConvolution, weakHessian_translate_spatial]

theorem source_fourier_pairing_integrable {ρ : Space → ℂ} (hρ : Integrable ρ)
    (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    Integrable (fun p : Space × Space => ρ p.1 * (NewtonHessian.hessianSymbol p.2 i j *
      (HeatFourier.phase p.2 p.1 * ((SchwartzMap.fourierTransformCLE ℂ).symm f) p.2)))
      (volume.prod volume) := by
  have hm : Measurable (fun ξ : Space => NewtonHessian.hessianSymbol ξ i j) := by
    unfold NewtonHessian.hessianSymbol
    fun_prop
  have hp : Measurable (fun p : Space × Space => HeatFourier.phase p.2 p.1) := by
    unfold HeatFourier.phase
    fun_prop
  apply (hρ.norm.mul_prod ((SchwartzMap.fourierTransformCLE ℂ).symm f).integrable.norm).mono'
    (hρ.aestronglyMeasurable.fst.mul (hm.aestronglyMeasurable.snd.mul
      (hp.aestronglyMeasurable.mul
        ((SchwartzMap.fourierTransformCLE ℂ).symm f).continuous.aestronglyMeasurable.snd)))
  filter_upwards with p
  simp only [norm_mul, HeatFourier.phase_norm, one_mul]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) (NewtonHessian.hessianSymbol_norm_le _ i j))
    (norm_nonneg _)

theorem source_weak_pairing_integrable {ρ : Space → ℂ} (hρ : Integrable ρ)
    (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    Integrable (fun y => ρ y * NewtonHessian.weakHessian i j (translate y f)) := by
  apply (source_fourier_pairing_integrable hρ i j f).integral_prod_left.congr
  filter_upwards with y
  rw [weakHessian_translate_fourier, integral_const_mul]

/-- The explicitly spatial weak convolution by the full Newton Hessian
has the derived Fourier multiplier, for every actual L1 source. -/
theorem weakConvolution_fourier {ρ : Space → ℂ} (hρ : Integrable ρ)
    (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    weakConvolution ρ i j f = ∫ ξ, NewtonHessian.hessianSymbol ξ i j *
      𝓕 ρ ξ * ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ := by
  unfold weakConvolution
  simp_rw [weakHessian_translate_fourier, ← integral_const_mul]
  rw [integral_integral_swap (source_fourier_pairing_integrable hρ i j f)]
  apply integral_congr_ae
  filter_upwards with ξ
  have he (y : Space) : ρ y * (NewtonHessian.hessianSymbol ξ i j *
      (HeatFourier.phase ξ y * ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ)) =
      (NewtonHessian.hessianSymbol ξ i j * (HeatFourier.phase ξ y * ρ y)) *
        ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ := by ring
  simp_rw [he]
  rw [integral_mul_const, integral_const_mul, HeatFourier.fourier_as_modulate]
  rfl

end OQ14.NewtonConvolution
