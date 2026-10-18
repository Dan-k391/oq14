import NewtonFourier
import GradientProjection

/-!
# Distributional Hessian of the actual Newton kernel

The second derivatives are defined through the actual derivatives of Schwartz
test functions. The source contribution is therefore retained. The Fourier
symbol is derived from the proved scalar Newton identity, not postulated.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.NewtonHessian

open MeasureTheory
open scoped SchwartzMap FourierTransform InnerProductSpace ComplexConjugate

abbrev Space := FourierL2.Space

theorem inverse_fourier_pderivative (i : Fin 3) (f : 𝓢(Space, ℂ)) (ξ : Space) :
    ((SchwartzMap.fourierTransformCLE ℂ).symm (GradientProjection.pderivative i f)) ξ =
      -(2 * Real.pi * Complex.I) * (ξ i : ℂ) *
        ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ := by
  have h := GradientProjection.fourier_pderivative i f (-ξ)
  simp only [← Real.fourierIntegralInv_eq_fourierIntegral_neg] at h
  change 𝓕⁻ (GradientProjection.pderivative i f) ξ = _ at h
  simp only [SchwartzMap.fourierTransformCLE_symm_apply]
  rw [h]
  change (2 * Real.pi * Complex.I) * ((-ξ i : ℝ) : ℂ) * 𝓕⁻ f ξ = _
  push_cast
  ring

def hessianSymbol (ξ : Space) (i j : Fin 3) : ℂ :=
  -((ξ i : ℂ) * (ξ j : ℂ)) / (‖ξ‖ : ℂ)^2

private theorem symbol_factor (ξ : Space) (i j : Fin 3) (z : ℂ) :
    NewtonFourier.newtonSymbol ξ *
      (-(2 * Real.pi * Complex.I) * (ξ i : ℂ) *
        (-(2 * Real.pi * Complex.I) * (ξ j : ℂ) * z)) = hessianSymbol ξ i j * z := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold NewtonFourier.newtonSymbol hessianSymbol
  push_cast
  simp only [mul_inv_rev, inv_pow, div_eq_mul_inv]
  ring_nf
  simp [Complex.I_sq, hp]

def weakHessian (i j : Fin 3) (f : 𝓢(Space, ℂ)) : ℂ :=
  ∫ x, GreenKernel.phi 0 x *
    (GradientProjection.pderivative i (GradientProjection.pderivative j f)) x

/-- Fourier identification of the full distributional Newton Hessian. -/
theorem weakHessian_fourier (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    weakHessian i j f = ∫ ξ, hessianSymbol ξ i j *
      ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ := by
  rw [weakHessian, NewtonFourier.newton_inverse_pairing]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [inverse_fourier_pderivative, inverse_fourier_pderivative, symbol_factor]

theorem weakHessian_fourier_test (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    weakHessian i j (SchwartzMap.fourierTransformCLE ℂ f) =
      ∫ ξ, hessianSymbol ξ i j * f ξ := by
  rw [weakHessian_fourier, ContinuousLinearEquiv.symm_apply_apply]

theorem hessianSymbol_coordinate (ξ : Space) (z : VectorFourier.Vector) (i : Fin 3) :
    (∑ j, hessianSymbol ξ i j * z j) =
      -LongitudinalProjection.symbol (VectorFourier.coordinateMap ξ) z i := by
  rw [LongitudinalProjection.symbol_coordinate]
  have hn : ∑ j : Fin 3, (ξ j : ℂ)^2 = (‖ξ‖ : ℂ)^2 := by
    simpa only [Fin.sum_univ_three] using GreenKernel.coordinate_squares ξ
  change (∑ j, hessianSymbol ξ i j * z j) =
    -((∑ j, (ξ j : ℂ) * z j) / (∑ j, (ξ j : ℂ)^2) * (ξ i : ℂ))
  rw [hn]
  simp only [hessianSymbol, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_neg_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hessianSymbol_single (ξ : Space) (i j : Fin 3) :
    hessianSymbol ξ i j = -LongitudinalProjection.symbol (VectorFourier.coordinateMap ξ)
      (EuclideanSpace.single j (1 : ℂ)) i := by
  simpa [EuclideanSpace.single_apply] using
    hessianSymbol_coordinate ξ (EuclideanSpace.single j (1 : ℂ)) i

theorem hessianSymbol_norm_le (ξ : Space) (i j : Fin 3) : ‖hessianSymbol ξ i j‖ ≤ 1 := by
  rw [hessianSymbol_single, norm_neg]
  exact (PiLp.norm_apply_le _ i).trans ((LongitudinalProjection.symbol_norm_le _ _).trans_eq
    (by simp [EuclideanSpace.norm_single]))

theorem hessianSymbol_schwartz_integrable (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    Integrable (fun ξ => hessianSymbol ξ i j * f ξ) := by
  have hm : Measurable (fun ξ => hessianSymbol ξ i j) := by unfold hessianSymbol; fun_prop
  apply f.integrable.norm.mono' (hm.mul f.continuous.measurable).aestronglyMeasurable
  filter_upwards with ξ
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hessianSymbol_norm_le ξ i j)

theorem hessianSymbol_trace (ξ : Space) (hξ : ξ ≠ 0) :
    (∑ i : Fin 3, hessianSymbol ξ i i) = -1 := by
  have hr : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
  simp only [hessianSymbol, ← pow_two, ← Finset.sum_div, ← Finset.sum_neg_distrib]
  have hn : ∑ j : Fin 3, (ξ j : ℂ)^2 = (‖ξ‖ : ℂ)^2 := by
    simpa only [Fin.sum_univ_three] using GreenKernel.coordinate_squares ξ
  rw [Finset.sum_neg_distrib, hn, neg_div, div_self (pow_ne_zero _ hr)]

private theorem integral_inverse_fourier (f : 𝓢(Space, ℂ)) :
    (∫ ξ, ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ) = f 0 := by
  have h := congrArg (fun g : 𝓢(Space, ℂ) => g 0)
    ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply f)
  change 𝓕 ((SchwartzMap.fourierTransformCLE ℂ).symm f) 0 = f 0 at h
  rw [Real.fourierIntegral_eq'] at h
  simpa using h

/-- The fundamental-solution identity includes the Dirac source exactly. -/
theorem weakHessian_trace (f : 𝓢(Space, ℂ)) :
    (∑ i : Fin 3, weakHessian i i f) = -f 0 := by
  simp_rw [weakHessian_fourier]
  rw [← integral_finset_sum _ (fun i _ => hessianSymbol_schwartz_integrable i i
    ((SchwartzMap.fourierTransformCLE ℂ).symm f))]
  calc
    _ = ∫ ξ, -((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ := by
      apply integral_congr_ae
      filter_upwards [show ∀ᵐ ξ : Space, ξ ≠ 0 from ae_iff.mpr (by simp)] with ξ hξ
      rw [← Finset.sum_mul, hessianSymbol_trace ξ hξ]
      ring
    _ = -f 0 := by rw [integral_neg, integral_inverse_fourier]

/-- The already constructed physical projection has exactly the negative
distributional Newton Hessian matrix as its Fourier multiplier. -/
theorem physicalProjection_hessianSymbol (F : VectorFourier.VectorL2) (i : Fin 3) :
    (fun ξ => VectorFourier.fourier (VectorFourier.physicalProjection F) ξ i) =ᵐ[volume]
      fun ξ => -(∑ j, hessianSymbol (VectorFourier.coordinateMap.symm ξ) i j *
        VectorFourier.fourier F ξ j) := by
  filter_upwards [VectorFourier.physicalProjection_symbol F] with ξ hξ
  rw [hξ]
  have he := hessianSymbol_coordinate (VectorFourier.coordinateMap.symm ξ)
    (VectorFourier.fourier F ξ) i
  rw [MeasurableEquiv.apply_symm_apply] at he
  simpa using (congrArg Neg.neg he).symm

end OQ14.NewtonHessian

#print axioms OQ14.NewtonHessian.inverse_fourier_pderivative
#print axioms OQ14.NewtonHessian.weakHessian_fourier
#print axioms OQ14.NewtonHessian.weakHessian_fourier_test
#print axioms OQ14.NewtonHessian.hessianSymbol_coordinate
#print axioms OQ14.NewtonHessian.hessianSymbol_single
#print axioms OQ14.NewtonHessian.hessianSymbol_norm_le
#print axioms OQ14.NewtonHessian.hessianSymbol_schwartz_integrable
#print axioms OQ14.NewtonHessian.hessianSymbol_trace
#print axioms OQ14.NewtonHessian.weakHessian_trace
#print axioms OQ14.NewtonHessian.physicalProjection_hessianSymbol
