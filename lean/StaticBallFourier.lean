import StaticBallSchwartz

/-! # Fourier identification of actual uniform-ball weak derivatives -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallFourier

open MeasureTheory Filter Set
open scoped Topology SchwartzMap

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2

theorem coordinate_mul_locallyIntegrable (G : ScalarL2) (i : Fin 3) (c : ℂ) :
    LocallyIntegrable (fun ξ : Space => c * (ξ i : ℂ) * G ξ) := by
  have hg := (Lp.memLp G).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hc : Continuous (fun ξ : Space => c * (ξ i : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous)
  exact locallyIntegrableOn_univ.mp
    ((hg.locallyIntegrableOn univ).continuousOn_mul hc.continuousOn isClosed_univ.isLocallyClosed)

/-- The Fourier derivative relation is derived from actual Schwartz weak
pairings and the actual Plancherel equivalence. -/
theorem weak_derivative_fourier (G H : ScalarL2) (i : Fin 3)
    (h : ∀ φ : 𝓢(Space, ℂ), (∫ x, H x * φ x) =
      -(∫ x, G x * GradientProjection.pderivative i φ x)) :
    FourierL2.fourierEquiv H =ᵐ[volume] fun ξ =>
      (2 * Real.pi * Complex.I) * (ξ i : ℂ) * FourierL2.fourierEquiv G ξ := by
  have hp : ∀ g : 𝓢(Space, ℂ),
      (∫ ξ, FourierL2.fourierEquiv H ξ * g ξ) =
        ∫ ξ, ((2 * Real.pi * Complex.I) * (ξ i : ℂ) * FourierL2.fourierEquiv G ξ) * g ξ := by
    intro g
    have he := h (SchwartzMap.fourierTransformCLE ℂ g)
    rw [NewtonL2.scalar_bilinear_parseval H (SchwartzMap.fourierTransformCLE ℂ g),
      NewtonL2.scalar_bilinear_parseval G
        (GradientProjection.pderivative i (SchwartzMap.fourierTransformCLE ℂ g))] at he
    rw [ContinuousLinearEquiv.symm_apply_apply] at he
    rw [he, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [NewtonHessian.inverse_fourier_pderivative, ContinuousLinearEquiv.symm_apply_apply]
    ring
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
    (coordinate_mul_locallyIntegrable (FourierL2.fourierEquiv G) i _)
  intro φ hφ hc
  let g := FourierL2.compactSmoothSchwartz (fun x => (φ x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
  have he := hp g
  simpa only [g, FourierL2.compactSmoothSchwartz, Complex.real_smul, mul_comm] using he

theorem hessian_fourier_derivative (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    FourierL2.fourierEquiv (StaticBallL2.hessianL2 R hR i j) =ᵐ[volume] fun ξ =>
      (2 * Real.pi * Complex.I) * (ξ i : ℂ) *
        FourierL2.fourierEquiv (StaticBallL2.gradientL2 R hR j) ξ :=
  weak_derivative_fourier _ _ i (StaticBallSchwartz.weak_hessian_schwartz R hR i j)

end OQ14.StaticBallFourier

#print axioms OQ14.StaticBallFourier.coordinate_mul_locallyIntegrable
#print axioms OQ14.StaticBallFourier.weak_derivative_fourier
#print axioms OQ14.StaticBallFourier.hessian_fourier_derivative
