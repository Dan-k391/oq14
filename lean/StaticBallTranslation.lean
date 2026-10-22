import StaticBallNewton

/-! # Actual L2 translation of the uniform-ball weak Hessian -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallTranslation

open MeasureTheory Metric Set
open scoped Topology SchwartzMap BigOperators

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2

def scalar (c : Space) : ScalarL2 →ₗᵢ[ℂ] ScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Space => x + -c)
    (measurePreserving_add_right volume (-c))

theorem scalar_ae (c : Space) (F : ScalarL2) :
    scalar c F =ᵐ[volume] fun x => F (x-c) := by
  simpa only [sub_eq_add_neg] using
    Lp.coeFn_compMeasurePreserving F (measurePreserving_add_right volume (-c))

theorem scalar_pairing (c : Space) (F : ScalarL2) (φ : 𝓢(Space, ℂ)) :
    (∫ x, scalar c F x * φ x) = ∫ x, F x * NewtonConvolution.translate c φ x := by
  calc
    _ = ∫ x, F (x-c) * φ x := by
      apply integral_congr_ae
      filter_upwards [scalar_ae c F] with x hx
      rw [hx]
    _ = _ := by
      have he := integral_add_right_eq_self (μ := (volume : Measure Space))
        (fun x => F (x-c)*φ x) c
      simpa only [add_sub_cancel_right, NewtonConvolution.translate_apply] using he.symm

theorem translated_ball_ae (c : Space) (R : ℝ) :
    scalar c (StaticBallSymbol.ballL2 R) =ᵐ[volume]
      (ball c R).indicator (fun _ => (1 : ℂ)) := by
  have hb := (measurePreserving_add_right (volume : Measure Space) (-c)).quasiMeasurePreserving.ae
    (StaticBallSymbol.ballL2_ae R)
  filter_upwards [scalar_ae c (StaticBallSymbol.ballL2 R), hb] with x hx hb
  rw [hx]
  change StaticBallSymbol.ballL2 R (x-c) = _
  rw [show StaticBallSymbol.ballL2 R (x-c) =
    (ball (0 : Space) R).indicator (fun _ => (1 : ℂ)) (x-c) by
      simpa only [sub_eq_add_neg] using hb]
  by_cases hm : x ∈ ball c R
  · have h0 : x-c ∈ ball (0 : Space) R := by
      simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hm
    rw [indicator_of_mem h0, indicator_of_mem hm]
  · have h0 : x-c ∉ ball (0 : Space) R := by
      simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hm
    rw [indicator_of_not_mem h0, indicator_of_not_mem hm]

theorem translated_hessian_ae (c : Space) (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    scalar c (StaticBallL2.hessianL2 R hR i j) =ᵐ[volume]
      fun x => StaticBallHessian.hessian R i j (x-c) := by
  have hh := (measurePreserving_add_right (volume : Measure Space) (-c)).quasiMeasurePreserving.ae
    (StaticBallL2.hessianL2_ae R hR i j)
  filter_upwards [scalar_ae c (StaticBallL2.hessianL2 R hR i j), hh] with x hx hh
  exact hx.trans (by simpa only [sub_eq_add_neg] using hh)

theorem translated_weak_derivative (c : Space) (G H : ScalarL2) (i : Fin 3)
    (h : ∀ φ : 𝓢(Space, ℂ), (∫ x, H x * φ x) =
      -(∫ x, G x * GradientProjection.pderivative i φ x))
    (φ : 𝓢(Space, ℂ)) :
    (∫ x, scalar c H x * φ x) =
      -(∫ x, scalar c G x * GradientProjection.pderivative i φ x) := by
  rw [scalar_pairing, scalar_pairing]
  have he := h (NewtonConvolution.translate c φ)
  rw [NewtonConvolution.translate_pderivative] at he
  exact he

theorem translated_hessian_fourier_derivative (c : Space) (R : ℝ) (hR : 0 < R)
    (i j : Fin 3) :
    FourierL2.fourierEquiv (scalar c (StaticBallL2.hessianL2 R hR i j)) =ᵐ[volume] fun ξ =>
      (2 * Real.pi * Complex.I) * (ξ i : ℂ) *
        FourierL2.fourierEquiv (scalar c (StaticBallL2.gradientL2 R hR j)) ξ :=
  StaticBallFourier.weak_derivative_fourier _ _ i
    (translated_weak_derivative c _ _ i (StaticBallSchwartz.weak_hessian_schwartz R hR i j))

theorem translated_fourier_trace_ae (c : Space) (R : ℝ) (hR : 0 < R) :
    (fun ξ => ∑ i : Fin 3,
      FourierL2.fourierEquiv (scalar c (StaticBallL2.hessianL2 R hR i i)) ξ)
      =ᵐ[volume] fun ξ => -FourierL2.fourierEquiv (scalar c (StaticBallSymbol.ballL2 R)) ξ := by
  have he := congrArg (fun F => FourierL2.fourierEquiv (scalar c F))
    (StaticBallSymbol.hessianL2_trace R hR)
  simp only [map_sum, map_neg] at he
  filter_upwards [StaticBallSymbol.three_sum_ae
    (fun i => FourierL2.fourierEquiv (scalar c (StaticBallL2.hessianL2 R hR i i))),
    Lp.coeFn_neg (FourierL2.fourierEquiv (scalar c (StaticBallSymbol.ballL2 R)))] with ξ hs hn
  rw [← hs, he, hn]
  rfl

theorem translated_hessian_fourier_symbol (c : Space) (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    FourierL2.fourierEquiv (scalar c (StaticBallL2.hessianL2 R hR i j)) =ᵐ[volume] fun ξ =>
      NewtonHessian.hessianSymbol ξ i j *
        FourierL2.fourierEquiv (scalar c (StaticBallSymbol.ballL2 R)) ξ := by
  have hd : ∀ᵐ ξ : Space, ∀ i j : Fin 3,
      FourierL2.fourierEquiv (scalar c (StaticBallL2.hessianL2 R hR i j)) ξ =
        (2 * Real.pi * Complex.I) * (ξ i : ℂ) *
          FourierL2.fourierEquiv (scalar c (StaticBallL2.gradientL2 R hR j)) ξ :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr
      (fun j => translated_hessian_fourier_derivative c R hR i j))
  filter_upwards [hd, translated_fourier_trace_ae c R hR,
    show ∀ᵐ ξ : Space, ξ ≠ 0 from ae_iff.mpr (by simp)] with ξ hd ht hn
  apply StaticBallSymbol.symmetric_derivative_symbol ξ hn _ _ _ _ hd _ ht i j
  intro p q
  rw [StaticBallSymbol.hessianL2_symmetric R hR p q]

end OQ14.StaticBallTranslation

#print axioms OQ14.StaticBallTranslation.scalar_ae
#print axioms OQ14.StaticBallTranslation.scalar_pairing
#print axioms OQ14.StaticBallTranslation.translated_ball_ae
#print axioms OQ14.StaticBallTranslation.translated_hessian_ae
#print axioms OQ14.StaticBallTranslation.translated_weak_derivative
#print axioms OQ14.StaticBallTranslation.translated_hessian_fourier_derivative
#print axioms OQ14.StaticBallTranslation.translated_fourier_trace_ae
#print axioms OQ14.StaticBallTranslation.translated_hessian_fourier_symbol
