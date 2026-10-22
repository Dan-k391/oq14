import StaticBallFourier

/-! # Actual Fourier Hessian symbol for a uniform-ball source -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallSymbol

open MeasureTheory Metric Set
open scoped Topology BigOperators

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2

def ballL2 (R : ℝ) : ScalarL2 :=
  indicatorConstLp 2 (measurableSet_ball (x := (0 : Space)) (ε := R))
    measure_ball_lt_top.ne (1 : ℂ)

theorem ballL2_ae (R : ℝ) : ballL2 R =ᵐ[volume]
    (ball (0 : Space) R).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

theorem three_sum_ae (F : Fin 3 → ScalarL2) :
    (fun x => (∑ i, F i : ScalarL2) x) =ᵐ[volume] fun x => ∑ i, F i x := by
  simp only [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (F 0 + F 1) (F 2), Lp.coeFn_add (F 0) (F 1)] with x hx hy
  exact hx.trans (congrArg (fun z => z + F 2 x) hy)

theorem hessian_symmetric (R : ℝ) (i j : Fin 3) (x : Space) :
    StaticBallHessian.hessian R i j x = StaticBallHessian.hessian R j i x := by
  simp only [StaticBallHessian.hessian, StaticBallHessian.exterior, eq_comm, mul_comm]

theorem hessianL2_symmetric (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    StaticBallL2.hessianL2 R hR i j = StaticBallL2.hessianL2 R hR j i := by
  apply Lp.ext
  filter_upwards [StaticBallL2.hessianL2_ae R hR i j,
    StaticBallL2.hessianL2_ae R hR j i] with x hx hy
  rw [hx, hy, hessian_symmetric]

theorem hessianL2_trace (R : ℝ) (hR : 0 < R) :
    (∑ i : Fin 3, StaticBallL2.hessianL2 R hR i i) = -ballL2 R := by
  apply Lp.ext
  have hh : ∀ᵐ x : Space, ∀ i : Fin 3,
      StaticBallL2.hessianL2 R hR i i x = StaticBallHessian.hessian R i i x :=
    ae_all_iff.mpr (fun i => StaticBallL2.hessianL2_ae R hR i i)
  filter_upwards [three_sum_ae (fun i => StaticBallL2.hessianL2 R hR i i),
    hh, StaticBallHessian.trace_ae R, Lp.coeFn_neg (ballL2 R), ballL2_ae R]
    with x hx hh ht hn hb
  rw [hx, hn, Pi.neg_apply, hb]
  simpa only [hh] using ht

theorem fourier_trace_ae (R : ℝ) (hR : 0 < R) :
    (fun ξ => ∑ i : Fin 3, FourierL2.fourierEquiv (StaticBallL2.hessianL2 R hR i i) ξ)
      =ᵐ[volume] fun ξ => -FourierL2.fourierEquiv (ballL2 R) ξ := by
  have he := congrArg FourierL2.fourierEquiv (hessianL2_trace R hR)
  simp only [map_sum, map_neg] at he
  filter_upwards [three_sum_ae
    (fun i => FourierL2.fourierEquiv (StaticBallL2.hessianL2 R hR i i)),
    Lp.coeFn_neg (FourierL2.fourierEquiv (ballL2 R))] with ξ hs hn
  rw [← hs, he, hn]
  rfl

theorem symmetric_derivative_symbol (ξ : Space) (hξ : ξ ≠ 0)
    (H : Fin 3 → Fin 3 → ℂ) (G : Fin 3 → ℂ) (c b : ℂ)
    (hd : ∀ i j, H i j = c * (ξ i : ℂ) * G j)
    (hs : ∀ i j, H i j = H j i) (ht : ∑ k, H k k = -b) (i j : Fin 3) :
    H i j = NewtonHessian.hessianSymbol ξ i j * b := by
  have hr : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
  have hc : ∀ k : Fin 3, (ξ k : ℂ)^2 * H i j = (ξ i : ℂ)*(ξ j : ℂ)*H k k := by
    intro k
    calc
      _ = (ξ i : ℂ)*(ξ k : ℂ)*H k j := by rw [hd i j, hd k j]; ring
      _ = (ξ i : ℂ)*(ξ k : ℂ)*H j k := by rw [hs k j]
      _ = _ := by rw [hd j k, hd k k]; ring
  have he : (‖ξ‖ : ℂ)^2 * H i j = (ξ i : ℂ)*(ξ j : ℂ)*(-b) := by
    calc
      _ = (∑ k : Fin 3, (ξ k : ℂ)^2) * H i j := by
        rw [StaticBallHessian.coordinate_square_sum]
      _ = ∑ k : Fin 3, (ξ k : ℂ)^2 * H i j := Finset.sum_mul ..
      _ = ∑ k : Fin 3, (ξ i : ℂ)*(ξ j : ℂ)*H k k := Finset.sum_congr rfl (fun k _ => hc k)
      _ = (ξ i : ℂ)*(ξ j : ℂ)*(∑ k : Fin 3, H k k) := (Finset.mul_sum ..).symm
      _ = _ := by rw [ht]
  unfold NewtonHessian.hessianSymbol
  field_simp [hr]
  linear_combination he

theorem hessian_fourier_symbol (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    FourierL2.fourierEquiv (StaticBallL2.hessianL2 R hR i j) =ᵐ[volume] fun ξ =>
      NewtonHessian.hessianSymbol ξ i j * FourierL2.fourierEquiv (ballL2 R) ξ := by
  have hd : ∀ᵐ ξ : Space, ∀ i j : Fin 3,
      FourierL2.fourierEquiv (StaticBallL2.hessianL2 R hR i j) ξ =
        (2 * Real.pi * Complex.I) * (ξ i : ℂ) *
          FourierL2.fourierEquiv (StaticBallL2.gradientL2 R hR j) ξ :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr
      (fun j => StaticBallFourier.hessian_fourier_derivative R hR i j))
  filter_upwards [hd, fourier_trace_ae R hR,
    show ∀ᵐ ξ : Space, ξ ≠ 0 from ae_iff.mpr (by simp)] with ξ hd ht hn
  apply symmetric_derivative_symbol ξ hn _ _ _ _ hd _ ht i j
  intro p q
  rw [hessianL2_symmetric R hR p q]

end OQ14.StaticBallSymbol

#print axioms OQ14.StaticBallSymbol.ballL2_ae
#print axioms OQ14.StaticBallSymbol.three_sum_ae
#print axioms OQ14.StaticBallSymbol.hessian_symmetric
#print axioms OQ14.StaticBallSymbol.hessianL2_symmetric
#print axioms OQ14.StaticBallSymbol.hessianL2_trace
#print axioms OQ14.StaticBallSymbol.fourier_trace_ae
#print axioms OQ14.StaticBallSymbol.symmetric_derivative_symbol
#print axioms OQ14.StaticBallSymbol.hessian_fourier_symbol
